package generator

import (
	"go/ast"
	"go/parser"
	"go/token"
	"log"
	"strings"

	"github.com/iancoleman/strcase"
	"github.com/pocketbase/pocketbase/core"
	"github.com/snonky/astpos/astpos"
)

// Generates the template and returns the source code bytes
func Template(collections []*core.Collection, savePath, packageName string) []byte {
	if !validatePackageName(packageName) {
		log.Fatalf("The package name %v is not valid.", packageName)
	}

	translator := newSchemaTranslator(collections)
	decls := translator.translate()
	f := wrapTemplateDeclarations(decls, packageName)

	f, fset := astpos.RewritePositions(f)
	sourceCode := printAST(f, fset, savePath)

	return sourceCode
}

type SchemaTranslator struct {
	collections   []*core.Collection
	collectionIds map[string]*core.Collection
}

func newSchemaTranslator(collections []*core.Collection) *SchemaTranslator {
	t := &SchemaTranslator{
		collections:   collections,
		collectionIds: make(map[string]*core.Collection, len(collections)),
	}
	t.collectionIds = make(map[string]*core.Collection, len(t.collections))
	for _, c := range t.collections {
		t.collectionIds[c.Id] = c
	}
	return t
}

// Translates the collections into one struct declaration each
func (t *SchemaTranslator) translate() []ast.Decl {
	decls := make([]ast.Decl, 0, 2*len(t.collections))
	for _, collection := range t.collections {
		decl := &ast.GenDecl{
			Tok:   token.TYPE,
			Specs: []ast.Spec{t.collectionToStruct(collection)},
		}
		decls = append(decls, decl)

	}

	return decls
}

func (t *SchemaTranslator) collectionToStruct(collection *core.Collection) *ast.TypeSpec {
	structType := &ast.StructType{
		Fields: t.translateFields(collection),
	}
	spec := &ast.TypeSpec{
		Name: ast.NewIdent(strcase.ToCamel(collection.Name)),
		Type: structType,
	}
	return spec
}

func (t *SchemaTranslator) translateFields(collection *core.Collection) *ast.FieldList {
	fields := make([]*ast.Field, len(collection.Fields))
	for i, f := range collection.Fields {
		fields[i] = t.translateField(f)
	}
	fieldList := &ast.FieldList{
		List:    fields,
		Opening: 1,
		Closing: 1,
	}
	return fieldList
}

func (t *SchemaTranslator) translateField(field core.Field) *ast.Field {
	fieldName := field.GetName()

	if fieldName == "id" {
		// Since the id is the only public field
		// of the core.Record struct it will
		// be accessed by the proxy in this way too
		fieldName = "Id"
	}

	ident := toIdentifier(fieldName)
	f := &ast.Field{
		Doc: createFieldDoc(field),
		Names: []*ast.Ident{
			ident,
		},
		Type: t.goType(field),
	}

	return f
}

func (t *SchemaTranslator) goType(field core.Field) ast.Expr {
	typeName := ""
	switch f := field.(type) {
	case *core.BoolField:
		typeName = "bool"
	case *core.NumberField:
		if f.OnlyInt {
			typeName = "int"
		} else {
			typeName = "float64"
		}
	case *core.TextField:
		typeName = "string"
	case *core.EmailField:
		typeName = "string"
	case *core.URLField:
		typeName = "string"
	case *core.EditorField:
		typeName = "string"
	case *core.DateField:
		typeName = "types.DateTime"
	case *core.AutodateField:
		typeName = "types.DateTime"
	case *core.SelectField:
		typeName = "int"
	case *core.FileField:
		typeName = "string"
	case *core.RelationField:
		relatedCollection := t.collectionIds[f.CollectionId]
		typeName = "*" + strcase.ToCamel(relatedCollection.Name)
	case *core.JSONField:
		typeName = "types.JSONRaw"
	case *core.PasswordField:
		typeName = "string"
	}

	multi, ok := field.(core.MultiValuer)
	if ok && multi.IsMultiple() {
		typeName = "[]" + typeName
	}

	fieldType, _ := parser.ParseExpr(typeName)
	return fieldType
}

func createFieldDoc(field core.Field) *ast.CommentGroup {
	comments := make([]*ast.Comment, 0, 1)
	if selectComment := createSelectTypeComment(field); selectComment != nil {
		comments = append(comments, selectComment)
	}
	if systemComment := createSystemFieldComment(field); systemComment != nil {
		comments = append(comments, systemComment)
	}
	doc := &ast.CommentGroup{List: comments}
	return doc
}

func createSelectTypeComment(field core.Field) *ast.Comment {
	selectField, ok := field.(*core.SelectField)
	if !ok {
		return nil
	}
	selectTypeName := strcase.ToCamel(selectField.Name) + "SelectType"
	selectOptions := selectField.Values

	var sb strings.Builder

	sb.WriteString(selectTypeComment)
	sb.WriteString(" ")
	sb.WriteString(selectTypeName)
	sb.WriteString("(")
	for i, o := range selectOptions {
		o = validateIdentifier(o)
		sb.WriteString(o)
		if i < len(selectOptions)-1 {
			sb.WriteString(", ")
		}
	}
	sb.WriteString(")")

	comment := &ast.Comment{Text: sb.String()}
	return comment
}

func createSystemFieldComment(field core.Field) *ast.Comment {
	if !field.GetSystem() {
		return nil
	}
	comment := &ast.Comment{Text: systemFieldComment + " " + field.GetName()}
	return comment
}

func wrapTemplateDeclarations(decls []ast.Decl, packageName string) *ast.File {
	f := &ast.File{
		Doc:   newInfoComment(),
		Name:  ast.NewIdent(packageName),
		Decls: decls,
	}

	return f
}

func newInfoComment() *ast.CommentGroup {
	return &ast.CommentGroup{
		List: []*ast.Comment{
			{Text: "// Autogenerated by github.com/snonky/pocketbase-gogen."},
			{Text: "// Please feel free to edit after noting the explanation:"},
			{Text: "//"},
			{Text: "// This file is an intermediate product of the proxy generation."},
			{Text: "// It is called a 'schema as code' or just 'template'. It is not meant to be"},
			{Text: "// compiled it is only meant for human interaction, place it in a separate package"},
			{Text: "// but never import it."},
			{Text: "// Here's what you can do to influence the final code generation step:"},
			{Text: "//"},
			{Text: "// Do:"},
			{Text: "//  - Edit the struct names. The names are directly copied to the proxy struct definitions."},
			{Text: "//  - Remove structs or fields that you don't want in the generated code. Note that upon removing a struct"},
			{Text: "//    you also have to remove any fields that have that struct as their type."},
			{Text: "//  - Edit the type name in the '// select:' comments."},
			{Text: "//  - Change the const names of the select options by adding a pair of [] to the // select: comment."},
			{Text: "//    Example: // select: MySelectType(optionA, optionB)[OpA, OpB] <-- These constants will represent"},
			{Text: "//    the select options (like an enum). If you omit the [] the option names are used directly."},
			{Text: "//  - Edit the field names. If you do, the generator still needs to know the original database field name."},
			{Text: "//    To provide this, add a '// schema-name: [original field name]' comment directly above the field."},
			{Text: "//  - Add methods to the template structs. The generator will replace any fields you access with the also"},
			{Text: "//    generated getters/setters. Be aware of that when repeatedly assigning a template field. You are"},
			{Text: "//    calling a setter on every assignment. The methods can also call each other."},
			{Text: "//"},
			{Text: "// Do not:"},
			{Text: "//  - Add structs that do not represent a PB collection."},
			{Text: "//  - Add fields that are not part of the PB schema to the structs."},
			{Text: "//  - Change the select values in the () of the '// select:' comments'"},
			{Text: "//  - Remove the '// system:' doc comments from the system fields. Generation will fail if you do so."},
			{Text: "//  - Shadow any names from the core.Record struct. Generation will also fail for safety."},
			{Text: "//  - Rename fields without preserving the original name with a '// schema-name:' comment.'"},
			{Text: "//"},
			{Text: "// If you edit this file, be careful and back it up to prevent the changes from being overridden by"},
			{Text: "// subsequent runs of the template command. Check out the PocketBase docs to find out how to use the"},
			{Text: "// generated code in your code: https://pocketbase.io/docs/go-record-proxy/"},
		},
	}
}
