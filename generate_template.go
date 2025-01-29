package main

import (
	"encoding/json"
	"go/ast"
	"go/parser"
	"go/token"
	"log"
	"strings"

	"github.com/iancoleman/strcase"
	"github.com/pocketbase/pocketbase/core"
)

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
	parsed, err := parser.ParseExpr(fieldName)
	ident, ok := parsed.(*ast.Ident)
	// This check fails when the field name is a reserved go keyword
	if err != nil || !ok {
		fieldName += "_"
		parsed, err = parser.ParseExpr(fieldName)
		ident, ok = parsed.(*ast.Ident)
	}
	if err != nil || !ok {
		log.Fatalf("Error: Could not parse collection field name `%v`", field.GetName())
	}

	f := &ast.Field{
		Doc: createSelectTypeComment(field),
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

func createSelectTypeComment(field core.Field) *ast.CommentGroup {
	selectField, ok := field.(*core.SelectField)
	if !ok {
		return nil
	}
	selectTypeName := strcase.ToCamel(selectField.Name) + "SelectType"
	selectOptions := selectField.Values

	var sb strings.Builder

	sb.WriteString(selectTypeComment + " ")
	sb.WriteString(selectTypeName)
	sb.WriteString("(")
	for i, o := range selectOptions {
		sb.WriteString(o)
		if i < len(selectOptions)-1 {
			sb.WriteString(", ")
		}
	}
	sb.WriteString(")")

	comment := &ast.CommentGroup{
		List: []*ast.Comment{{
			Text: sb.String(),
		}},
	}
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
			{Text: "// It is not meant to be compiled it is only meant for human interaction."},
			{Text: "// You can make the following changes to influence the final code generation step:"},
			{Text: "//"},
			{Text: "//  - Edit the struct names. The names are directly copied to the proxy struct definitions."},
			{Text: "//  - Remove structs or fields that you don't want in the generated code. Note that upon removing a struct"},
			{Text: "//    you also have to remove any fields that have that struct as their type."},
			{Text: "//  - Edit the type name in the '// select:' comments. Do not edit the contents of the round brackets."},
			{Text: "//  - Change the const names of the select options by adding a pair of [] to the // select: comment."},
			{Text: "//    Example: // select:(optionA, optionB)[OpA, OpB] these will be the names of the constants that"},
			{Text: "//    represent the select options (like an enum)."},
			{Text: "//  - Edit the field names. If you do, the generator still needs to know the original database field name."},
			{Text: "//    To provide this, add a '// schema-name: [original field name]' comment directly above the field."},
			{Text: "//"},
			{Text: "// If you edit this file, be careful and back it up to prevent the changes from being overridden by"},
			{Text: "// subsequent runs of the generator."},
		},
	}
}

func parseSchemaJson(rawJson []byte, includeSystem bool) []*core.Collection {
	data := []map[string]any{}
	json.Unmarshal(rawJson, &data)

	collections := make([]*core.Collection, 0, len(data))
	for _, cData := range data {
		rawData, err := json.Marshal(cData)
		if err != nil {
			log.Fatalf("Error while parsing pocketbase schema json: %v", err)
		}
		collection := &core.Collection{}
		json.Unmarshal(rawData, collection)
		if !collection.System || includeSystem {
			collections = append(collections, collection)
		}
	}

	return collections
}
