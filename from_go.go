package main

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/scanner"
	"go/token"
	"log"
	"strings"

	"golang.org/x/tools/go/ast/astutil"
)

// Parses a go file and creates a proxy for every
// struct that is found in it.
// Each proxy has a getter/setter for each field
// in the original struct.
// Fields with an unknown type are ignored with
// a warning.
func proxiesFromGoFile(filename string) []ast.Decl {
	p := newParser(filename)
	structs := p.structSpecs

	decls := make([]ast.Decl, 0, 25)
	for _, s := range structs {
		fields := p.extractStructFields(s)

		decls = append(decls, createSelectTypes(fields)...)
		decls = append(decls, newProxyDecl(s.Name.Name))

		getters := createFuncs(fields, newGetterDecl)
		setters := createFuncs(fields, newSetterDecl)
		for i, getter := range getters {
			if getter == nil {
				continue
			}
			decls = append(decls, getter, setters[i])
		}
	}

	return decls
}

type Parser struct {
	Filename string

	Fset *token.FileSet
	fAst *ast.File

	structSpecs []*ast.TypeSpec
	structNames map[string]*ast.TypeSpec
}

func newParser(filename string) *Parser {
	parser := &Parser{Filename: filename}
	parser.parseFile()
	parser.collectStructSpecs()
	return parser
}

func (p *Parser) parseFile() {
	p.Fset = token.NewFileSet()

	opts := parser.SkipObjectResolution |
		parser.ParseComments
	f, err := parser.ParseFile(p.Fset, p.Filename, nil, opts)
	if err != nil {
		log.Fatal(err)
	}

	p.fAst = f
}

func (p *Parser) collectStructSpecs() {
	specs := make([]*ast.TypeSpec, 0, 16)
	names := make(map[string]*ast.TypeSpec)

	ast.Inspect(p.fAst, func(n ast.Node) bool {
		structSpec := structSpec(n)
		if structSpec != nil {
			specs = append(specs, structSpec)
			names[structSpec.Name.Name] = structSpec
			return false
		}
		return true
	})

	p.structSpecs = specs
	p.structNames = names
}

func (p *Parser) extractStructFields(structSpec *ast.TypeSpec) []*Field {
	structName := structSpec.Name.Name
	astFields := structSpec.Type.(*ast.StructType).Fields.List
	fields := make([]*Field, 0, len(astFields))

	for _, f := range astFields {
		fields = append(fields, p.newFieldsFromAST(structName, f)...)
	}

	return fields
}

func (p *Parser) newFieldsFromAST(structName string, field *ast.Field) []*Field {
	fieldType := field.Type

	selectTypeName, selectOptions := p.parseSelectTypeComment(field)
	schemaName := p.parseAlternativeSchemaName(field)
	if schemaName == "" {
		schemaName = field.Names[0].Name
	}

	fields := make([]*Field, len(field.Names))
	for i, n := range field.Names {
		fieldName := n.Name
		field := newField(
			structName,
			fieldName,
			schemaName,
			fieldType,
			selectTypeName,
			selectOptions,
			p.structNames,
			field,
			p,
		)
		fields[i] = field
	}

	return fields
}

func (p *Parser) parseSelectTypeComment(field *ast.Field) (string, []string) {
	if field.Doc == nil || len(field.Doc.List) == 0 {
		return "", nil
	}

	comment := ""
	for _, c := range field.Doc.List {
		if c.Text[:9] == "//select:" {
			comment = c.Text
			break
		}
	}
	if comment == "" {
		return "", nil
	}

	if nodeString(baseType(field.Type)) != "int" {
		pos := p.Fset.Position(field.Pos())
		p.logError("Cannot have //select: comment on field of type other than int or []int", pos, -1, nil)
	}

	comment = strings.TrimSpace(comment[9:])
	parsed, err := parser.ParseExpr(comment)
	if err != nil {
		parserErr := err.(scanner.ErrorList)[0]
		pos := p.Fset.Position(field.Pos())
		p.logError(parserErr.Msg, pos, -1, parserErr)
	}

	typeName := ""
	selectOptions := make([]string, 0, 8)

	identFinder := func(c *astutil.Cursor) bool {
		ident, ok := c.Node().(*ast.Ident)
		if !ok {
			return true
		}
		switch c.Name() {
		case "Fun":
			typeName = ident.Name
		case "Args":
			selectOptions = append(selectOptions, ident.Name)
		}
		return true
	}
	astutil.Apply(parsed, identFinder, nil)

	if len(field.Names) > 1 {
		pos := p.Fset.Position(field.Pos())
		errMsg := fmt.Sprintf("The //select: comment can only be used on fields with one identifier. Found %v.", len(field.Names))
		p.logError(errMsg, pos, -1, nil)
	}

	if typeName == "" || len(selectOptions) == 0 {
		pos := p.Fset.Position(field.Pos())
		p.logError("Malformed //select: comment. Example usage: //select: TypeName(option1, option2)", pos, -1, nil)
	}

	return typeName, selectOptions
}

func (p *Parser) parseAlternativeSchemaName(field *ast.Field) string {
	if field.Doc == nil || len(field.Doc.List) == 0 {
		return p.trailingUnderscoreName(field)
	}

	comment := ""
	for _, c := range field.Doc.List {
		if c.Text[:14] == "//schema-name:" {
			comment = c.Text
			break
		}
	}
	if comment == "" {
		return p.trailingUnderscoreName(field)
	}

	if len(field.Names) > 1 {
		pos := p.Fset.Position(field.Pos())
		errMsg := fmt.Sprintf("The //schema-name: comment can only be used on fields with one identifier. Found %v.", len(field.Names))
		p.logError(errMsg, pos, 0, nil)
	}

	schemaname := strings.TrimSpace(comment[14:])
	return schemaname
}

// A trailing underscore signals an identifier that could otherwise
// not be used because it is a reserved go keyword like "type" or "func".
// This function returns the identifier name without the trailing underscore.
// If no trailing underscore is present, an empty string is returned.
func (p *Parser) trailingUnderscoreName(field *ast.Field) string {
	tuName := ""
	for _, n := range field.Names {
		name := n.Name

		if len(name) > 1 && name[len(name)-1] == '_' {
			tuName = name[:len(name)-1]
		}
	}
	if tuName != "" && len(field.Names) > 1 {
		pos := p.Fset.Position(field.Pos())
		errMsg := fmt.Sprintf("Trailing underscore identifiers can only be used on fields with one identifier. Found %v.", len(field.Names))
		p.logError(errMsg, pos, 0, nil)
	}
	return tuName
}

func (p *Parser) logError(msg string, pos token.Position, lineOffset int, origErr *scanner.Error) {
	if origErr != nil {
		pos.Column = origErr.Pos.Column
	}
	pos.Line += lineOffset
	log.Fatalf("Error: %v: %v", pos, msg)

}
func (p *Parser) logWarning(msg string, pos token.Position, lineOffset int, origErr *scanner.Error) {
	if origErr != nil {
		pos.Column = origErr.Pos.Column
	}
	pos.Line += lineOffset
	log.Printf("Warning: %v: %v", pos, msg)
}

func createFuncs(fields []*Field, declare func(f *Field) *ast.FuncDecl) []*ast.FuncDecl {
	decls := make([]*ast.FuncDecl, 0, len(fields))
	for _, f := range fields {
		decl := declare(f)
		decls = append(decls, decl)
	}

	return decls
}

func createSelectTypes(fields []*Field) []ast.Decl {
	decls := make([]ast.Decl, 0, 10)
	for _, f := range fields {
		if f.selectTypeName == "" {
			continue
		}
		decls = append(
			decls,
			newSelectTypeDecl(f.selectTypeName),
			newSelectConstDecl(f),
			newSelectMapDecl(f, true),
			newSelectMapDecl(f, false),
		)
	}

	return decls
}

// Returns a *ast.TypeSpec if it specifies a struct.
// Otherwise nil
func structSpec(n ast.Node) *ast.TypeSpec {
	structSpec, ok := n.(*ast.TypeSpec)
	if !ok {
		return nil
	}
	_, ok = structSpec.Type.(*ast.StructType)
	if !ok {
		return nil
	}
	return structSpec
}
