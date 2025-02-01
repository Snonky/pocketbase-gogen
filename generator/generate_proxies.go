package generator

import (
	"fmt"
	"go/ast"
	"go/parser"
	"go/scanner"
	"go/token"
	"go/types"
	"log"
	"slices"
	"strings"

	"github.com/iancoleman/strcase"
	"github.com/snonky/astpos/astpos"
	"golang.org/x/tools/go/ast/astutil"
)

func Generate(template []byte, savePath, packageName string) []byte {
	if !validatePackageName(packageName) {
		log.Fatalf("The package name %v is not valid.", packageName)
	}

	loadTemplateASTs()
	loadPBInfo()

	decls := proxiesFromGoTemplate(template)
	f := wrapProxyDeclarations(decls, packageName)

	f, fset := astpos.RewritePositions(f)
	sourceCode := printAST(f, fset, savePath)

	checkPbShadows(sourceCode)

	return sourceCode
}

func checkPbShadows(sourceCode []byte) {
	fset := token.NewFileSet()
	f, err := parser.ParseFile(fset, "shadowcheck.go", sourceCode, parser.SkipObjectResolution)
	if err != nil {
		log.Fatal(err)
	}

	conf := types.Config{Importer: &Importer{}}
	pkg, err := conf.Check("x", fset, []*ast.File{f}, nil)
	if pkg == nil {
		// Do not check error here because type errors can happen
		// with only a single file being checked w/o dependencies.
		// We only want the scope names for the shadow check.
		log.Fatal(err)
	}

	scope := pkg.Scope()
	names := scope.Names()
	allShadows := make([]string, 0)
	for _, name := range names {
		obj := scope.Lookup(name)
		proxyType, ok := obj.Type().(*types.Named)
		if !ok {
			continue
		}
		_, ok = proxyType.Underlying().(*types.Struct)
		if !ok {
			continue
		}
		_, shadows := pbInfo.shadowsRecord(proxyType)
		allShadows = append(allShadows, shadows...)
	}

	if len(allShadows) > 0 {
		log.Fatalf(`Can not generate proxy code because some of the generated names shadow names from PocketBase's core.Record struct. This prevents the internals of PocketBase to safely handle data.
Try renaming fields/methods in the template to escape the shadowing. Don't forget to use the '// schema-name:' comment when renaming fields.
The shadowed names are: %v`, allShadows)
	}

}

func wrapProxyDeclarations(decls []ast.Decl, packageName string) *ast.File {
	infoComment := &ast.CommentGroup{
		List: []*ast.Comment{
			{Text: "// Autogenerated by github.com/snonky/pocketbase-gogen. Do not edit."},
		},
	}

	f := &ast.File{
		Doc:   infoComment,
		Name:  ast.NewIdent(packageName),
		Decls: decls,
	}
	return f
}

// Parses a go template file and creates a proxy for every
// struct that is found in it.
// Each proxy has a getter/setter for each field
// in the template struct.
// Fields with an unknown type are ignored with
// a warning.
func proxiesFromGoTemplate(sourceCode []byte) []ast.Decl {
	p := newParser(sourceCode)

	proxyMethods := createProxyMethods(p)

	decls := make([]ast.Decl, 0, 25)
	for _, s := range p.structSpecs {
		structName := s.Name.Name
		fields := p.structFields[structName]

		decls = append(decls, createSelectTypes(fields)...)
		decls = append(decls, newProxyDecl(structName, s.Doc))

		methods := proxyMethods[structName]
		decls = append(decls, methods...)

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
	sourceCode []byte

	Fset *token.FileSet
	fAst *ast.File

	structSpecs   []*ast.TypeSpec
	structNames   map[string]*ast.TypeSpec
	structFields  map[string][]*Field
	structMethods map[string][]*ast.FuncDecl

	// Tracks the declarations of select-typing related
	// names to prevent duplication
	selectTypeDups       map[string]any
	selectVarDups        map[string]any
	selectTypeToOptions  map[string][]string
	selectTypeToVarNames map[string][]string
	varToSelectType      map[string]string
}

func newParser(sourceCode []byte) *Parser {
	parser := &Parser{
		sourceCode:           sourceCode,
		selectTypeDups:       map[string]any{},
		selectVarDups:        map[string]any{},
		selectTypeToOptions:  map[string][]string{},
		selectTypeToVarNames: map[string][]string{},
		varToSelectType:      map[string]string{},
	}
	parser.parseFile()
	parser.collectStructSpecs()
	parser.collectStructFields()
	parser.collectStructMethods()
	return parser
}

func (p *Parser) parseFile() {
	p.Fset = token.NewFileSet()

	opts := parser.SkipObjectResolution |
		parser.ParseComments
	f, err := parser.ParseFile(p.Fset, "x.go", p.sourceCode, opts)
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

func (p *Parser) collectStructFields() {
	p.structFields = make(map[string][]*Field)

	for _, s := range p.structSpecs {
		structName := s.Name.Name
		astFields := s.Type.(*ast.StructType).Fields.List
		fields := make([]*Field, 0, len(astFields))

		for _, f := range astFields {
			fields = append(fields, p.newFieldsFromAST(structName, f)...)
		}

		p.structFields[structName] = fields
	}
}

func (p *Parser) collectStructMethods() {
	funcs := make(map[string][]*ast.FuncDecl)

	for _, decl := range p.fAst.Decls {
		funcDecl, ok := decl.(*ast.FuncDecl)
		if !ok {
			continue
		}
		recv := funcDecl.Recv
		if recv == nil {
			continue
		}

		recvType := baseType(recv.List[0].Type)
		recvName := nodeString(recvType)

		_, ok = funcs[recvName]
		if !ok {
			funcs[recvName] = make([]*ast.FuncDecl, 0)
		}
		funcs[recvName] = append(funcs[recvName], funcDecl)
	}

	p.structMethods = funcs
}

func (p *Parser) newFieldsFromAST(structName string, field *ast.Field) []*Field {
	selectTypeName, selectOptions, selectVarNames := p.parseSelectTypeComment(field)
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
			field.Type,
			selectTypeName,
			selectOptions,
			selectVarNames,
			p.structNames,
			field,
			p,
		)
		fields[i] = field
	}

	return fields
}

var selectTypeComment = "// select:"

func (p *Parser) parseSelectTypeComment(field *ast.Field) (string, []string, []string) {
	if field.Doc == nil || len(field.Doc.List) == 0 {
		return "", nil, nil
	}

	comment := ""
	var astComment *ast.Comment
	for _, c := range field.Doc.List {
		if c.Text[:len(selectTypeComment)] == selectTypeComment {
			comment = c.Text
			astComment = c
			break
		}
	}
	if comment == "" {
		return "", nil, nil
	}

	if nodeString(baseType(field.Type)) != "int" {
		pos := p.Fset.Position(astComment.Slash)
		p.logError("Cannot have // select: comment on field of type other than int or []int", pos, nil)
	}

	if len(field.Names) > 1 {
		pos := p.Fset.Position(astComment.Slash)
		errMsg := fmt.Sprintf("The // select: comment can only be used on fields with one identifier. Found %v.", len(field.Names))
		p.logError(errMsg, pos, nil)
	}

	comment = strings.TrimSpace(comment[len(selectTypeComment):])

	typeName, selectOptions, selectVarNames := p.parseSelectType(astComment.Slash, comment)
	typeName, selectOptions, selectVarNames = p.validateSelectType(astComment.Slash, typeName, selectOptions, selectVarNames)

	return typeName, selectOptions, selectVarNames
}

// Parses a string of the form 'TypeName(option1, option2, ...)' or
// 'TypeName(option1, option2, ...)[VarName1, VarName2, ...]
// Returns the [TypeName], the [option1, option1, ...] list and the [VarName1, VarName2, ...] list.
// If the var name list is omitted the option names are reused as the var names.
func (p *Parser) parseSelectType(commentPos token.Pos, typeStr string) (string, []string, []string) {
	parsed, err := parser.ParseExpr(typeStr)
	if err != nil {
		parserErr := err.(scanner.ErrorList)[0]
		pos := p.Fset.Position(commentPos)
		p.logError(parserErr.Msg, pos, parserErr)
	}

	withVarNames := p.checkBrackets(commentPos, parsed)

	typeName := ""
	selectOptions := make([]string, 0, 8)
	selectVarNames := make([]string, 0, 8)
	identFinder := func(c *astutil.Cursor) bool {
		ident, ok := c.Node().(*ast.Ident)
		if !ok {
			return true
		}
		switch c.Name() {
		case "Fun":
			typeName = ident.Name
		case "Args":
			selectOption, _ := trimUnderscore(ident.Name)
			selectOptions = append(selectOptions, selectOption)
			if !withVarNames {
				varName := strcase.ToCamel(ident.Name)
				selectVarNames = append(selectVarNames, varName)
			}
		case "Index":
			fallthrough
		case "Indices":
			varName := strcase.ToCamel(ident.Name)
			selectVarNames = append(selectVarNames, varName)
		}
		return true
	}
	astutil.Apply(parsed, identFinder, nil)

	if typeName == "" || len(selectOptions) == 0 {
		pos := p.Fset.Position(commentPos)
		p.logError("Malformed // select: comment. Example usage: // select: TypeName(option1, option2)[VarName1, VarName2]", pos, nil)
	}

	if len(selectOptions) != len(selectVarNames) {
		pos := p.Fset.Position(commentPos)
		errMsg := fmt.Sprintf(
			"Unequal number of select options and variable names in // select: comment. Found %v options and %v names",
			len(selectOptions),
			len(selectVarNames),
		)
		p.logError(errMsg, pos, nil)
	}

	return typeName, selectOptions, selectVarNames
}

// Checks if the // select: comment only has () or also includes []
// Errors if neither are found. Returns true when the [] are present.
func (p *Parser) checkBrackets(commentPos token.Pos, parsedComment ast.Node) bool {
	var indexExpr ast.Expr
	var callExpr ast.Expr

	switch n := parsedComment.(type) {
	case *ast.IndexExpr:
		indexExpr = n
		callExpr = n.X
	case *ast.IndexListExpr:
		indexExpr = n
		callExpr = n.X
	case *ast.CallExpr:
		callExpr = n
	}

	withVarNames := indexExpr != nil
	withOpts := callExpr != nil
	if !withVarNames && !withOpts {
		pos := p.Fset.Position(commentPos)
		p.logError("Malformed // select: comment. Example usage: // select: TypeName(option1, option2)[VarName1, VarName2]", pos, nil)
	}

	return withVarNames
}

func (p *Parser) validateSelectType(commentPos token.Pos, typeName string, selectOptions, selectVarNames []string) (string, []string, []string) {
	origName := typeName
	_, isDuplicate := p.selectTypeDups[typeName]

	if isDuplicate {
		otherOpts := p.selectTypeToOptions[typeName]
		otherVars := p.selectTypeToVarNames[typeName]
		if slices.Equal(selectOptions, otherOpts) && slices.Equal(selectVarNames, otherVars) {
			// Another field already defined the same select type. Reuse.
			return typeName, []string{}, []string{}
		} else {
			// Another field has a duplicate name but different select options. Rename this one.
			typeName = rename(typeName, p.selectTypeDups)

			pos := p.Fset.Position(commentPos)
			warnMsg := fmt.Sprintf("Found a duplicate select type name: %v. Renaming to %v", origName, typeName)
			p.logWarning(warnMsg, pos, nil)
		}
	}

	p.selectTypeDups[typeName] = struct{}{}
	p.selectTypeToOptions[typeName] = selectOptions
	p.selectTypeToVarNames[typeName] = selectVarNames

	selectVarNames = p.checkSelectVarNameDuplicates(commentPos, typeName, selectVarNames)

	return typeName, selectOptions, selectVarNames
}

func (p *Parser) checkSelectVarNameDuplicates(commentPos token.Pos, typeName string, selectVarNames []string) []string {
	checkedNames := make([]string, len(selectVarNames))

	for i, name := range selectVarNames {
		origName := name
		_, isDuplicate := p.selectVarDups[name]

		if isDuplicate {
			name = rename(name, p.selectVarDups)

			origOwner := p.varToSelectType[origName]
			pos := p.Fset.Position(commentPos)
			warnMsg := fmt.Sprintf(
				"Found a duplicate select variable name. %v is already in %v. Renaming to %v.",
				origName, origOwner, name,
			)
			p.logWarning(warnMsg, pos, nil)
		}

		p.selectVarDups[name] = struct{}{}
		p.varToSelectType[name] = typeName

		checkedNames[i] = name
	}

	return checkedNames
}

var schemaNameComment = "// schema-name:"

func (p *Parser) parseAlternativeSchemaName(field *ast.Field) string {
	if field.Doc == nil || len(field.Doc.List) == 0 {
		return p.trailingUnderscoreName(field)
	}

	comment := ""
	var astComment *ast.Comment
	for _, c := range field.Doc.List {
		if c.Text[:len(schemaNameComment)] == schemaNameComment {
			comment = c.Text
			astComment = c
			break
		}
	}
	if comment == "" {
		return p.trailingUnderscoreName(field)
	}

	if len(field.Names) > 1 {
		pos := p.Fset.Position(astComment.Slash)
		errMsg := fmt.Sprintf("The // schema-name: comment can only be used on fields with one identifier. Found %v.", len(field.Names))
		p.logError(errMsg, pos, nil)
	}

	schemaname := strings.TrimSpace(comment[len(schemaNameComment):])
	return schemaname
}

// A trailing underscore signals an identifier that could otherwise
// not be used because it is a reserved go keyword like "type" or "func".
// This function returns the identifier name without the trailing underscore.
// If no trailing underscore is present, an empty string is returned.
func (p *Parser) trailingUnderscoreName(field *ast.Field) string {
	tuName := ""
	for _, n := range field.Names {
		trimmed, ok := trimUnderscore(n.Name)
		if ok {
			tuName = trimmed
			break
		}
	}
	if tuName != "" && len(field.Names) > 1 {
		pos := p.Fset.Position(field.Pos())
		errMsg := fmt.Sprintf("Trailing underscore identifiers can only be used on fields with one identifier. Found %v.", len(field.Names))
		p.logError(errMsg, pos, nil)
	}
	return tuName
}

func (p *Parser) logError(msg string, pos token.Position, origErr *scanner.Error) {
	if origErr != nil {
		pos.Column = origErr.Pos.Column
	}
	log.Fatalf("Error: %v: %v", pos, msg)
}

func (p *Parser) logWarning(msg string, pos token.Position, origErr *scanner.Error) {
	if origErr != nil {
		pos.Column = origErr.Pos.Column
	}
	log.Printf("Warning: %v: %v", pos, msg)
}

func rename(name string, existingNames map[string]any) string {
	newName := name
	for i := 2; ; i += 1 {
		newName = fmt.Sprintf("%v%v", name, i)
		_, isDuplicate := existingNames[newName]
		if !isDuplicate {
			break
		}
	}
	return newName
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
		if len(f.selectOptions) == 0 {
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
	structDecl, ok := n.(*ast.GenDecl)
	if !ok {
		return nil
	}
	structSpec, ok := structDecl.Specs[0].(*ast.TypeSpec)
	if !ok {
		return nil
	}
	_, ok = structSpec.Type.(*ast.StructType)
	if !ok {
		return nil
	}
	structSpec.Doc = structDecl.Doc
	return structSpec
}

// Removes one trailing underscore from a string
// if present and returns it with true.
// Otherwise returns s and false.
func trimUnderscore(s string) (string, bool) {
	if len(s) > 1 && s[len(s)-1] == '_' {
		return s[:len(s)-1], true
	}
	return s, false
}
