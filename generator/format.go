package generator

import (
	"bytes"
	"errors"
	"fmt"
	"go/ast"
	"go/format"
	"go/parser"
	"go/token"
	"strings"

	"github.com/iancoleman/strcase"
	"golang.org/x/tools/imports"
)

func printAST(f *ast.File, fset *token.FileSet, filename string) ([]byte, error) {
	buf := &bytes.Buffer{}
	if err := format.Node(buf, fset, f); err != nil {
		return nil, err
	}

	sourceCode, err := imports.Process(filename, buf.Bytes(), nil)
	if err != nil {
		return nil, err
	}

	return sourceCode, nil
}

// Converts an ast node to a string
func nodeString(n ast.Node) (string, error) {
	fset := token.NewFileSet()
	sb := &strings.Builder{}
	err := format.Node(sb, fset, n)
	if err != nil {
		return "", err
	}
	return sb.String(), nil
}

func toIdentifier(s string) (*ast.Ident, error) {
	validated, err := validateIdentifier(s)
	if err != nil {
		return nil, err
	}
	return ast.NewIdent(validated), nil
}

// Validates if the given string s can be used
// as an identifier in go source code.
// If not, it appends a '_' and checks again.
// Errors if the string is still not valid.
func validateIdentifier(s string) (string, error) {
	origS := s
	parsed, err := parser.ParseExpr(s)
	_, ok := parsed.(*ast.Ident)
	// This check fails e.g. when the field name is a reserved go keyword
	if err != nil || !ok {
		s += "_" // Add a _ to circumvent the reservation
		parsed, err = parser.ParseExpr(s)
		_, ok = parsed.(*ast.Ident)
	}
	if err != nil || !ok {
		errMsg := fmt.Sprintf("Error: Encoutered `%v`, which can not be used as a go identifier", origS)
		return "", errors.New(errMsg)
	}

	return s, nil
}

// Returns true if the given string can be used as a package name
func validatePackageName(packageName string) bool {
	packageDecl := fmt.Sprintf("package %v", packageName)
	_, err := parser.ParseFile(token.NewFileSet(), "x.go", packageDecl, parser.SkipObjectResolution)

	return err == nil
}

func getterName(varName string) string {
	getterName := strcase.ToCamel(varName)
	return getterName
}

func setterName(varName string) string {
	setterName := "Set" + strcase.ToCamel(varName)
	return setterName
}
