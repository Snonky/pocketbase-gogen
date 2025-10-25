package generator_test

import (
	"bufio"
	"bytes"
	"strings"
	"testing"

	. "github.com/snonky/pocketbase-gogen/generator"
)

var expectedAuthCollectionStruct = `type AuthCollection struct {
	// collection-name: auth_collection
	// system: id
	Id string
	// system: password
	password string
	// system: tokenKey
	tokenKey string
	// system: email
	email string
	// system: emailVisibility
	emailVisibility bool
	// system: verified
	verified bool
	name     string
	avatar   string
	created  types.DateTime
	updated  types.DateTime
}
`

var expectedAllTypesCollectionStruct = `type AllFieldTypes struct {
	// collection-name: all_field_types
	// system: id
	Id             string
	text           string
	richText       string
	oneFile        string
	manyFiles      []string
	floatingNumber float64
	intergerNumber int
	boolValue      bool
	email          string
	url            string
	date           types.DateTime
	// select: SingleSelectSelectType
	// - optionA
	// - optionB
	// - optionC
	singleSelect int
	// select: MultiSelectSelectType
	// - optionD
	// - optionE
	multiSelect    []int
	json           string
	singleRelation *AllFieldTypes
	multiRelation  []*AllFieldTypes
	created        types.DateTime
	updated        types.DateTime
}
`

var expectedReservedGoNameCollectionStruct = `type WithReservedGoNames struct {
	// collection-name: with_reserved_go_names
	// system: id
	Id      string
	func_   string
	type_   string
	struct_ string
	// select: VarSelectType
	// - var
	// - struct
	var_    int
	created types.DateTime
	updated types.DateTime
}
`

func TestTemplate(t *testing.T) {
	collections, err := QuerySchema("./db_test/test_pb_data", false)
	if err != nil {
		t.Fatalf("Error during schema query: %v", err)
	}

	template, err := Template(collections, ".", "test")
	if err != nil {
		t.Fatalf("Error during template generation: %v", err)
	}

	structDefs := separateTemplateStructs(template)

	if len(structDefs) != 3 {
		t.Fatal("the number of struct definitions does not match the number of collections in the schema")
	}

	if structDefs[0] != expectedAuthCollectionStruct {
		t.Fatal("the test auth collection did not result in the expected template struct")
	}

	if structDefs[1] != expectedAllTypesCollectionStruct {
		t.Fatal("the test collection containing all pocketbase field types did not result in the expected template struct")
	}

	if structDefs[2] != expectedReservedGoNameCollectionStruct {
		t.Fatal("the test collection containing field names that are reserved go names did not result in the expected template struct")
	}
}

func TestTemplatePackageName(t *testing.T) {
	_, err := Template(nil, ".", "validpackagename")
	if err != nil {
		t.Fatalf("valid package name caused error: %v", err)
	}

	_, err = Template(nil, ".", "valid_package_name")
	if err != nil {
		t.Fatalf("valid package name caused error: %v", err)
	}

	_, err = Template(nil, ".", "invalid-packagename")
	if err == nil {
		t.Fatal("the invalid package name did not cause an error")
	}
}

func separateTemplateStructs(templateFile []byte) []string {
	structs := make([]string, 0, 3)

	reader := bytes.NewReader(templateFile)
	lineReader := bufio.NewReader(reader)

	var readStruct bool
	var sb strings.Builder
	line, err := lineReader.ReadBytes('\n')
	for ; err == nil; line, err = lineReader.ReadBytes('\n') {
		lineStr := string(line)
		if !readStruct && len(lineStr) >= 4 && lineStr[:4] == "type" {
			readStruct = true
		}
		if readStruct {
			sb.WriteString(lineStr)
		}
		if readStruct && len(lineStr) >= 1 && lineStr[:1] == "}" {
			readStruct = false
			structs = append(structs, sb.String())
			sb.Reset()
		}
	}

	return structs
}
