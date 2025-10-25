package generator_test

import (
	"bufio"
	"bytes"
	"strings"
	"testing"

	. "github.com/snonky/pocketbase-gogen/generator"
)

func TestSimpleMethod(t *testing.T) {
	template := `func (s *StructName) Method() {
	fmt.Println("Hi!")
}
`

	equal, err := expectGeneratedMethod(template, template, "import \"fmt\"")
	if err != nil {
		t.Fatalf("Error during generation: %v", err)
	}
	if !equal {
		t.Fatal("The simple method did not have the expected generation result")
	}
}

func TestReadAndAssign(t *testing.T) {
	template := `func (s *StructName) Method() {
	_ = s.intField
	s.stringField = "Hi!"
}
`

	expectedGeneration := `func (s *StructName) Method() {
	_ = s.IntField()
	s.SetStringField("Hi!")
}
`

	equal, err := expectGeneratedMethod(template, expectedGeneration)
	if err != nil {
		t.Fatalf("Error during generation: %v", err)
	}
	if !equal {
		t.Fatal("The read and assign statements did not have the expected generation result")
	}
}

func TestMultiRead(t *testing.T) {
	template := `func (s *StructName) Method() {
	_, _ = s.other, s.intField
}
`

	expectedGeneration := `func (s *StructName) Method() {
	_, _ = s.Other(), s.IntField()
}
`

	equal, err := expectGeneratedMethod(template, expectedGeneration)
	if err != nil {
		t.Fatalf("Error during generation: %v", err)
	}
	if !equal {
		t.Fatal("The multi read statement did not have the expected generation result")
	}
}

func TestMultiAssign(t *testing.T) {
	template := `func (s *StructName) Method() {
	s.intField, s.stringField = 42, "42"
}
`

	expectedGeneration := `func (s *StructName) Method() {
	intField, stringField := 42, "42"
	s.SetStringField(stringField)
	s.SetIntField(intField)
}
`

	equal, err := expectGeneratedMethod(template, expectedGeneration)
	if err != nil {
		t.Fatalf("Error during generation: %v", err)
	}
	if !equal {
		t.Fatal("The multi assign statement did not have the expected generation result")
	}
}

func TestVarSwitch(t *testing.T) {
	template := `func (s *StructName) Method() {
	s.intField, s.intField2 = s.intField2, s.intField
}
`

	expectedGeneration := `func (s *StructName) Method() {
	intField, intField2 := s.IntField2(), s.IntField()
	s.SetIntField2(intField2)
	s.SetIntField(intField)
}
`

	equal, err := expectGeneratedMethod(template, expectedGeneration)
	if err != nil {
		t.Fatalf("Error during generation: %v", err)
	}
	if !equal {
		t.Fatal("The variable switch statement did not have the expected generation result")
	}
}

func TestSystemFields(t *testing.T) {
	template := `func (s *StructName) Method() {
	_ = s.Id
	s.Id = "wow"
	s.password = "Mb2.r5oHf-0t"
	_ = s.tokenKey
	s.tokenKey = "key"
	_ = s.email
	s.email = "test@example.com"
	_ = s.emailVisibility
	s.emailVisibility = false
	_ = s.verified
	s.verified = true
}
`

	expectedGeneration := `func (s *StructName) Method() {
	_ = s.Id
	s.Id = "wow"
	s.SetPassword("Mb2.r5oHf-0t")
	_ = s.TokenKey()
	s.SetTokenKey("key")
	_ = s.Email()
	s.SetEmail("test@example.com")
	_ = s.EmailVisibility()
	s.SetEmailVisibility(false)
	_ = s.Verified()
	s.SetVerified(true)
}
`

	equal, err := expectGeneratedMethod(template, expectedGeneration)
	if err != nil {
		t.Fatalf("Error during generation: %v", err)
	}
	if !equal {
		t.Fatal("getting/setting all system fields did not have the expected generation result")
	}
}

func TestChainedSelectors(t *testing.T) {
	template := `func (s *StructName) Method() {
	_ = s.other.other.other.selectField
	s.other.other.intField = 42
}
`

	expectedGeneration := `func (s *StructName) Method() {
	_ = s.Other().Other().Other().SelectField()
	s.Other().Other().SetIntField(42)
}
`

	equal, err := expectGeneratedMethod(template, expectedGeneration)
	if err != nil {
		t.Fatalf("Error during generation: %v", err)
	}
	if !equal {
		t.Fatal("the chained selector statements did not have the expected generation result")
	}
}

func TestOtherProxyMethod(t *testing.T) {
	template := `func (s *StructName) Method() {
	_ = s.other.other.other.OtherMethod().other.email
	s.other.other.other.OtherMethod().other.email = "test@example.com"
}
`

	expectedGeneration := `func (s *StructName) Method() {
	_ = s.Other().Other().Other().OtherMethod().Other().Email()
	s.Other().Other().Other().OtherMethod().Other().SetEmail("test@example.com")
}
`

	equal, err := expectGeneratedMethod(template, expectedGeneration)
	if err != nil {
		t.Fatalf("Error during generation: %v", err)
	}
	if !equal {
		t.Fatal("the other proxy method call did not have the expected generation result")
	}
}

func TestInitAndPostAssignments(t *testing.T) {
	template := `func (s *StructName) Method() {
	if s.intField = 42; s.intField == 42 {
	}
	for s.intField = 30; s.intField <= 100; s.intField += 3 {
	}
	switch s.intField = 0; s.intField {
	}
	var a interface{} = s.intField
	switch s.intField = 2; a.(type) {
	}
}
`

	expectedGeneration := `func (s *StructName) Method() {
	if s.SetIntField(42); s.IntField() == 42 {
	}
	for s.SetIntField(30); s.IntField() <= 100; s.SetIntField(s.IntField() + 3) {
	}
	switch s.SetIntField(0); s.IntField() {
	}
	var a interface{} = s.IntField()
	switch s.SetIntField(2); a.(type) {
	}
}
`

	equal, err := expectGeneratedMethod(template, expectedGeneration)
	if err != nil {
		t.Fatalf("Error during generation: %v", err)
	}
	if !equal {
		t.Fatal("the init/post statements did not have the expected generation result")
	}
}

func TestMultiInitAndPostAssignments(t *testing.T) {
	template := `func (s *StructName) Method() {
	if s.intField, s.stringField = 42, "str"; s.intField == 42 {
	}
	for s.intField, s.stringField = 30, "a"; s.intField <= 100; s.intField, s.stringField = -1, "b" {
		_ = "Hello World!"
	}
	switch s.intField, s.stringField = 0, "c"; s.intField {
	}
	var a interface{} = s.intField
	switch s.intField, s.other = 2, s.others[0]; a.(type) {
	}
}
`

	expectedGeneration := `func (s *StructName) Method() {
	intField, stringField := 42, "str"
	s.SetIntField(intField)
	s.SetStringField(stringField)
	if s.IntField() == 42 {
	}
	intField2, stringField2 := 30, "a"
	s.SetIntField(intField2)
	s.SetStringField(stringField2)
	for s.IntField() <= 100 {
		_ = "Hello World!"
		intField3, stringField3 := -1, "b"
		s.SetIntField(intField3)
		s.SetStringField(stringField3)
	}
	intField4, stringField4 := 0, "c"
	s.SetIntField(intField4)
	s.SetStringField(stringField4)
	switch s.IntField() {
	}
	var a interface{} = s.IntField()
	intField5, other := 2, s.Others()[0]
	s.SetIntField(intField5)
	s.SetOther(other)
	switch a.(type) {
	}
}
`

	equal, err := expectGeneratedMethod(template, expectedGeneration)
	if err != nil {
		t.Fatalf("Error during generation: %v", err)
	}
	if !equal {
		t.Fatal("the multi init/post statements did not have the expected generation result")
	}
}

func TestReassignments(t *testing.T) {
	template := `func (s *StructName) Method() {
	s.intField += 42
	s.stringField += "_"
	s.intField2 -= 12
	s.intField *= 2
	s.intField2 /= 1
	s.intField >>= 3
	s.intField2 <<= 4
	s.intField %= 9
	s.intField2 &= 12
	s.intField |= 18
	s.intField2 ^= 21
	s.intField &^= 24
}
`

	expectedGeneration := `func (s *StructName) Method() {
	s.SetIntField(s.IntField() + 42)
	s.SetStringField(s.StringField() + "_")
	s.SetIntField2(s.IntField2() - 12)
	s.SetIntField(s.IntField() * 2)
	s.SetIntField2(s.IntField2() / 1)
	s.SetIntField(s.IntField() >> 3)
	s.SetIntField2(s.IntField2() << 4)
	s.SetIntField(s.IntField() % 9)
	s.SetIntField2(s.IntField2() & 12)
	s.SetIntField(s.IntField() | 18)
	s.SetIntField2(s.IntField2() ^ 21)
	s.SetIntField(s.IntField() &^ 24)
}
`

	equal, err := expectGeneratedMethod(template, expectedGeneration)
	if err != nil {
		t.Fatalf("Error during generation: %v", err)
	}
	if !equal {
		t.Fatal("the reassign statements did not have the expected generation result")
	}
}

func TestRangeStmt(t *testing.T) {
	template := `func (s *StructName) Method() {
	for i, e := range s.others {
		_, _ = i, e
	}
	for s.intField, s.other = range s.others {
		_ = "Hello!"
	}
}
`

	expectedGeneration := `func (s *StructName) Method() {
	for i, e := range s.Others() {
		_, _ = i, e
	}
	for intField, other := range s.Others() {
		s.SetIntField(intField)
		s.SetOther(other)
		_ = "Hello!"
	}
}
`

	equal, err := expectGeneratedMethod(template, expectedGeneration)
	if err != nil {
		t.Fatalf("Error during generation: %v", err)
	}
	if !equal {
		t.Fatal("the range statements did not have the expected generation result")
	}
}

func TestElseIfBranch(t *testing.T) {
	template := `func (s *StructName) Method() {
	if s.intField, s.stringField = 77, "x"; true {
	} else if s.email = s.stringField; false {
	}
}
`

	expectedGeneration := `func (s *StructName) Method() {
	intField, stringField := 77, "x"
	s.SetIntField(intField)
	s.SetStringField(stringField)
	if true {
	} else if s.SetEmail(s.StringField()); false {
	}
}
`

	equal, err := expectGeneratedMethod(template, expectedGeneration)
	if err != nil {
		t.Fatalf("Error during generation: %v", err)
	}
	if !equal {
		t.Fatal("the else if branch did not have the expected generation result")
	}
}

func TestImpossibleElseIfBranch(t *testing.T) {
	// multi assignment in init statement of else if
	// is impossible to convert to getter/setter syntax
	template := `func (s *StructName) Method() {
	if s.intField, s.stringField = 77, "x"; true {
	} else if s.email, s.intField = s.stringField, 99; false {
	}
}
`

	template = addMethodBoilerplate(template)
	parser, _ := NewTemplateParser([]byte(template))
	_, err := Generate(parser, ".", "test")
	if err == nil {
		t.Fatal("the impossible else if branch init statement did not cause the generation to error")
	}
}

func TestPartialProxyAassignment(t *testing.T) {
	template := `
func (s *StructName) Method() {
	var a, b int
	a, s.intField, b, s.intField2 = 1, 2, 3, 4
	_, _ = a, b
}
`

	expectedGeneration := `func (s *StructName) Method() {
	var a, b int
	a, intField, b, intField2 := 1, 2, 3, 4
	s.SetIntField2(intField2)
	s.SetIntField(intField)
	_, _ = a, b
}
`

	equal, err := expectGeneratedMethod(template, expectedGeneration)
	if err != nil {
		t.Fatalf("Error during generation: %v", err)
	}
	if !equal {
		t.Fatal("the mix between local var and proxy struct assignments did not have the expected generation result")
	}
}

func TestPartialInitAssignment(t *testing.T) {
	template := `func (s *StructName) Method() {
	var a, b int
	if a, s.intField, b, s.intField2 = 1, 2, 3, 4; true {
		_, _ = a, b
	}
}
`

	expectedGeneration := `func (s *StructName) Method() {
	var a, b int
	intField, intField2 := 2, 4
	s.SetIntField(intField)
	s.SetIntField2(intField2)
	if a, b = 1, 3; true {
		_, _ = a, b
	}
}
`

	equal, err := expectGeneratedMethod(template, expectedGeneration)
	if err != nil {
		t.Fatalf("Error during generation: %v", err)
	}
	if !equal {
		t.Fatal("the mix between local var and proxy struct assignments in the if-init-statement did not have the expected generation result")
	}
}

func TestSingleSelectAssign(t *testing.T) {
	template := `func (s *StructName) Method() {
	var i int = 1
	s.other.selectField = i
}
`

	expectedGeneration := `func (s *StructName) Method() {
	var i int = 1
	s.Other().SetSelectField(Enum(i))
}
`

	equal, err := expectGeneratedMethod(template, expectedGeneration)
	if err != nil {
		t.Fatalf("Error during generation: %v", err)
	}
	if !equal {
		t.Fatal("the single select type field did not have the expected generation result")
	}
}

func TestMultiSelectAssign(t *testing.T) {
	template := `func (s *StructName) Method() {
	i := []int{1, 0}
	s.other.multiSelectField = i
}
`

	expectedGeneration := `func (s *StructName) Method() {
	i := []int{1, 0}
	s.Other().SetMultiSelectField(*(*[]SelectType)(unsafe.Pointer(&i)))
}
`

	equal, err := expectGeneratedMethod(template, expectedGeneration)
	if err != nil {
		t.Fatalf("Error during generation: %v", err)
	}
	if !equal {
		t.Fatal("the multi select type field assign did not have the expected generation result")
	}
}

func TestNestedContainers(t *testing.T) {
	template := `func (s *StructName) Method() {
	switch s.email {
	case "":
		fallthrough
	case "b":
		for s.intField, s.intField2 = 15, 16; true; s.intField, s.stringField = 9, "" {
			_ = "Hello World!"
		}
	case "c":
		return
	}
	a := make(chan int)
	b := make(chan int)
	select {
	case <-a:
	case a <- s.intField:
		for s.intField, s.intField2 = 15, 16; true; s.intField, s.stringField = 9, "" {
			_ = "Hi there!"
		}
	case <-b:
		return
	}
}
`

	expectedGeneration := `func (s *StructName) Method() {
	switch s.Email() {
	case "":
		fallthrough
	case "b":
		intField, intField2 := 15, 16
		s.SetIntField(intField)
		s.SetIntField2(intField2)
		for true {
			_ = "Hello World!"
			intField3, stringField := 9, ""
			s.SetIntField(intField3)
			s.SetStringField(stringField)
		}
	case "c":
		return
	}
	a := make(chan int)
	b := make(chan int)
	select {
	case <-a:
	case a <- s.IntField():
		intField4, intField22 := 15, 16
		s.SetIntField(intField4)
		s.SetIntField2(intField22)
		for true {
			_ = "Hi there!"
			intField5, stringField2 := 9, ""
			s.SetIntField(intField5)
			s.SetStringField(stringField2)
		}
	case <-b:
		return
	}
}
`

	equal, err := expectGeneratedMethod(template, expectedGeneration)
	if err != nil {
		t.Fatalf("Error during generation: %v", err)
	}
	if !equal {
		t.Fatal("the nested block-statements in case clauses did not have the expected generation result")
	}
}

func TestTypeCheckerError(t *testing.T) {
	template := `func (s *StructName) Method() {
	s.intField = "hello"
}
`

	template = addMethodBoilerplate(template)
	parser, _ := NewTemplateParser([]byte(template))
	_, err := Generate(parser, ".", "test")
	if err == nil {
		t.Fatal("the type checker error did not cause the generation to error")
	}
}

func TestNameShadowing(t *testing.T) {
	// Shadow the core.Record.Set Method with a proxy method of the same name
	template := `func (s *StructName) Set() {
	_ = "Shadow!"
}
`

	template = addMethodBoilerplate(template)
	parser, _ := NewTemplateParser([]byte(template))
	_, err := Generate(parser, ".", "test")
	if err == nil {
		t.Fatal("the shadowed core.Record method did not cause the generation to error")
	}
}

var testTemplateStructs = `type StructName struct {
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
	verified 	bool
	intField    int
	intField2   int
	stringField string
	other       *OtherStruct
	others      []*OtherStruct
}

type OtherStruct struct {
	intField int
	// select: SelectType
	// - opt1
	// - opt2
	// - opt3
	multiSelectField []int
	// select: Enum
	// - optA
	// - optB
	selectField int
	other		*StructName
}

func (o *OtherStruct) OtherMethod() *OtherStruct {
	return o
}
`

func expectGeneratedMethod(templateMethod, expectedMethod string, imports ...string) (bool, error) {
	input := addMethodBoilerplate(templateMethod, imports...)

	parser, err := NewTemplateParser([]byte(input))
	if err != nil {
		return false, err
	}
	outBytes, err := Generate(parser, ".", "test")
	if err != nil {
		return false, err
	}

	output := extractMethod(outBytes)
	return output == expectedMethod, nil
}

func extractMethod(proxyCode []byte) string {
	reader := bytes.NewReader(proxyCode)
	lineReader := bufio.NewReader(reader)

	var doRead bool
	var sb strings.Builder
	line, err := lineReader.ReadBytes('\n')
	for ; err == nil; line, err = lineReader.ReadBytes('\n') {
		lineStr := string(line)
		if !doRead && len(lineStr) >= 4 && lineStr[:4] == "func" {
			doRead = true
		}
		if doRead {
			sb.WriteString(lineStr)
		}
		if doRead && len(lineStr) >= 1 && lineStr[:1] == "}" {
			break
		}
	}

	return sb.String()
}

func addMethodBoilerplate(method string, imports ...string) string {
	structs := addBoilerplate(testTemplateStructs, imports...)
	return structs + "\n" + method
}
