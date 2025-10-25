package generator_test

import (
	"bufio"
	"bytes"
	"strings"
	"testing"

	. "github.com/snonky/pocketbase-gogen/generator"
)

func TestMinimalGeneration(t *testing.T) {
	template := `type Minimal struct {
	value string
}
`
	expectedGeneration := `type Minimal struct {
	core.BaseRecordProxy
}

func (p *Minimal) Value() string {
	return p.GetString("value")
}

func (p *Minimal) SetValue(value string) {
	p.Set("value", value)
}
`

	equal, err := expectGenerated(template, expectedGeneration)
	if err != nil {
		t.Fatalf("Error during generation: %v", err)
	}
	if !equal {
		t.Fatal("the minimal template did not have the expected generation result")
	}
}

func TestSingleSelectTypeField(t *testing.T) {
	template := `type HasSelect struct {
	// select: Enum
	// - opt1
	// - opt2
	value int
}
`
	expectedGeneration := `type Enum int

const (
	Opt1 Enum = iota
	Opt2
)

var zzEnumSelectNameMap = map[string]Enum{
	"opt1": 0,
	"opt2": 1,
}
var zzEnumSelectIotaMap = map[Enum]string{
	0: "opt1",
	1: "opt2",
}

type HasSelect struct {
	core.BaseRecordProxy
}

func (p *HasSelect) Value() Enum {
	option := p.GetString("value")
	i, ok := zzEnumSelectNameMap[option]
	if !ok {
		panic("Unknown select value")
	}
	return i
}

func (p *HasSelect) SetValue(value Enum) {
	i, ok := zzEnumSelectIotaMap[value]
	if !ok {
		panic("Unknown select value")
	}
	p.Set("value", i)
}
`

	equal, err := expectGenerated(template, expectedGeneration)
	if err != nil {
		t.Fatalf("Error during generation: %v", err)
	}
	if !equal {
		t.Fatal("the single selection type field did not have the expected generation result")
	}
}

func TestMultiSelectTypeField(t *testing.T) {
	template := `type HasSelect struct {
	// select: Enum
	// - opt1
	// - opt2
	value []int
}
`

	expectedGeneration := `type Enum int

const (
	Opt1 Enum = iota
	Opt2
)

var zzEnumSelectNameMap = map[string]Enum{
	"opt1": 0,
	"opt2": 1,
}
var zzEnumSelectIotaMap = map[Enum]string{
	0: "opt1",
	1: "opt2",
}

type HasSelect struct {
	core.BaseRecordProxy
}

func (p *HasSelect) Value() []Enum {
	options := p.GetStringSlice("value")
	is := make([]Enum, 0, len(options))
	for _, o := range options {
		i, ok := zzEnumSelectNameMap[o]
		if !ok {
			panic("Unknown select value")
		}
		is = append(is, i)
	}
	return is
}

func (p *HasSelect) SetValue(value []Enum) {
	is := make([]string, 0, len(value))
	for _, s := range value {
		i, ok := zzEnumSelectIotaMap[s]
		if !ok {
			panic("Unknown select value")
		}
		is = append(is, i)
	}
	p.Set("value", is)
}
`

	equal, err := expectGenerated(template, expectedGeneration)
	if err != nil {
		t.Fatalf("Error during generation: %v", err)
	}
	if !equal {
		t.Fatal("the multi select type field did not have the expected generation result")
	}
}

func TestSingleRelationField(t *testing.T) {
	template := `type Parent struct {
	child *Child
}

type Child struct {}
`

	expectedGeneration := `type Parent struct {
	core.BaseRecordProxy
}

func (p *Parent) Child() *Child {
	var proxy *Child
	if rel := p.ExpandedOne("child"); rel != nil {
		proxy = &Child{}
		proxy.Record = rel
	}
	return proxy
}

func (p *Parent) SetChild(child *Child) {
	var id string
	if child != nil {
		id = child.Id
	}
	p.Record.Set("child", id)
	e := p.Expand()
	if child != nil {
		e["child"] = child.Record
	} else {
		delete(e, "child")
	}
	p.SetExpand(e)
}

type Child struct {
	core.BaseRecordProxy
}
`

	equal, err := expectGenerated(template, expectedGeneration)
	if err != nil {
		t.Fatalf("Error during generation: %v", err)
	}
	if !equal {
		t.Fatal("the single relation field did not have the expected generation result")
	}
}

func TestMultiRelationField(t *testing.T) {
	template := `type Parent struct {
	children []*Child
}

type Child struct {
}
`

	expectedGeneration := `type Parent struct {
	core.BaseRecordProxy
}

func (p *Parent) Children() []*Child {
	rels := p.ExpandedAll("children")
	proxies := make([]*Child, len(rels))
	for i := range len(rels) {
		proxies[i] = &Child{}
		proxies[i].Record = rels[i]
	}
	return proxies
}

func (p *Parent) SetChildren(children []*Child) {
	records := make([]*core.Record, len(children))
	ids := make([]string, len(children))
	for i, r := range children {
		records[i] = r.Record
		ids[i] = r.Record.Id
	}
	p.Record.Set("children", ids)
	e := p.Expand()
	e["children"] = records
	p.SetExpand(e)
}

type Child struct {
	core.BaseRecordProxy
}
`

	equal, err := expectGenerated(template, expectedGeneration)
	if err != nil {
		t.Fatalf("Error during generation: %v", err)
	}
	if !equal {
		t.Fatal("the multi relation field did not have the expected generation")
	}
}

func TestAllBasicTypes(t *testing.T) {
	template := `type AllBasicTypes struct {
	field1 bool
	field2 int
	field3 float64
	field4 string
	field5 types.DateTime
}
`

	expectedGeneration := `type AllBasicTypes struct {
	core.BaseRecordProxy
}

func (p *AllBasicTypes) Field1() bool {
	return p.GetBool("field1")
}

func (p *AllBasicTypes) SetField1(field1 bool) {
	p.Set("field1", field1)
}

func (p *AllBasicTypes) Field2() int {
	return p.GetInt("field2")
}

func (p *AllBasicTypes) SetField2(field2 int) {
	p.Set("field2", field2)
}

func (p *AllBasicTypes) Field3() float64 {
	return p.GetFloat("field3")
}

func (p *AllBasicTypes) SetField3(field3 float64) {
	p.Set("field3", field3)
}

func (p *AllBasicTypes) Field4() string {
	return p.GetString("field4")
}

func (p *AllBasicTypes) SetField4(field4 string) {
	p.Set("field4", field4)
}

func (p *AllBasicTypes) Field5() types.DateTime {
	return p.GetDateTime("field5")
}

func (p *AllBasicTypes) SetField5(field5 types.DateTime) {
	p.Set("field5", field5)
}
`

	equal, err := expectGenerated(template, expectedGeneration, "import \"github.com/pocketbase/pocketbase/tools/types\"")
	if err != nil {
		t.Fatalf("Error during generation: %v", err)
	}
	if !equal {
		t.Fatal("the basic typed fields did not have the expected generation")
	}
}

func TestRenamedField(t *testing.T) {
	template := `type Name struct {
	// schema-name: original_name
	newName string
}
`

	expectedGeneration := `type Name struct {
	core.BaseRecordProxy
}

func (p *Name) NewName() string {
	return p.GetString("original_name")
}

func (p *Name) SetNewName(newName string) {
	p.Set("original_name", newName)
}
`

	equal, err := expectGenerated(template, expectedGeneration)
	if err != nil {
		t.Fatalf("Error during generation: %v", err)
	}
	if !equal {
		t.Fatal("the renamed field did not have the expected generation result")
	}
}

func TestSystemField(t *testing.T) {
	template := `type Name struct {
	// system: important
	important string
}
`

	expectedGeneration := `type Name struct {
	core.BaseRecordProxy
}
`

	equal, err := expectGenerated(template, expectedGeneration)
	if err != nil {
		t.Fatalf("Error during generation: %v", err)
	}
	if !equal {
		t.Fatal("the system field did not have the expected generation")
	}
}

func TestUnderscoreEscapedField(t *testing.T) {
	template := `type Name struct {
	import_ string
}
`

	expectedGeneration := `type Name struct {
	core.BaseRecordProxy
}

func (p *Name) Import() string {
	return p.GetString("import")
}

func (p *Name) SetImport(import_ string) {
	p.Set("import", import_)
}
`

	equal, err := expectGenerated(template, expectedGeneration)
	if err != nil {
		t.Fatalf("Error during generation: %v", err)
	}
	if !equal {
		t.Fatal("the underscore-escaped field did not have the expected generation result")
	}
}

func TestRenamedSelectOptions(t *testing.T) {
	template := `type Name struct {
	// select: SelectTypeName
	// - optA
	// > RenameA
	select1 int
}
`

	expectedGeneration := `type SelectTypeName int

const RenameA SelectTypeName = iota

var zzSelectTypeNameSelectNameMap = map[string]SelectTypeName{"optA": 0}
var zzSelectTypeNameSelectIotaMap = map[SelectTypeName]string{0: "optA"}

type Name struct {
	core.BaseRecordProxy
}

func (p *Name) Select1() SelectTypeName {
	option := p.GetString("select1")
	i, ok := zzSelectTypeNameSelectNameMap[option]
	if !ok {
		panic("Unknown select value")
	}
	return i
}

func (p *Name) SetSelect1(select1 SelectTypeName) {
	i, ok := zzSelectTypeNameSelectIotaMap[select1]
	if !ok {
		panic("Unknown select value")
	}
	p.Set("select1", i)
}
`

	equal, err := expectGenerated(template, expectedGeneration)
	if err != nil {
		t.Fatalf("Error during generation: %v", err)
	}
	if !equal {
		t.Fatal("the renamed select options did not have the expected generation result")
	}
}

func TestDuplicateSelectTypeNames(t *testing.T) {
	template := `type Name struct {
	// select: SameName
	// - optA
	select1 int
	// select: SameName
	// - optB
	select2 int
}
`

	expectedGeneration := `type SameName int

const OptA SameName = iota

var zzSameNameSelectNameMap = map[string]SameName{"optA": 0}
var zzSameNameSelectIotaMap = map[SameName]string{0: "optA"}

type SameName2 int

const OptB SameName2 = iota

var zzSameName2SelectNameMap = map[string]SameName2{"optB": 0}
var zzSameName2SelectIotaMap = map[SameName2]string{0: "optB"}

type Name struct {
	core.BaseRecordProxy
}

func (p *Name) Select1() SameName {
	option := p.GetString("select1")
	i, ok := zzSameNameSelectNameMap[option]
	if !ok {
		panic("Unknown select value")
	}
	return i
}

func (p *Name) SetSelect1(select1 SameName) {
	i, ok := zzSameNameSelectIotaMap[select1]
	if !ok {
		panic("Unknown select value")
	}
	p.Set("select1", i)
}

func (p *Name) Select2() SameName2 {
	option := p.GetString("select2")
	i, ok := zzSameName2SelectNameMap[option]
	if !ok {
		panic("Unknown select value")
	}
	return i
}

func (p *Name) SetSelect2(select2 SameName2) {
	i, ok := zzSameName2SelectIotaMap[select2]
	if !ok {
		panic("Unknown select value")
	}
	p.Set("select2", i)
}
`

	equal, err := expectGenerated(template, expectedGeneration)
	if err != nil {
		t.Fatalf("Error during generation: %v", err)
	}
	if !equal {
		t.Fatal("the duplicate select type names did not have the expected generation result")
	}
}

func TestIdenticalSelectTypes(t *testing.T) {
	template := `type Name struct {
	// select: SameName
	// - sameName
	select1 int
	// select: SameName
	// - sameName
	select2 int
}
`

	expectedGeneration := `type SameName int

const SameName2 SameName = iota

var zzSameNameSelectNameMap = map[string]SameName{"sameName": 0}
var zzSameNameSelectIotaMap = map[SameName]string{0: "sameName"}

type Name struct {
	core.BaseRecordProxy
}

func (p *Name) Select1() SameName {
	option := p.GetString("select1")
	i, ok := zzSameNameSelectNameMap[option]
	if !ok {
		panic("Unknown select value")
	}
	return i
}

func (p *Name) SetSelect1(select1 SameName) {
	i, ok := zzSameNameSelectIotaMap[select1]
	if !ok {
		panic("Unknown select value")
	}
	p.Set("select1", i)
}

func (p *Name) Select2() SameName {
	option := p.GetString("select2")
	i, ok := zzSameNameSelectNameMap[option]
	if !ok {
		panic("Unknown select value")
	}
	return i
}

func (p *Name) SetSelect2(select2 SameName) {
	i, ok := zzSameNameSelectIotaMap[select2]
	if !ok {
		panic("Unknown select value")
	}
	p.Set("select2", i)
}
`

	equal, err := expectGenerated(template, expectedGeneration)
	if err != nil {
		t.Fatalf("Error during generation: %v", err)
	}
	if !equal {
		t.Fatal("the identical select types did not have the expected generation result")
	}
}

func TestUnknownType(t *testing.T) {
	template := `type Name struct {
		illegal float32
	}
	`

	template = addBoilerplate(template)
	parser, _ := NewTemplateParser([]byte(template))
	_, err := Generate(parser, ".", "test")
	if err == nil {
		t.Fatal("the illegally typed field did not cause the generation to error")
	}
}

func TestIllegalSelectFieldType(t *testing.T) {
	// Only int or []int is allowed for select types
	template := `type Name struct {
		// select: IllegalSelect
		// - optA
		// - optB
		illegal string
	}
	`

	template = addBoilerplate(template)
	_, err := NewTemplateParser([]byte(template))
	if err == nil {
		t.Fatal("the illegally typed select type field did not cause the generation to error")
	}
}

func TestUncommentedSystemField(t *testing.T) {
	template := `type Name struct {
	Id string
}
`
	template = addBoilerplate(template)
	parser, _ := NewTemplateParser([]byte(template))
	_, err := Generate(parser, ".", "test")
	if err == nil {
		t.Fatal("the uncommented system field did not cause the generation to error")
	}
}

func TestMalformedSelectComment(t *testing.T) {
	template := `type Name struct {
	// select:
	// - optA
	// - optB
	selectVar int
}
`
	template = addBoilerplate(template)
	_, err := NewTemplateParser([]byte(template))
	if err == nil {
		t.Fatal("the malformed select comment did not cause the generation to error")
	}

	template = `type Name struct {
		// select: SelectTypeName
		selectVar int
}
`
	template = addBoilerplate(template)
	_, err = NewTemplateParser([]byte(template))
	if err == nil {
		t.Fatal("the malformed select comment did not cause the generation to error")
	}

	template = `type Name struct {
		// select: SelectTypeName
		// one more line
		selectVar int
}
`
	template = addBoilerplate(template)
	_, err = NewTemplateParser([]byte(template))
	if err == nil {
		t.Fatal("the malformed select comment did not cause the generation to error")
	}

	template = `type Name struct {
		// select: SelectTypeName
		// - optA
		// - optB
		// > renameA
		// > renameB
		selectVar int
}
`
	template = addBoilerplate(template)
	_, err = NewTemplateParser([]byte(template))
	if err == nil {
		t.Fatal("the malformed select comment did not cause the generation to error")
	}

	template = `type Name struct {
		// select: SelectTypeName
		// - optA
		// - 
		selectVar int
}
`
	template = addBoilerplate(template)
	_, err = NewTemplateParser([]byte(template))
	if err == nil {
		t.Fatal("the malformed select comment did not cause the generation to error")
	}

	template = `type Name struct {
		// select: SelectTypeName
		// > aliasToNothing
		// - optA
		selectVar int
}
`
	template = addBoilerplate(template)
	_, err = NewTemplateParser([]byte(template))
	if err == nil {
		t.Fatal("the malformed select comment did not cause the generation to error")
	}

	template = `type Name struct {
		// select: SelectTypeName
		// - invalid-go-identifier
		selectVar int
}
`
	template = addBoilerplate(template)
	_, err = NewTemplateParser([]byte(template))
	if err == nil {
		t.Fatal("the malformed select comment did not cause the generation to error")
	}

	template = `type Name struct {
		// select: SelectTypeName
		// - func
		selectVar int
}
`
	template = addBoilerplate(template)
	_, err = NewTemplateParser([]byte(template))
	if err == nil {
		t.Fatal("the malformed select comment did not cause the generation to error")
	}
}

func TestIllegalMultiNameFields(t *testing.T) {
	template := `type Name struct {
	select1, func_ int
}
`

	template = addBoilerplate(template)
	_, err := NewTemplateParser([]byte(template))
	if err == nil {
		t.Fatal("the illegal multi name field with an underscore escape did not cause the generation to error")
	}

	template = `type Name struct {
		// system: both!
		name1, name2 int
}
`

	template = addBoilerplate(template)
	_, err = NewTemplateParser([]byte(template))
	if err == nil {
		t.Fatal("the illegal multi name system field did not cause the generation to error")
	}

	template = `type Name struct {
		// select: SelectTypeName
		// - a
		// - b
		name1, name2 int
}
`

	template = addBoilerplate(template)
	_, err = NewTemplateParser([]byte(template))
	if err == nil {
		t.Fatal("the illegal multi name select type field did not cause the generation to error")
	}

	template = `type Name struct {
		// schema-name: both!
		name1, name2 int
}
`

	template = addBoilerplate(template)
	_, err = NewTemplateParser([]byte(template))
	if err == nil {
		t.Fatal("the illegal multi name renamed field did not cause the generation to error")
	}
}

func TestDuplicateSelectOption(t *testing.T) {
	template := `type Name struct {
	// select: SelectTypeName2
	// - sameName
	select1 int
	// select: SelectTypeName1
	// - sameName
	select2 int
}
`

	expectedGeneration := `type SelectTypeName2 int

const SameName SelectTypeName2 = iota

var zzSelectTypeName2SelectNameMap = map[string]SelectTypeName2{"sameName": 0}
var zzSelectTypeName2SelectIotaMap = map[SelectTypeName2]string{0: "sameName"}

type SelectTypeName1 int

const SameName2 SelectTypeName1 = iota

var zzSelectTypeName1SelectNameMap = map[string]SelectTypeName1{"sameName": 0}
var zzSelectTypeName1SelectIotaMap = map[SelectTypeName1]string{0: "sameName"}

type Name struct {
	core.BaseRecordProxy
}

func (p *Name) Select1() SelectTypeName2 {
	option := p.GetString("select1")
	i, ok := zzSelectTypeName2SelectNameMap[option]
	if !ok {
		panic("Unknown select value")
	}
	return i
}

func (p *Name) SetSelect1(select1 SelectTypeName2) {
	i, ok := zzSelectTypeName2SelectIotaMap[select1]
	if !ok {
		panic("Unknown select value")
	}
	p.Set("select1", i)
}

func (p *Name) Select2() SelectTypeName1 {
	option := p.GetString("select2")
	i, ok := zzSelectTypeName1SelectNameMap[option]
	if !ok {
		panic("Unknown select value")
	}
	return i
}

func (p *Name) SetSelect2(select2 SelectTypeName1) {
	i, ok := zzSelectTypeName1SelectIotaMap[select2]
	if !ok {
		panic("Unknown select value")
	}
	p.Set("select2", i)
}
`

	equal, err := expectGenerated(template, expectedGeneration)
	if err != nil {
		t.Fatalf("Error during generation: %v", err)
	}
	if !equal {
		t.Fatal("the duplicate select option names did not have the expected generation result")
	}
}

func TestCollectionNameGetter(t *testing.T) {
	template := `type Name struct {
	// collection-name: collection_name
	firstField string
}
`

	expectedGeneration := `type Name struct {
	core.BaseRecordProxy
}

func (p *Name) CollectionName() string {
	return "collection_name"
}

func (p *Name) FirstField() string {
	return p.GetString("firstField")
}

func (p *Name) SetFirstField(firstField string) {
	p.Set("firstField", firstField)
}
`

	equal, err := expectGenerated(template, expectedGeneration)
	if err != nil {
		t.Fatalf("Error during generation: %v", err)
	}
	if !equal {
		t.Fatal("the collection name comment did not have the expected generation result")
	}
}

func expectGenerated(input, expectedOutput string, imports ...string) (bool, error) {
	input = addBoilerplate(input, imports...)

	parser, err := NewTemplateParser([]byte(input))
	if err != nil {
		return false, err
	}
	outBytes, err := Generate(parser, ".", "test")
	if err != nil {
		return false, err
	}

	output := removeBoilerplate(outBytes)

	return output == expectedOutput, nil
}

// Removes everything up until the first line that starts
// with "type"
func removeBoilerplate(sourceCode []byte) string {
	reader := bytes.NewReader(sourceCode)
	lineReader := bufio.NewReader(reader)

	var sb strings.Builder
	var doRead bool
	line, err := lineReader.ReadBytes('\n')
	for ; err == nil; line, err = lineReader.ReadBytes('\n') {
		lineStr := string(line)
		if len(lineStr) >= 4 && lineStr[:4] == "type" {
			doRead = true
		}
		if doRead {
			sb.WriteString(lineStr)
		}
	}

	output := sb.String()
	return output
}

func addBoilerplate(sourceCode string, imports ...string) string {
	var sb strings.Builder
	sb.WriteString("package test")
	sb.WriteRune('\n')
	for _, i := range imports {
		sb.WriteString(i)
		sb.WriteRune('\n')
	}
	sb.WriteString(sourceCode)
	return sb.String()
}
