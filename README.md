# PocketBase Type-Safe Go Code Generator

A tool for developers using [PocketBase](https://github.com/pocketbase/pocketbase) as a go backend framework.

Convert your PocketBase schema into type-safe accessor structs ("DAOs", "Proxies") for your code base.

Also supports custom methods that work with the typed data.

## Usage

### Step 0: Install `pocketbase-gogen`
```console
go install github.com/snonky/pocketbase-gogen@latest
```
You should now have access to the CLI with the `pocketbase-gogen` command.

### Step 1: Generate a template
```console
pocketbase-gogen template ./path/to/pb_data ./yourmodule/pbschema/template.go
```

You will now have `template.go` which is your "schema as code" and contains your PB schema as a set of go structs. The file contains a doc comment with a detailed description of what you can do to customize it.

### Step 2: Generate proxies from template

```console
pocketbase-gogen generate ./yourmodule/pbschema/template.go ./yourmodule/generated/proxies.go
```

You will now have `proxies.go` which contains the actual proxy structs
that you can drop in to use instead of raw `core.Record` structs from PocketBase ([PB doc on proxy usage](https://pocketbase.io/docs/go-record-proxy/)).

Optionally append the following flags:

 - `--utils` flag. The [example](#generate-utilsgo) shows what the result of that is.
 - `--hooks` flag. Its effect is also illustrated by [example](#generate-proxy-hooks).


> [!IMPORTANT]
> Do not run the generator against a production data base file.
> As with any code, please always test your generated code before putting it to use.
# Example

For the example we have a simple PB schema of 3 collections `person`, `child` and `bank_account`. They look like this:

<p align="center">
        <img src="https://i.imgur.com/yXYQtAD.png" alt="Example Schema Screenshot" />
</p>

### Running `pocketbase-gogen template` we get this:

```go
type BankAccount struct {
	// collection-name: bank_account
	// system: id
	Id    string
	money int
}

type Child struct {
	// collection-name: child
	// system: id
	Id   string
	name string
	age  int
}

type Person struct {
	// collection-name: person
	// system: id
	Id      string
	name    string
	address string
	// select: HealthSelectType
	// - good
	// - medium
	// - bad
	health   int
	account  *BankAccount
	children []*Child
}
```

Things to note about the template:

 - The `Id` field is marked as a system field and thus will not have getters/setters generated.
 - The `health` field is a PocketBase select type field which is always represented as an `int` (or `[]int` for multi select types) in the template. The field comment lists the select options.
 - The relation type fields `account` and `children` are already typed with the other template structs.
 - All template structs have a `// collection-name:` comment on their first field that stores the original collection name.

 ### Now running `pocketbase-gogen generate`

 The generated code for the three template structs comes out as this (they are in one file but for the example they are shown separately):

 ### Bank Account
```go
type BankAccount struct {
	core.BaseRecordProxy
}

func (p *BankAccount) CollectionName() string {
	return "bank_account"
}

func (p *BankAccount) Money() int {
	return p.GetInt("money")
}

func (p *BankAccount) SetMoney(money int) {
	p.Set("money", money)
}
```

### Child

```go
type Child struct {
	core.BaseRecordProxy
}

func (p *Child) CollectionName() string {
	return "child"
}

func (p *Child) Name() string {
	return p.GetString("name")
}

func (p *Child) SetName(name string) {
	p.Set("name", name)
}

func (p *Child) Age() int {
	return p.GetInt("age")
}

func (p *Child) SetAge(age int) {
	p.Set("age", age)
}
```

### Person 

```go
type HealthSelectType int

const (
	Good HealthSelectType = iota
	Medium
	Bad
)

var zzHealthSelectTypeSelectNameMap = map[string]HealthSelectType{
	"good":   0,
	"medium": 1,
	"bad":    2,
}
var zzHealthSelectTypeSelectIotaMap = map[HealthSelectType]string{
	0: "good",
	1: "medium",
	2: "bad",
}

type Person struct {
	core.BaseRecordProxy
}

func (p *Person) CollectionName() string {
	return "person"
}

func (p *Person) Name() string {
	return p.GetString("name")
}

func (p *Person) SetName(name string) {
	p.Set("name", name)
}

func (p *Person) Address() string {
	return p.GetString("address")
}

func (p *Person) SetAddress(address string) {
	p.Set("address", address)
}

func (p *Person) Health() HealthSelectType {
	option := p.GetString("health")
	i, ok := zzHealthSelectTypeSelectNameMap[option]
	if !ok {
		panic("Unknown select value")
	}
	return i
}

func (p *Person) SetHealth(health HealthSelectType) {
	i, ok := zzHealthSelectTypeSelectIotaMap[health]
	if !ok {
		panic("Unknown select value")
	}
	p.Set("health", i)
}

func (p *Person) Account() *BankAccount {
	var proxy *BankAccount
	if rel := p.ExpandedOne("account"); rel != nil {
		proxy = &BankAccount{}
		proxy.Record = rel
	}
	return proxy
}

func (p *Person) SetAccount(account *BankAccount) {
	var id string
	if account != nil {
		id = account.Id
	}
	p.Record.Set("account", id)
	e := p.Expand()
	if account != nil {
		e["account"] = account.Record
	} else {
		delete(e, "account")
	}
	p.SetExpand(e)
}

func (p *Person) Children() []*Child {
	rels := p.ExpandedAll("children")
	proxies := make([]*Child, len(rels))
	for i := range len(rels) {
		proxies[i] = &Child{}
		proxies[i].Record = rels[i]
	}
	return proxies
}

func (p *Person) SetChildren(children []*Child) {
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
```

Every proxy has getters and setters generated for its fields plus a `CollectionName()` convenience method.
`CollectionName()` is generated from the `// collection-name:` comment in the template.

Bank Account and Child are straightforward. Things of interest about the Person generation:

 - The `health` select type got its own go type of 
    ```go
    type HealthSelectType int
    ```
    with an accompanying `const` declaration:
    ```go
    const (
        Good HealthSelectType = iota
        Medium
        Bad
    )
    ```
    The constants guarantee correct select options in your application code.

 - For the relation type fields `SetAccount` and `SetChildren` enable you to pass in other proxies just as easily as primitive types.

## Generate `utils.go`
### When running `pocketbase-gogen generate` with the `--utils` flag you get `utils.go`
`utils.go` will be saved in the same package next to your output generated source code file.

It looks like this:
```go
type Proxy interface{ BankAccount | Child | Person }

// This interface constrains a type parameter of
// a Proxy core type into its pointer type.
type ProxyP[P Proxy] interface {
	*P
	core.RecordProxy
	CollectionName() string
}

// Returns the collection name of a proxy type
//
//	collectionName := CName[ProxyType]()
func CName[P Proxy, PP ProxyP[P]]() string {
	return PP.CollectionName(nil)
}

// Creates a new record and wraps it in a new proxy
//
//	proxy := NewProxy[ProxyType](app)
func NewProxy[P Proxy, PP ProxyP[P]](app core.App) (PP, error) {
	var p PP = &P{}
	collectionName := p.CollectionName()
	collection, err := app.FindCachedCollectionByNameOrId(collectionName)
	if err != nil {
		return nil, err
	}
	record := core.NewRecord(collection)
	p.SetProxyRecord(record)
	return p, nil
}

// Wraps a record in a newly created proxy
//
//	proxy := WrapRecord[ProxyType](record)
func WrapRecord[P Proxy, PP ProxyP[P]](record *core.Record) (PP, error) {
	collectionName := record.Collection().Name
	proxyCollectionName := PP.CollectionName(nil)
	if collectionName != proxyCollectionName {
		return nil, errors.New("the generic proxy type is not of the same collection as the given record")
	}
	var p PP = &P{}
	p.SetProxyRecord(record)
	return p, nil
}

type RelationField struct {
	FieldName string
	IsMulti   bool
}

// This map contains all relations between the collections that
// have a proxy struct with a CollectionName() method.
// It maps like this:
//
//	collection name
//	 -> collection names that it is related to
//	  -> list of fields that contain the relation values
var Relations = map[string]map[string][]RelationField{
	"person": {
		"bank_account": {
			{"account", false},
		},
		"child": {
			{"children", true},
		},
	},
}
```

- The util functions are documented with usage examples.
- The type contstraint interfaces `Proxy` and `ProxyP` can also be used outside the utils for generic parameters of proxy-handling functions.
- The `Relations` map is a helper for when you need to fetch related records to expand relations. It connects the names of relation type fields with the origin collection of the related records.

## Generate proxy hooks
### When running `pocketbase-gogen generate` with the `--hooks` flag you get `proxy_events.go` and `proxy_hooks.go`

This gives you access to the `NewProxyHooks(app core.App)` function. It returns a struct that has various hooks _per proxy type_.
In the example, `proxy_hooks.go` looks like this:

<details>

<summary>Click here to see the file contents</summary>

```go
type BankAccountEvent = ProxyRecordEvent[BankAccount, *BankAccount]
type BankAccountEnrichEvent = ProxyRecordEnrichEvent[BankAccount, *BankAccount]
type BankAccountErrorEvent = ProxyRecordErrorEvent[BankAccount, *BankAccount]
type BankAccountListRequestEvent = ProxyRecordsListRequestEvent[BankAccount, *BankAccount]
type BankAccountRequestEvent = ProxyRecordRequestEvent[BankAccount, *BankAccount]
type ChildEvent = ProxyRecordEvent[Child, *Child]
type ChildEnrichEvent = ProxyRecordEnrichEvent[Child, *Child]
type ChildErrorEvent = ProxyRecordErrorEvent[Child, *Child]
type ChildListRequestEvent = ProxyRecordsListRequestEvent[Child, *Child]
type ChildRequestEvent = ProxyRecordRequestEvent[Child, *Child]
type PersonEvent = ProxyRecordEvent[Person, *Person]
type PersonEnrichEvent = ProxyRecordEnrichEvent[Person, *Person]
type PersonErrorEvent = ProxyRecordErrorEvent[Person, *Person]
type PersonListRequestEvent = ProxyRecordsListRequestEvent[Person, *Person]
type PersonRequestEvent = ProxyRecordRequestEvent[Person, *Person]

// This struct is a container for all proxy hooks.
// Use NewProxyHooks(app core.App) to create it once.
type ProxyHooks struct {
	OnBankAccountEnrich             *hook.Hook[*BankAccountEnrichEvent]
	OnBankAccountValidate           *hook.Hook[*BankAccountEvent]
	OnBankAccountCreate             *hook.Hook[*BankAccountEvent]
	OnBankAccountCreateExecute      *hook.Hook[*BankAccountEvent]
	OnBankAccountAfterCreateSuccess *hook.Hook[*BankAccountEvent]
	OnBankAccountAfterCreateError   *hook.Hook[*BankAccountErrorEvent]
	OnBankAccountUpdate             *hook.Hook[*BankAccountEvent]
	OnBankAccountUpdateExecute      *hook.Hook[*BankAccountEvent]
	OnBankAccountAfterUpdateSuccess *hook.Hook[*BankAccountEvent]
	OnBankAccountAfterUpdateError   *hook.Hook[*BankAccountErrorEvent]
	OnBankAccountDelete             *hook.Hook[*BankAccountEvent]
	OnBankAccountDeleteExecute      *hook.Hook[*BankAccountEvent]
	OnBankAccountAfterDeleteSuccess *hook.Hook[*BankAccountEvent]
	OnBankAccountAfterDeleteError   *hook.Hook[*BankAccountErrorEvent]
	OnBankAccountListRequest        *hook.Hook[*BankAccountListRequestEvent]
	OnBankAccountViewRequest        *hook.Hook[*BankAccountRequestEvent]
	OnBankAccountCreateRequest      *hook.Hook[*BankAccountRequestEvent]
	OnBankAccountUpdateRequest      *hook.Hook[*BankAccountRequestEvent]
	OnBankAccountDeleteRequest      *hook.Hook[*BankAccountRequestEvent]
	OnChildEnrich                   *hook.Hook[*ChildEnrichEvent]
	OnChildValidate                 *hook.Hook[*ChildEvent]
	OnChildCreate                   *hook.Hook[*ChildEvent]
	OnChildCreateExecute            *hook.Hook[*ChildEvent]
	OnChildAfterCreateSuccess       *hook.Hook[*ChildEvent]
	OnChildAfterCreateError         *hook.Hook[*ChildErrorEvent]
	OnChildUpdate                   *hook.Hook[*ChildEvent]
	OnChildUpdateExecute            *hook.Hook[*ChildEvent]
	OnChildAfterUpdateSuccess       *hook.Hook[*ChildEvent]
	OnChildAfterUpdateError         *hook.Hook[*ChildErrorEvent]
	OnChildDelete                   *hook.Hook[*ChildEvent]
	OnChildDeleteExecute            *hook.Hook[*ChildEvent]
	OnChildAfterDeleteSuccess       *hook.Hook[*ChildEvent]
	OnChildAfterDeleteError         *hook.Hook[*ChildErrorEvent]
	OnChildListRequest              *hook.Hook[*ChildListRequestEvent]
	OnChildViewRequest              *hook.Hook[*ChildRequestEvent]
	OnChildCreateRequest            *hook.Hook[*ChildRequestEvent]
	OnChildUpdateRequest            *hook.Hook[*ChildRequestEvent]
	OnChildDeleteRequest            *hook.Hook[*ChildRequestEvent]
	OnPersonEnrich                  *hook.Hook[*PersonEnrichEvent]
	OnPersonValidate                *hook.Hook[*PersonEvent]
	OnPersonCreate                  *hook.Hook[*PersonEvent]
	OnPersonCreateExecute           *hook.Hook[*PersonEvent]
	OnPersonAfterCreateSuccess      *hook.Hook[*PersonEvent]
	OnPersonAfterCreateError        *hook.Hook[*PersonErrorEvent]
	OnPersonUpdate                  *hook.Hook[*PersonEvent]
	OnPersonUpdateExecute           *hook.Hook[*PersonEvent]
	OnPersonAfterUpdateSuccess      *hook.Hook[*PersonEvent]
	OnPersonAfterUpdateError        *hook.Hook[*PersonErrorEvent]
	OnPersonDelete                  *hook.Hook[*PersonEvent]
	OnPersonDeleteExecute           *hook.Hook[*PersonEvent]
	OnPersonAfterDeleteSuccess      *hook.Hook[*PersonEvent]
	OnPersonAfterDeleteError        *hook.Hook[*PersonErrorEvent]
	OnPersonListRequest             *hook.Hook[*PersonListRequestEvent]
	OnPersonViewRequest             *hook.Hook[*PersonRequestEvent]
	OnPersonCreateRequest           *hook.Hook[*PersonRequestEvent]
	OnPersonUpdateRequest           *hook.Hook[*PersonRequestEvent]
	OnPersonDeleteRequest           *hook.Hook[*PersonRequestEvent]
}

// Create a new set of proxy hooks and register them
// on the given app. Keep in mind that calling this
// multiple times will result in multiple duplicate
// hooks being registered. So in general that should be
// avoided.
//
// Usage with an exemplary User proxy that has a name field:
//
//	pHooks := NewProxyHooks(app)
//	pHooks.OnUserCreate.BindFunc(func(e *UserEvent) error {
//		var user *User = e.PRecord // <-- Proxy events contain the proxy in the PRecord field
//		fmt.Printf("Hello new user, %v!", user.Name())
//		return e.Next()
//	})
func NewProxyHooks(app core.App) *ProxyHooks {
	pHooks := &ProxyHooks{
		OnBankAccountEnrich:             &hook.Hook[*BankAccountEnrichEvent]{},
		OnBankAccountValidate:           &hook.Hook[*BankAccountEvent]{},
		OnBankAccountCreate:             &hook.Hook[*BankAccountEvent]{},
		OnBankAccountCreateExecute:      &hook.Hook[*BankAccountEvent]{},
		OnBankAccountAfterCreateSuccess: &hook.Hook[*BankAccountEvent]{},
		OnBankAccountAfterCreateError:   &hook.Hook[*BankAccountErrorEvent]{},
		OnBankAccountUpdate:             &hook.Hook[*BankAccountEvent]{},
		OnBankAccountUpdateExecute:      &hook.Hook[*BankAccountEvent]{},
		OnBankAccountAfterUpdateSuccess: &hook.Hook[*BankAccountEvent]{},
		OnBankAccountAfterUpdateError:   &hook.Hook[*BankAccountErrorEvent]{},
		OnBankAccountDelete:             &hook.Hook[*BankAccountEvent]{},
		OnBankAccountDeleteExecute:      &hook.Hook[*BankAccountEvent]{},
		OnBankAccountAfterDeleteSuccess: &hook.Hook[*BankAccountEvent]{},
		OnBankAccountAfterDeleteError:   &hook.Hook[*BankAccountErrorEvent]{},
		OnBankAccountListRequest:        &hook.Hook[*BankAccountListRequestEvent]{},
		OnBankAccountViewRequest:        &hook.Hook[*BankAccountRequestEvent]{},
		OnBankAccountCreateRequest:      &hook.Hook[*BankAccountRequestEvent]{},
		OnBankAccountUpdateRequest:      &hook.Hook[*BankAccountRequestEvent]{},
		OnBankAccountDeleteRequest:      &hook.Hook[*BankAccountRequestEvent]{},
		OnChildEnrich:                   &hook.Hook[*ChildEnrichEvent]{},
		OnChildValidate:                 &hook.Hook[*ChildEvent]{},
		OnChildCreate:                   &hook.Hook[*ChildEvent]{},
		OnChildCreateExecute:            &hook.Hook[*ChildEvent]{},
		OnChildAfterCreateSuccess:       &hook.Hook[*ChildEvent]{},
		OnChildAfterCreateError:         &hook.Hook[*ChildErrorEvent]{},
		OnChildUpdate:                   &hook.Hook[*ChildEvent]{},
		OnChildUpdateExecute:            &hook.Hook[*ChildEvent]{},
		OnChildAfterUpdateSuccess:       &hook.Hook[*ChildEvent]{},
		OnChildAfterUpdateError:         &hook.Hook[*ChildErrorEvent]{},
		OnChildDelete:                   &hook.Hook[*ChildEvent]{},
		OnChildDeleteExecute:            &hook.Hook[*ChildEvent]{},
		OnChildAfterDeleteSuccess:       &hook.Hook[*ChildEvent]{},
		OnChildAfterDeleteError:         &hook.Hook[*ChildErrorEvent]{},
		OnChildListRequest:              &hook.Hook[*ChildListRequestEvent]{},
		OnChildViewRequest:              &hook.Hook[*ChildRequestEvent]{},
		OnChildCreateRequest:            &hook.Hook[*ChildRequestEvent]{},
		OnChildUpdateRequest:            &hook.Hook[*ChildRequestEvent]{},
		OnChildDeleteRequest:            &hook.Hook[*ChildRequestEvent]{},
		OnPersonEnrich:                  &hook.Hook[*PersonEnrichEvent]{},
		OnPersonValidate:                &hook.Hook[*PersonEvent]{},
		OnPersonCreate:                  &hook.Hook[*PersonEvent]{},
		OnPersonCreateExecute:           &hook.Hook[*PersonEvent]{},
		OnPersonAfterCreateSuccess:      &hook.Hook[*PersonEvent]{},
		OnPersonAfterCreateError:        &hook.Hook[*PersonErrorEvent]{},
		OnPersonUpdate:                  &hook.Hook[*PersonEvent]{},
		OnPersonUpdateExecute:           &hook.Hook[*PersonEvent]{},
		OnPersonAfterUpdateSuccess:      &hook.Hook[*PersonEvent]{},
		OnPersonAfterUpdateError:        &hook.Hook[*PersonErrorEvent]{},
		OnPersonDelete:                  &hook.Hook[*PersonEvent]{},
		OnPersonDeleteExecute:           &hook.Hook[*PersonEvent]{},
		OnPersonAfterDeleteSuccess:      &hook.Hook[*PersonEvent]{},
		OnPersonAfterDeleteError:        &hook.Hook[*PersonErrorEvent]{},
		OnPersonListRequest:             &hook.Hook[*PersonListRequestEvent]{},
		OnPersonViewRequest:             &hook.Hook[*PersonRequestEvent]{},
		OnPersonCreateRequest:           &hook.Hook[*PersonRequestEvent]{},
		OnPersonUpdateRequest:           &hook.Hook[*PersonRequestEvent]{},
		OnPersonDeleteRequest:           &hook.Hook[*PersonRequestEvent]{},
	}
	pHooks.registerProxyHooks(app)
	return pHooks
}

func (pHooks *ProxyHooks) registerProxyHooks(app core.App) {
	registerProxyEnrichEventHook(app.OnRecordEnrich("bank_account"), pHooks.OnBankAccountEnrich)
	registerProxyEventHook(app.OnRecordValidate("bank_account"), pHooks.OnBankAccountValidate)
	registerProxyEventHook(app.OnRecordCreate("bank_account"), pHooks.OnBankAccountCreate)
	registerProxyEventHook(app.OnRecordCreateExecute("bank_account"), pHooks.OnBankAccountCreateExecute)
	registerProxyEventHook(app.OnRecordAfterCreateSuccess("bank_account"), pHooks.OnBankAccountAfterCreateSuccess)
	registerProxyErrorEventHook(app.OnRecordAfterCreateError("bank_account"), pHooks.OnBankAccountAfterCreateError)
	registerProxyEventHook(app.OnRecordUpdate("bank_account"), pHooks.OnBankAccountUpdate)
	registerProxyEventHook(app.OnRecordUpdateExecute("bank_account"), pHooks.OnBankAccountUpdateExecute)
	registerProxyEventHook(app.OnRecordAfterUpdateSuccess("bank_account"), pHooks.OnBankAccountAfterUpdateSuccess)
	registerProxyErrorEventHook(app.OnRecordAfterUpdateError("bank_account"), pHooks.OnBankAccountAfterUpdateError)
	registerProxyEventHook(app.OnRecordDelete("bank_account"), pHooks.OnBankAccountDelete)
	registerProxyEventHook(app.OnRecordDeleteExecute("bank_account"), pHooks.OnBankAccountDeleteExecute)
	registerProxyEventHook(app.OnRecordAfterDeleteSuccess("bank_account"), pHooks.OnBankAccountAfterDeleteSuccess)
	registerProxyErrorEventHook(app.OnRecordAfterDeleteError("bank_account"), pHooks.OnBankAccountAfterDeleteError)
	registerProxyListRequestEventHook(app.OnRecordsListRequest("bank_account"), pHooks.OnBankAccountListRequest)
	registerProxyRequestEventHook(app.OnRecordViewRequest("bank_account"), pHooks.OnBankAccountViewRequest)
	registerProxyRequestEventHook(app.OnRecordCreateRequest("bank_account"), pHooks.OnBankAccountCreateRequest)
	registerProxyRequestEventHook(app.OnRecordUpdateRequest("bank_account"), pHooks.OnBankAccountUpdateRequest)
	registerProxyRequestEventHook(app.OnRecordDeleteRequest("bank_account"), pHooks.OnBankAccountDeleteRequest)
	registerProxyEnrichEventHook(app.OnRecordEnrich("child"), pHooks.OnChildEnrich)
	registerProxyEventHook(app.OnRecordValidate("child"), pHooks.OnChildValidate)
	registerProxyEventHook(app.OnRecordCreate("child"), pHooks.OnChildCreate)
	registerProxyEventHook(app.OnRecordCreateExecute("child"), pHooks.OnChildCreateExecute)
	registerProxyEventHook(app.OnRecordAfterCreateSuccess("child"), pHooks.OnChildAfterCreateSuccess)
	registerProxyErrorEventHook(app.OnRecordAfterCreateError("child"), pHooks.OnChildAfterCreateError)
	registerProxyEventHook(app.OnRecordUpdate("child"), pHooks.OnChildUpdate)
	registerProxyEventHook(app.OnRecordUpdateExecute("child"), pHooks.OnChildUpdateExecute)
	registerProxyEventHook(app.OnRecordAfterUpdateSuccess("child"), pHooks.OnChildAfterUpdateSuccess)
	registerProxyErrorEventHook(app.OnRecordAfterUpdateError("child"), pHooks.OnChildAfterUpdateError)
	registerProxyEventHook(app.OnRecordDelete("child"), pHooks.OnChildDelete)
	registerProxyEventHook(app.OnRecordDeleteExecute("child"), pHooks.OnChildDeleteExecute)
	registerProxyEventHook(app.OnRecordAfterDeleteSuccess("child"), pHooks.OnChildAfterDeleteSuccess)
	registerProxyErrorEventHook(app.OnRecordAfterDeleteError("child"), pHooks.OnChildAfterDeleteError)
	registerProxyListRequestEventHook(app.OnRecordsListRequest("child"), pHooks.OnChildListRequest)
	registerProxyRequestEventHook(app.OnRecordViewRequest("child"), pHooks.OnChildViewRequest)
	registerProxyRequestEventHook(app.OnRecordCreateRequest("child"), pHooks.OnChildCreateRequest)
	registerProxyRequestEventHook(app.OnRecordUpdateRequest("child"), pHooks.OnChildUpdateRequest)
	registerProxyRequestEventHook(app.OnRecordDeleteRequest("child"), pHooks.OnChildDeleteRequest)
	registerProxyEnrichEventHook(app.OnRecordEnrich("person"), pHooks.OnPersonEnrich)
	registerProxyEventHook(app.OnRecordValidate("person"), pHooks.OnPersonValidate)
	registerProxyEventHook(app.OnRecordCreate("person"), pHooks.OnPersonCreate)
	registerProxyEventHook(app.OnRecordCreateExecute("person"), pHooks.OnPersonCreateExecute)
	registerProxyEventHook(app.OnRecordAfterCreateSuccess("person"), pHooks.OnPersonAfterCreateSuccess)
	registerProxyErrorEventHook(app.OnRecordAfterCreateError("person"), pHooks.OnPersonAfterCreateError)
	registerProxyEventHook(app.OnRecordUpdate("person"), pHooks.OnPersonUpdate)
	registerProxyEventHook(app.OnRecordUpdateExecute("person"), pHooks.OnPersonUpdateExecute)
	registerProxyEventHook(app.OnRecordAfterUpdateSuccess("person"), pHooks.OnPersonAfterUpdateSuccess)
	registerProxyErrorEventHook(app.OnRecordAfterUpdateError("person"), pHooks.OnPersonAfterUpdateError)
	registerProxyEventHook(app.OnRecordDelete("person"), pHooks.OnPersonDelete)
	registerProxyEventHook(app.OnRecordDeleteExecute("person"), pHooks.OnPersonDeleteExecute)
	registerProxyEventHook(app.OnRecordAfterDeleteSuccess("person"), pHooks.OnPersonAfterDeleteSuccess)
	registerProxyErrorEventHook(app.OnRecordAfterDeleteError("person"), pHooks.OnPersonAfterDeleteError)
	registerProxyListRequestEventHook(app.OnRecordsListRequest("person"), pHooks.OnPersonListRequest)
	registerProxyRequestEventHook(app.OnRecordViewRequest("person"), pHooks.OnPersonViewRequest)
	registerProxyRequestEventHook(app.OnRecordCreateRequest("person"), pHooks.OnPersonCreateRequest)
	registerProxyRequestEventHook(app.OnRecordUpdateRequest("person"), pHooks.OnPersonUpdateRequest)
	registerProxyRequestEventHook(app.OnRecordDeleteRequest("person"), pHooks.OnPersonDeleteRequest)
}
```

</details>

### Here's an example on how to use the proxy hooks

```go
pHooks := NewProxyHooks(app)

pHooks.OnPersonCreate(func(e *PersonEvent) error {
	var *Person person = e.PRecord // The event carries a proxy of the changed record
	fmt.Printf("Hello new person, %v!", person.Name())
	return e.Next()
})
```

The following PocketBase hooks will be generated as proxy hooks:

 - `OnRecordEnrich`
 - `OnRecordValidate`
 - `OnRecordCreate`
 - `OnRecordCreateExecute`
 - `OnRecordAfterCreateSuccess`
 - `OnRecordAfterCreateError`
 - `OnRecordCreateRequest`
 - `OnRecordUpdate`
 - `OnRecordUpdateExecute`
 - `OnRecordAfterUpdateSuccess`
 - `OnRecordAfterUpdateError`
 - `OnRecordUpdateRequest`
 - `OnRecordDelete`
 - `OnRecordDeleteExecute`
 - `OnRecordAfterDeleteSuccess`
 - `OnRecordAfterDeleteError`
 - `OnRecordDeleteRequest`
 - `OnRecordsListRequest`
 - `OnRecordViewRequest`
 
Each of these hooks gets generated for every proxy type.
The corresponding proxy hooks are named by replacing "`Record`" with the proxy struct name (e.g. `OnPersonCreate`).

## Custom Methods
### `pocketbase-gogen` also converts methods that you manually add to your template

 > [!IMPORTANT]  
> As said before, always test your generated code especially with custom methods.

For example:

```go
func (a *BankAccount) Withdraw(amount int) {
	newAmount := a.money - amount
	if newAmount < 0 {
		fmt.Println("You are out of money!")
		return
	}
	a.money = newAmount
}
```

Will generate this:

```go
func (a *BankAccount) Withdraw(amount int) {
	newAmount := a.Money() - amount
	if newAmount < 0 {
		fmt.Println("You are out of money!")
		return
	}
	a.SetMoney(newAmount)
}
```

As you can see, the generator replaced all template field accessors with the appropriate getters and setters so you use the method for editing your data.

A few more examples:

<table align="center" width="100%">
<tr>
<th> Template</th>
<th> Generated</code></th>
</tr>
<tr>
<td>

```go
func (a *BankAccount) Deposit(amount int) {
	a.money += amount
}
```

</td>
<td>

```go
func (a *BankAccount) Deposit(amount int) {
	a.SetMoney(a.Money() + amount)
}
```

</td>
</tr>
</table>

<table align="center" width="100%">
<tr>
<th> Template</th>
<th> Generated</code></th>
</tr>
<tr>
<td>

```go
// Doctor approved logic
func (p *Person) UpdateHealth() {
	if len(p.children) <= 2 {
		p.health = 0
	} else if len(p.children) <= 4 {
		p.health = 1
	} else {
		p.health = 2
	}
}
```

</td>
<td>

```go
// Doctor approved logic
func (p *Person) UpdateHealth() {
	if len(p.Children()) <= 2 {
		p.SetHealth(HealthSelectType(0))
	} else if len(p.Children()) <= 4 {
		p.SetHealth(HealthSelectType(1))
	} else {
		p.SetHealth(HealthSelectType(2))
	}
}
```

</td>
</tr>
</table>

<table align="center" width="100%">
<tr>
<th> Template</th>
<th> Generated</code></th>
</tr>
<tr>
<td>

```go
func (p *Person) BearChild(child *Child) {
	p.children = append(p.children, child)
}
```

</td>
<td>

```go
func (p *Person) BearChild(child *Child) {
	p.SetChildren(append(p.Children(), child))
}
```

</td>
</tr>
</table>

<table align="center" width="100%">
<tr>
<th> Template</th>
<th> Generated</code></th>
</tr>
<tr>
<td>

```go
func (p *Person) SwitchMyLifeUp() {
	p.name, p.address = p.address, p.name
	p.account.Withdraw(999999)
	p.children = []*Child{}
}
```

</td>
<td>

```go
func (p *Person) SwitchMyLifeUp() {
	name, address := p.Address(), p.Name()
	p.SetAddress(address)
	p.SetName(name)
	p.Account().Withdraw(999999)
	p.SetChildren([]*Child{})
}
```

</td>
</tr>
</table>

## Details

- The generator protects you from accidentially shadowing any names from the `core.Record` struct which could compromise your data in obscure ways.
  For example you can't define `func (p *Person) Id()`. The generator will error.
- There is no support for creating new records from inside of custom template methods.
- When using out-of-bounds indices for select types the getters/setters will panic.
- You can access most system fields in custom methods because they have their getters/setters directly in `core.Record`. Double check what you are doing with those.
- You can rename almost everything in the template. The comment at the top of the template file has instructions for that.
- The `pocketbase-gogen` command needs access to go module imports that you are using (mostly the PocketBase module). Best run it from inside your project directory.
- If you have reserved go keywords (e.g. `func`) as field names in your PB schema, the generator will escape them using a trailing underscore (`func_`).
- When you delete the `// collection-name:` comment from a template struct, the `CollectionName()` method will not be generated and because of that the proxy type will not work with the functions from `utils.go`. It will also not get proxy hooks generated when using `--hooks`. The generator will warn of the missing comment.
