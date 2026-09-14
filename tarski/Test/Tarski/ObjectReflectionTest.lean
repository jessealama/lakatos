import Tarski.Eval
import Tarski.Format

/-! The `Object` reflection surface and the property-write rules.

`Test/Tarski/DescriptorTest.lean` checks 10.1.6.3's table as a pure
function; this checks the built-ins that reach it and the refusals they
turn into `TypeError`s — which is the half of the property protocol a
script can see.

The acceptance criterion the issue asks for is here: own-key order,
enumerability, and the strict-mode refusal a non-writable property gives
a write. -/

open Tarski

/-- What the binary would print, so a case reads as its own stdout. -/
private def outcome (p : Program) : String :=
  match runScript p with
  | none => "<diverges>"
  | some (.error (.throw v), h) => s!"uncaught: {describeThrown h v}"
  | some (.error _, _) => "<abrupt>"
  | some (.ok none, _) => "<empty>"
  | some (.ok (some v), _) => formatValue v

/-- A program that is one expression. -/
private def expr (e : Expr) : Program := [.exprStmt e]

/-- `Object.<name>(<args>)`. -/
private def obj (name : String) (args : List Expr) : Expr :=
  .call (.member (.ident "Object") name) args

/-- `<e>.join()`, which is how a list of keys reads as a string. -/
private def joined (e : Expr) : Expr := .call (.member e "join") []

/-- `const <n> = <e>;` -/
private def «let» (n : String) (e : Expr) : Stmt :=
  .varDecl .«const» [{ name := n, init := some e }]

/-- An object literal with no members, which every case starts from. -/
private def empty : Expr := .objectLit []

/-- `{ value: <v>, writable: <w>, enumerable: <e>, configurable: <c> }`. -/
private def dataDesc (v : Expr) (w e c : Bool) : Expr :=
  .objectLit [("value", v), ("writable", .boolLit w),
              ("enumerable", .boolLit e), ("configurable", .boolLit c)]

/-- `function () { return <e>; }`, an anonymous getter. -/
private def getterOf (e : Expr) : Expr := .funcExpr none [] [.returnStmt (some e)]

/-! ## `Object.defineProperty`

The issue's own half: a non-writable, non-enumerable, non-configurable
property refuses a strict-mode write, reads back as its descriptor, and
is not among `Object.keys`. -/

-- `const o = {}; Object.defineProperty(o, "x", {value: 1, ...}); o.x;`
private def defineX (rest : List Stmt) : Program :=
  «let» "o" empty ::
    .exprStmt (obj "defineProperty"
      [.ident "o", .strLit "x", dataDesc (.numLit 1.0) false false false]) :: rest

#guard outcome (defineX [.exprStmt (.member (.ident "o") "x")]) == "1"
#guard outcome (defineX [.exprStmt (.assign (.member (.ident "o") "x") (.numLit 2.0))])
  == "uncaught: TypeError: Cannot assign to read only property 'x' of object '#<Object>'"
#guard outcome (defineX [.exprStmt (joined (obj "keys" [.ident "o"]))]) == ""
#guard outcome (defineX
    [.exprStmt (.member (obj "getOwnPropertyDescriptor" [.ident "o", .strLit "x"]) "writable")])
  == "false"

-- A descriptor object's own keys are the specification's order.
#guard outcome (defineX
    [.exprStmt (joined (obj "keys" [obj "getOwnPropertyDescriptor" [.ident "o", .strLit "x"]]))])
  == "value,writable,enumerable,configurable"
#guard outcome
    [ «let» "o" empty,
      .exprStmt (obj "defineProperty"
        [.ident "o", .strLit "x", .objectLit [("get", getterOf (.numLit 1.0))]]),
      .exprStmt (joined (obj "keys"
        [obj "getOwnPropertyDescriptor" [.ident "o", .strLit "x"]])) ]
  == "get,set,enumerable,configurable"

-- A key that is not there has no descriptor at all.
#guard outcome (expr (obj "getOwnPropertyDescriptor" [empty, .strLit "x"])) == "undefined"

-- Redefining a non-configurable property is the other refusal.
#guard outcome (defineX
    [.exprStmt (obj "defineProperty"
      [.ident "o", .strLit "x", dataDesc (.numLit 2.0) false false false])])
  == "uncaught: TypeError: Cannot redefine property: x"

-- The argument checks, in the order 20.1.2.4 makes them.
#guard outcome (expr (obj "defineProperty" [.numLit 1.0, .strLit "x", empty]))
  == "uncaught: TypeError: Object.defineProperty called on non-object"
#guard outcome (expr (obj "defineProperty" [empty, .strLit "x", .numLit 1.0]))
  == "uncaught: TypeError: Property description must be an object: 1"
#guard outcome (expr (obj "defineProperty"
    [empty, .strLit "x", .objectLit [("value", .numLit 1.0), ("get", getterOf (.numLit 1.0))]]))
  == ("uncaught: TypeError: Invalid property descriptor. Cannot both specify accessors " ++
      "and a value or writable attribute")
#guard outcome (expr (obj "defineProperty"
    [empty, .strLit "x", .objectLit [("get", .numLit 1.0)]]))
  == "uncaught: TypeError: Getter must be a function: 1"
#guard outcome (expr (obj "defineProperty"
    [empty, .strLit "x", .objectLit [("set", .numLit 1.0)]]))
  == "uncaught: TypeError: Setter must be a function: 1"

-- An accessor defined by descriptor is read through and written
-- through; a getter with no setter refuses a write.
#guard outcome
    [ «let» "o" empty,
      .exprStmt (obj "defineProperty"
        [.ident "o", .strLit "x", .objectLit [("get", getterOf (.numLit 7.0))]]),
      .exprStmt (.member (.ident "o") "x") ]
  == "7"
#guard outcome
    [ «let» "o" empty,
      .exprStmt (obj "defineProperty"
        [.ident "o", .strLit "x", .objectLit [("get", getterOf (.numLit 7.0))]]),
      .exprStmt (.assign (.member (.ident "o") "x") (.numLit 1.0)) ]
  == "uncaught: TypeError: Cannot set property x of #<Object> which has only a getter"

/-! ## An array's `length` through `defineProperty`

ArraySetLength in its descriptor form: the length shortens, and once it
is non-writable a growing write refuses. -/

/-- `[1, 2, 3]`. -/
private def three : Expr := .arrayLit [.numLit 1.0, .numLit 2.0, .numLit 3.0]

#guard outcome
    [ «let» "xs" three,
      .exprStmt (obj "defineProperty"
        [.ident "xs", .strLit "length", .objectLit [("value", .numLit 1.0)]]),
      .exprStmt (joined (.ident "xs")) ]
  == "1"

#guard outcome
    [ «let» "xs" (.arrayLit [.numLit 1.0]),
      .exprStmt (obj "defineProperty"
        [.ident "xs", .strLit "length", .objectLit [("writable", .boolLit false)]]),
      .exprStmt (.call (.member (.ident "xs") "push") [.numLit 2.0]) ]
  == "uncaught: TypeError: Cannot assign to read only property 'length' of object '#<Object>'"

-- A non-configurable element stops the truncation at its index, and the
-- length that was actually reached is the one written.
#guard outcome
    [ «let» "xs" three,
      .exprStmt (obj "defineProperty"
        [.ident "xs", .strLit "1", dataDesc (.numLit 2.0) true true false]),
      .exprStmt (.assign (.member (.ident "xs") "length") (.numLit 0.0)) ]
  == "uncaught: TypeError: Cannot assign to read only property 'length' of object '#<Object>'"
#guard outcome
    [ «let» "xs" three,
      .exprStmt (obj "defineProperty"
        [.ident "xs", .strLit "1", dataDesc (.numLit 2.0) true true false]),
      .tryStmt [.exprStmt (.assign (.member (.ident "xs") "length") (.numLit 0.0))]
        (some { param := none, body := [] }) none,
      .exprStmt (.member (.ident "xs") "length") ]
  == "2"

-- An array's `length` has a descriptor of its own, read out of the kind.
#guard outcome (expr (joined (obj "keys"
    [obj "getOwnPropertyDescriptor" [.arrayLit [], .strLit "length"]])))
  == "value,writable,enumerable,configurable"

/-! ## `Object.defineProperties`

Every descriptor is read before any is applied, so a descriptor object
whose read throws leaves nothing defined. -/

#guard outcome
    [ «let» "o" empty,
      .exprStmt (obj "defineProperties"
        [.ident "o", .objectLit
          [ ("a", .objectLit [("value", .numLit 1.0), ("enumerable", .boolLit true)]),
            ("b", .objectLit [("value", .numLit 2.0), ("enumerable", .boolLit true)]) ]]),
      .exprStmt (joined (obj "keys" [.ident "o"])) ]
  == "a,b"

#guard outcome
    [ «let» "o" empty,
      .tryStmt
        [.exprStmt (obj "defineProperties"
          [.ident "o", .objectLit
            [ ("a", .objectLit [("value", .numLit 1.0), ("enumerable", .boolLit true)]),
              ("b", .numLit 1.0) ]])]
        (some { param := none, body := [] }) none,
      .exprStmt (joined (obj "keys" [.ident "o"])) ]
  == ""

/-! ## Own-key order — the issue's acceptance criterion

OrdinaryOwnPropertyKeys: index keys ascending, then the rest in
insertion order, accessor properties among them rather than after them.
The literal is built by assignment because a numeric key in an object
literal is #395's. -/

#guard outcome
    [ «let» "o" empty,
      .exprStmt (.assign (.member (.ident "o") "b") (.numLit 1.0)),
      .exprStmt (.assign (.index (.ident "o") (.numLit 2.0)) (.numLit 1.0)),
      .exprStmt (.assign (.member (.ident "o") "a") (.numLit 1.0)),
      .exprStmt (.assign (.index (.ident "o") (.numLit 1.0)) (.numLit 1.0)),
      .exprStmt (obj "defineProperty"
        [.ident "o", .strLit "c", .objectLit [("get", .funcExpr none [] [])]]),
      .exprStmt (joined (obj "getOwnPropertyNames" [.ident "o"])) ]
  == "1,2,b,a,c"

-- A function's three own properties, in the order the specification
-- creates them; an array's `length` after its indices; a class's static
-- field after the three.
#guard outcome (expr (joined (obj "getOwnPropertyNames" [.funcExpr none ["a"] []])))
  == "length,name,prototype"
#guard outcome (expr (joined (obj "getOwnPropertyNames" [.arrayLit [.numLit 1.0]])))
  == "0,length"
#guard outcome
    [ .classDecl "A"
        { name := some "A", superClass := none,
          elements := [.field true (.«public» "s") (some (.numLit 1.0))] },
      .exprStmt (joined (obj "getOwnPropertyNames" [.ident "A"])) ]
  == "length,name,prototype,s"

/-! ## Enumerability

`Object.keys`, `values`, and `entries` see the enumerable own keys and
nothing else, which is what hides a function's `prototype`, an error's
`message`, and a class's methods. -/

#guard outcome (expr (joined (obj "keys" [.funcExpr (some "f") [] []]))) == ""
#guard outcome (expr (joined (obj "keys" [.new (.ident "Error") [.strLit "m"]]))) == ""
#guard outcome (expr (joined (obj "values" [.objectLit
    [("a", .numLit 1.0), ("b", .numLit 2.0)]])))
  == "1,2"

-- EnumerableOwnProperties re-reads each own property before taking its
-- value, so a getter that deletes a later key is observed.
#guard outcome
    [ «let» "o" empty,
      .exprStmt (obj "defineProperty"
        [.ident "o", .strLit "a", .objectLit
          [ ("get", .funcExpr none []
              [.exprStmt (.delete (.member (.ident "o") "b")), .returnStmt (some (.numLit 1.0))]),
            ("enumerable", .boolLit true) ]]),
      .exprStmt (.assign (.member (.ident "o") "b") (.numLit 2.0)),
      .exprStmt (joined (obj "values" [.ident "o"])) ]
  == "1"

/-! ## `Object.assign`

`Get` on the source and `Set` on the target, so a getter and a setter
both run and a non-writable target key refuses. A nullish source is
skipped. -/

#guard outcome (expr (.member (obj "assign" [empty, .objectLit [("a", .numLit 1.0)], .nullLit])
    "a"))
  == "1"
#guard outcome (defineX [.exprStmt (obj "assign" [.ident "o", .objectLit [("x", .numLit 2.0)]])])
  == "uncaught: TypeError: Cannot assign to read only property 'x' of object '#<Object>'"

/-! ## `Object.create`, `getPrototypeOf`, and `setPrototypeOf` -/

#guard outcome (expr (.member (obj "create" [.nullLit]) "toString")) == "undefined"
#guard outcome
    (expr (.member (obj "create"
      [.nullLit, .objectLit [("a", .objectLit [("value", .numLit 1.0)])]]) "a"))
  == "1"
#guard outcome (expr (obj "create" [.numLit 1.0]))
  == "uncaught: TypeError: Object prototype may only be an Object or null: 1"

#guard outcome (expr (.binary .strictEq (obj "getPrototypeOf" [.funcExpr none [] []])
    (.member (.ident "Function") "prototype")))
  == "true"
#guard outcome (expr (.binary .strictEq (obj "getPrototypeOf" [.numLit 1.0])
    (.member (.ident "Number") "prototype")))
  == "true"
#guard outcome (expr (obj "getPrototypeOf" [obj "create" [.nullLit]])) == "null"

-- `setPrototypeOf` answers its first argument, refuses a cycle and a
-- non-extensible object, and takes a primitive without writing anything.
#guard outcome (expr (.binary .strictEq (obj "setPrototypeOf" [.numLit 1.0, .nullLit])
    (.numLit 1.0)))
  == "true"
#guard outcome
    [ «let» "o" empty,
      .exprStmt (obj "setPrototypeOf" [.ident "o", .ident "o"]) ]
  == "uncaught: TypeError: Cyclic __proto__ value"
#guard outcome
    [ «let» "o" empty, «let» "p" empty,
      .exprStmt (obj "setPrototypeOf" [.ident "o", .ident "p"]),
      .exprStmt (obj "setPrototypeOf" [.ident "p", .ident "o"]) ]
  == "uncaught: TypeError: Cyclic __proto__ value"
#guard outcome (expr (obj "setPrototypeOf" [obj "preventExtensions" [empty], .nullLit]))
  == "uncaught: TypeError: #<Object> is not extensible"
#guard outcome (expr (obj "setPrototypeOf" [.undefLit, .nullLit]))
  == "uncaught: TypeError: Object.setPrototypeOf called on null or undefined"

-- A changed prototype is what a read then walks.
#guard outcome
    [ «let» "o" empty,
      .exprStmt (obj "setPrototypeOf"
        [.ident "o", .objectLit [("a", .numLit 5.0)]]),
      .exprStmt (.member (.ident "o") "a") ]
  == "5"

/-! ## `freeze`, `seal`, `preventExtensions`, and their predicates

A primitive is frozen, sealed, and not extensible: it has no properties
to be otherwise about. -/

#guard outcome (expr (obj "isFrozen" [empty])) == "false"
#guard outcome (expr (obj "isFrozen" [obj "preventExtensions" [empty]])) == "true"
#guard outcome (expr (obj "isFrozen" [.numLit 1.0])) == "true"
#guard outcome (expr (obj "isExtensible" [.numLit 1.0])) == "false"
#guard outcome (expr (obj "isExtensible" [empty])) == "true"
#guard outcome (expr (obj "isSealed" [obj "seal" [.objectLit [("a", .numLit 1.0)]]])) == "true"
#guard outcome (expr (obj "isFrozen" [obj "seal" [.objectLit [("a", .numLit 1.0)]]])) == "false"
#guard outcome (expr (obj "isFrozen" [obj "freeze" [.arrayLit [.numLit 1.0]]])) == "true"

#guard outcome
    [ «let» "o" (obj "freeze" [.arrayLit [.numLit 1.0]]),
      .exprStmt (.assign (.member (.ident "o") "length") (.numLit 0.0)) ]
  == "uncaught: TypeError: Cannot assign to read only property 'length' of object '#<Object>'"

-- A sealed object still takes writes to the keys it has, and refuses
-- both a new key and a `delete`.
#guard outcome
    [ «let» "o" (obj "seal" [.objectLit [("a", .numLit 1.0)]]),
      .exprStmt (.assign (.member (.ident "o") "a") (.numLit 2.0)),
      .exprStmt (.member (.ident "o") "a") ]
  == "2"
#guard outcome
    [ «let» "o" (obj "seal" [.objectLit [("a", .numLit 1.0)]]),
      .exprStmt (.delete (.member (.ident "o") "a")) ]
  == "uncaught: TypeError: Cannot delete property 'a' of #<Object>"
#guard outcome
    [ «let» "o" (obj "preventExtensions" [empty]),
      .exprStmt (.assign (.member (.ident "o") "a") (.numLit 1.0)) ]
  == "uncaught: TypeError: Cannot add property a, object is not extensible"

/-! ## `Object.hasOwn` and `getOwnPropertyDescriptors` -/

#guard outcome (expr (obj "hasOwn" [.objectLit [("a", .numLit 1.0)], .strLit "a"])) == "true"
#guard outcome (expr (obj "hasOwn" [empty, .strLit "toString"])) == "false"
#guard outcome (expr (joined (obj "keys"
    [obj "getOwnPropertyDescriptors" [.objectLit [("a", .numLit 1.0)]]])))
  == "a"

/-! ## `Object.prototype`'s own methods -/

/-- `Object.prototype.<name>.call(<args>)`. -/
private def protoCall (name : String) (args : List Expr) : Expr :=
  .call (.member (.member (.member (.ident "Object") "prototype") name) "call") args

#guard outcome (expr (protoCall "toString" [.undefLit])) == "[object Undefined]"
#guard outcome (expr (protoCall "toString" [.nullLit])) == "[object Null]"
#guard outcome (expr (protoCall "toString" [.arrayLit []])) == "[object Array]"
#guard outcome (expr (protoCall "toString" [.funcExpr none [] []])) == "[object Function]"
#guard outcome (expr (protoCall "toString" [.new (.ident "Error") []])) == "[object Error]"
#guard outcome (expr (protoCall "toString" [.new (.ident "Number") [.numLit 1.0]]))
  == "[object Number]"
#guard outcome (expr (protoCall "toString" [.boolLit true])) == "[object Boolean]"
#guard outcome (expr (protoCall "toString" [empty])) == "[object Object]"
#guard outcome (expr (protoCall "toString"
    [.classExpr { name := some "A", superClass := none, elements := [] }]))
  == "[object Function]"

-- `valueOf` is ToObject, so a Number receiver answers a wrapper object
-- rather than the primitive.
#guard outcome (expr (.unary .typeof (protoCall "valueOf" [.numLit 1.0]))) == "object"
#guard outcome (expr (.call (.member (protoCall "valueOf" [.numLit 1.0]) "valueOf") []))
  == "1"

#guard outcome (expr (.call (.member (.member (.ident "Object") "prototype") "isPrototypeOf")
    [empty]))
  == "true"
#guard outcome (expr (.call (.member (.member (.ident "Object") "prototype") "isPrototypeOf")
    [.numLit 1.0]))
  == "false"
#guard outcome (expr (.call (.member (.arrayLit [.numLit 1.0]) "propertyIsEnumerable")
    [.strLit "length"]))
  == "false"
#guard outcome (expr (.call (.member (.arrayLit [.numLit 1.0]) "propertyIsEnumerable")
    [.strLit "0"]))
  == "true"
-- `toLocaleString` is Invoke(this, "toString"), so a `toString` of one's
-- own is what runs.
#guard outcome (expr (.call (.member (.objectLit
    [("toString", .funcExpr none [] [.returnStmt (some (.strLit "t"))])]) "toLocaleString") []))
  == "t"

/-! ## The write rules on the prototype chain

OrdinarySet reads the first own property on the chain, so an inherited
non-writable data property refuses a write on the instance. -/

#guard outcome
    [ «let» "p" empty,
      .exprStmt (obj "defineProperty"
        [.ident "p", .strLit "x", dataDesc (.numLit 1.0) false false false]),
      «let» "o" (obj "create" [.ident "p"]),
      .exprStmt (.assign (.member (.ident "o") "x") (.numLit 2.0)) ]
  == "uncaught: TypeError: Cannot assign to read only property 'x' of object '#<Object>'"

-- `Math.PI` is a non-writable property of an ordinary object, so the
-- same refusal reaches an intrinsic.
#guard outcome (expr (.assign (.member (.ident "Math") "PI") (.numLit 1.0)))
  == "uncaught: TypeError: Cannot assign to read only property 'PI' of object '#<Object>'"

-- `NaN` is still a cell, not a property, so it keeps the message an
-- assignment to a `const` gets. #487 makes it a global-object property.
#guard outcome (expr (.assign (.ident "NaN") (.numLit 1.0)))
  == "uncaught: TypeError: Assignment to constant variable."
