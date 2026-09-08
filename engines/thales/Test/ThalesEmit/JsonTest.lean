import ThalesEmit

/-! The emission JSON decodes strictly: a schema violation names the
offender, never a default. -/

open Lean ThalesEmit

/-- A number parameter as the wire spells it. -/
def numParamJson (name : String) : Json :=
  Json.mkObj [("name", name), ("type", "number")]

-- Schema violations decode to errors naming the offender, never to
-- defaults.
#guard (decodeEmission (Json.mkObj [])) matches .error _
#guard
  (decodeEmission (Json.mkObj
    [("file", "t.ts"), ("declarations", Json.arr #[Json.mkObj [("kind", "enum")]]),
     ("obligations", Json.arr #[])]))
  matches .error "unknown declaration kind 'enum'"
-- A known kind is still decoded strictly: a class missing its name is a
-- field error, not a default.
#guard
  (decodeEmission (Json.mkObj
    [("file", "t.ts"), ("declarations", Json.arr #[Json.mkObj [("kind", "class")]]),
     ("obligations", Json.arr #[])]))
  matches .error "property not found: name"

-- The unary-operator and binder-domain IR decodes strictly.
#guard
  (decodeExpr (Json.mkObj
    [("kind", "unop"), ("op", "-"), ("operand", Json.mkObj [("kind", "id"), ("name", "x")])]))
  matches .ok (.unop "-" (.id "x"))
#guard
  (decodeExpr (Json.mkObj
    [("kind", "same-value"),
     ("left", Json.mkObj [("kind", "id"), ("name", "x")]),
     ("right", Json.mkObj [("kind", "num"), ("lit", "-0")])]))
  matches .ok (.sameValue (.id "x") (.num "-0"))
#guard
  (decodeExpr (Json.mkObj
    [("kind", "cond"),
     ("cond", Json.mkObj [("kind", "id"), ("name", "b")]),
     ("then", Json.mkObj [("kind", "num"), ("lit", "0")]),
     ("else", Json.mkObj [("kind", "id"), ("name", "x")])]))
  matches .ok (.cond (.id "b") (.num "0") (.id "x"))
-- A builtin member call decodes by the object and member it names; the
-- renderer decides what the pair means.
#guard
  (decodeExpr (Json.mkObj
    [("kind", "builtin"), ("object", "Math"), ("member", "trunc"),
     ("args", Json.arr #[Json.mkObj [("kind", "id"), ("name", "x")]])]))
  matches .ok (.builtin "Math" "trunc" #[.id "x"])
#guard
  (decodeExpr (Json.mkObj
    [("kind", "builtin"), ("object", "Number"), ("member", "isNaN"),
     ("args", Json.arr #[Json.mkObj [("kind", "id"), ("name", "x")]])]))
  matches .ok (.builtin "Number" "isNaN" #[.id "x"])
#guard
  (decodeExpr (Json.mkObj
    [("kind", "builtin"), ("object", "Math"), ("member", "trunc")]))
  matches .error _
-- The class IR: instance construction, member reads, the receiver, and
-- a constructor's field assignment.
#guard
  (decodeExpr (Json.mkObj
    [("kind", "new"), ("className", "Box"),
     ("args", Json.arr #[Json.mkObj [("kind", "id"), ("name", "x")]])]))
  matches .ok (.newObj "Box" none #[.id "x"])
#guard
  (decodeExpr (Json.mkObj
    [("kind", "getter-read"), ("className", "Box"), ("name", "v"),
     ("object", Json.mkObj [("kind", "self")])]))
  matches .ok (.getterRead "Box" none "v" .selfRef)
#guard
  (decodeExpr (Json.mkObj
    [("kind", "field-read"), ("className", "Box"), ("field", "#v"),
     ("object", Json.mkObj [("kind", "self")])]))
  matches .ok (.fieldRead "Box" none "#v" .selfRef)
#guard
  (decodeExpr (Json.mkObj
    [("kind", "method-call"), ("className", "Box"), ("name", "double"),
     ("object", Json.mkObj [("kind", "self")]),
     ("args", Json.arr #[Json.mkObj [("kind", "id"), ("name", "y")]])]))
  matches .ok (.methodCall "Box" none "double" .selfRef #[.id "y"])
#guard
  (decodeStmt (Json.mkObj
    [("kind", "field-set"), ("field", "#v"),
     ("expr", Json.mkObj [("kind", "id"), ("name", "v")])]))
  matches .ok (.fieldSet "#v" (.id "v"))
#guard
  (decodeDecl (Json.mkObj
    [("kind", "class"), ("name", "Box"), ("source", "class Box {}"),
     ("fields", Json.arr #["#v"]),
     ("ctor", Json.mkObj
       [("params", Json.arr #[numParamJson "v"]),
        ("body", Json.arr #[Json.mkObj
          [("kind", "field-set"), ("field", "#v"),
           ("expr", Json.mkObj [("kind", "id"), ("name", "v")])]])]),
     ("getters", Json.arr #[Json.mkObj
       [("name", "v"),
        ("body", Json.arr #[Json.mkObj
          [("kind", "return"),
           ("expr", Json.mkObj
             [("kind", "field-read"), ("className", "Box"), ("field", "#v"),
              ("object", Json.mkObj [("kind", "self")])])]])]]),
     ("methods", Json.arr #[Json.mkObj
       [("name", "scale"), ("params", Json.arr #[numParamJson "k"]),
        ("body", Json.arr #[Json.mkObj
          [("kind", "return"),
           ("expr", Json.mkObj [("kind", "id"), ("name", "k")])]])]])]))
  matches .ok (.cls { methods := #[{ name := "scale", .. }], .. })
-- A parameter's type is "number" or a class object; anything else fails
-- the run rather than defaulting to a number.
#guard (decodeParam (numParamJson "x")) matches .ok { name := "x", ty := .number }
#guard
  (decodeParam (Json.mkObj
    [("name", "p"), ("type", Json.mkObj [("class", "Point")])]))
  matches .ok { name := "p", ty := .cls "Point" none }
#guard
  (decodeParam (Json.mkObj
    [("name", "p"),
     ("type", Json.mkObj [("class", "Point"), ("module", "point.mts")])]))
  matches .ok { name := "p", ty := .cls "Point" (some "point.mts") }
-- A defaulted class parameter's slot is an option of that class.
#guard
  (decodeParam (Json.mkObj
    [("name", "p"),
     ("type", Json.mkObj [("option", Json.mkObj [("class", "Pt")])])]))
  matches .ok { name := "p", ty := .option "Pt" none }
#guard
  (decodeParam (Json.mkObj [("name", "s"), ("type", "string")]))
  matches .error "unknown parameter type 'string'"
-- The three option expression kinds decode strictly, and a local may bind
-- at a class.
#guard
  (decodeExpr (Json.mkObj [("kind", "option")]))
  matches .ok (.optionInject none)
#guard
  (decodeExpr (Json.mkObj
    [("kind", "option"), ("expr", Json.mkObj [("kind", "id"), ("name", "q")])]))
  matches .ok (.optionInject (some (.id "q")))
#guard
  (decodeExpr (Json.mkObj
    [("kind", "option-test"),
     ("expr", Json.mkObj [("kind", "id"), ("name", "p")]), ("present", false)]))
  matches .ok (.optionTest (.id "p") false)
#guard
  (decodeExpr (Json.mkObj
    [("kind", "option-test"),
     ("expr", Json.mkObj [("kind", "id"), ("name", "p")]), ("present", "no")]))
  matches .error "field 'present' is not a boolean"
#guard
  (decodeExpr (Json.mkObj
    [("kind", "option-test"),
     ("expr", Json.mkObj [("kind", "id"), ("name", "p")])]))
  matches .error "property not found: present"
#guard
  (decodeExpr (Json.mkObj
    [("kind", "option-get"),
     ("expr", Json.mkObj [("kind", "id"), ("name", "p")])]))
  matches .ok (.optionGet (.id "p"))
#guard
  (decodeStmt (Json.mkObj
    [("kind", "const"), ("name", "p"),
     ("type", Json.mkObj [("class", "Pt")]),
     ("init", Json.mkObj [("kind", "id"), ("name", "q")])]))
  matches .ok (.constDecl "p" (.cls "Pt" none) (.id "q"))
#guard
  (decodeParams (Json.mkObj [("params", Json.arr #[Json.mkObj [("name", "x")]])])
    "params")
  matches .error "field 'params': property not found: type"
-- Union parameter types: an array of ≥2 known tags, order carried as-is.
#guard
  (decodeParam (Json.mkObj
    [("name", "v"), ("type", Json.arr #["number", "string"])]))
  matches .ok { name := "v", ty := .union #[.number, .string] }
#guard
  (decodeParam (Json.mkObj [("name", "v"), ("type", Json.arr #["number"])]))
  matches .error "a union parameter type needs at least two tags"
#guard
  (decodeParam (Json.mkObj
    [("name", "v"), ("type", Json.arr #["number", "object"])]))
  matches .error "unknown union tag 'object'"

-- The four union expression kinds decode strictly.
#guard
  (decodeExpr (Json.mkObj
    [("kind", "inject"), ("tag", "number"),
     ("expr", Json.mkObj [("kind", "id"), ("name", "x")])]))
  matches .ok (.inject .number (some (.id "x")))
#guard
  (decodeExpr (Json.mkObj [("kind", "inject"), ("tag", "undefined")]))
  matches .ok (.inject .undefined none)
#guard
  (decodeExpr (Json.mkObj [("kind", "inject"), ("tag", "null")]))
  matches .ok (.inject .null none)
#guard
  (decodeExpr (Json.mkObj
    [("kind", "inject"), ("tag", "boolean"),
     ("expr", Json.mkObj [("kind", "id"), ("name", "b")])]))
  matches .ok (.inject .boolean (some (.id "b")))
#guard
  (decodeExpr (Json.mkObj [("kind", "inject"), ("tag", "number")]))
  matches .error "an inject at 'number' needs its operand"
#guard
  (decodeExpr (Json.mkObj [("kind", "inject"), ("tag", "boolean")]))
  matches .error "an inject at 'boolean' needs its operand"
#guard
  (decodeExpr (Json.mkObj [("kind", "inject"), ("tag", "string")]))
  matches .error _
#guard
  (decodeExpr (Json.mkObj
    [("kind", "project"), ("tag", "number"),
     ("expr", Json.mkObj [("kind", "id"), ("name", "v")])]))
  matches .ok (.project .number (.id "v"))
#guard
  (decodeExpr (Json.mkObj
    [("kind", "typeof-test"), ("result", "number"),
     ("expr", Json.mkObj [("kind", "id"), ("name", "v")])]))
  matches .ok (.typeofTest (.id "v") "number")
#guard
  (decodeExpr (Json.mkObj
    [("kind", "typeof-test"), ("result", "numbr"),
     ("expr", Json.mkObj [("kind", "id"), ("name", "v")])]))
  matches .error "unknown typeof result 'numbr'"
#guard
  (decodeExpr (Json.mkObj
    [("kind", "jsval-eq"), ("semantics", "strict"),
     ("left", Json.mkObj [("kind", "id"), ("name", "v")]),
     ("right", Json.mkObj [("kind", "inject"), ("tag", "null")])]))
  matches .ok (.jsvalEq false (.id "v") (.inject .null none))
#guard
  (decodeExpr (Json.mkObj
    [("kind", "jsval-eq"), ("semantics", "same-value"),
     ("left", Json.mkObj [("kind", "id"), ("name", "v")]),
     ("right", Json.mkObj [("kind", "id"), ("name", "w")])]))
  matches .ok (.jsvalEq true (.id "v") (.id "w"))
#guard
  (decodeExpr (Json.mkObj
    [("kind", "jsval-eq"), ("semantics", "loose"),
     ("left", Json.mkObj [("kind", "id"), ("name", "v")]),
     ("right", Json.mkObj [("kind", "id"), ("name", "w")])]))
  matches .error "unknown equality semantics 'loose'"

-- A method missing its params is a field error, not a default.
#guard
  (decodeClass (Json.mkObj
    [("kind", "class"), ("name", "Box"), ("source", "class Box {}"),
     ("fields", Json.arr #[]), ("getters", Json.arr #[]),
     ("ctor", Json.mkObj [("params", Json.arr #[]), ("body", Json.arr #[])]),
     ("methods", Json.arr #[Json.mkObj [("name", "m")]])]))
  matches .error "property not found: params"
-- A class without its constructor is a decode error, never a default.
#guard
  (decodeDecl (Json.mkObj
    [("kind", "class"), ("name", "Box"), ("source", "class Box {}"),
     ("fields", Json.arr #[]), ("getters", Json.arr #[])]))
  matches .error _

#guard
  (decodeBinder (Json.mkObj [("name", "x"), ("kind", "int")]))
  matches .ok (.int "x")
#guard
  (decodeBinder (Json.mkObj [("name", "n"), ("kind", "nat")]))
  matches .ok (.nat "n")
#guard
  (decodeBinder (Json.mkObj
    [("name", "x"), ("kind", "range"), ("lo", "0"), ("hi", "10")]))
  matches .ok (.range "x" 0 10)
#guard
  (decodeBinder (Json.mkObj
    [("name", "a"), ("kind", "number"),
     ("lower", Json.mkObj [("op", "<"), ("lit", "0")]),
     ("upper", Json.mkObj [("op", "<="), ("lit", "1")])]))
  matches .ok (.number "a" (some (.lt, "0")) (some (.le, "1")))
-- A bound's op is decoded into the schema enum, so an op outside it fails
-- at decode time naming the side, never in the renderer.
#guard
  (decodeBinder (Json.mkObj
    [("name", "a"), ("kind", "number"),
     ("lower", Json.mkObj [("op", ">"), ("lit", "0")])]))
  matches .error "field 'lower' has op '>', not '<' or '<='"
#guard
  (decodeBinder (Json.mkObj
    [("name", "a"), ("kind", "number"),
     ("upper", Json.mkObj [("op", ">="), ("lit", "1")])]))
  matches .error "field 'upper' has op '>=', not '<' or '<='"
-- An absent side is a missing field, so a rangeless binder decodes bare.
#guard
  (decodeBinder (Json.mkObj [("name", "a"), ("kind", "number")]))
  matches .ok (.number "a" none none)
-- A class binder carries the class it ranges over and its constructor's
-- parameters; the module qualifier is absent for the entry's own.
/-- A number constructor parameter as the binder wire spells it. -/
def ctorParamJson (n : String) : Json :=
  Json.mkObj [("name", n), ("kind", "number")]

#guard
  (decodeBinder (Json.mkObj
    [("name", "p"), ("kind", "class"), ("className", "Point"),
     ("ctorParams", Json.arr #[ctorParamJson "x", ctorParamJson "y"])]))
  matches .ok (.cls "p" "Point" none #[.number "x" false, .number "y" false])
#guard
  (decodeBinder (Json.mkObj
    [("name", "p"), ("kind", "class"), ("className", "Point"),
     ("module", "dep.ts"), ("ctorParams", Json.arr #[])]))
  matches .ok (.cls "p" "Point" (some "dep.ts") #[])
-- A defaulted parameter carries its marker; its absence is not defaulted.
#guard
  (decodeCtorParam (Json.mkObj
    [("name", "y"), ("kind", "number"), ("defaulted", true)]))
  matches .ok (.number "y" true)
#guard
  (decodeCtorParam (Json.mkObj [("name", "x"), ("kind", "number")]))
  matches .ok (.number "x" false)
-- A class-typed parameter carries its own parameters, so the tree bottoms
-- out in numbers.
#guard
  (decodeBinder (Json.mkObj
    [("name", "s"), ("kind", "class"), ("className", "Span"),
     ("ctorParams", Json.arr #[Json.mkObj
       [("name", "p"), ("kind", "class"), ("className", "Point"),
        ("ctorParams", Json.arr #[ctorParamJson "x"])]])]))
  matches .ok (.cls "s" "Span" none #[.cls "p" "Point" none #[.number "x" false] false])
-- The parameters are objects with a known kind, and a missing list fails
-- the run.
#guard
  (decodeBinder (Json.mkObj
    [("name", "p"), ("kind", "class"), ("className", "Point"),
     ("ctorParams", Json.arr #[(1 : Nat)])]))
  matches .error _
#guard
  (decodeBinder (Json.mkObj
    [("name", "p"), ("kind", "class"), ("className", "Point"),
     ("ctorParams", Json.arr #[Json.mkObj
       [("name", "x"), ("kind", "bigint")]])]))
  matches .error _
#guard
  (decodeBinder (Json.mkObj
    [("name", "p"), ("kind", "class"), ("className", "Point")]))
  matches .error _
#guard (decodeBinder (Json.mkObj [("name", "x"), ("kind", "real")])) matches .error _
-- A bound is an op × literal pair; a bare string is not one.
#guard
  (decodeBinder (Json.mkObj
    [("name", "a"), ("kind", "number"), ("lower", "0")]))
  matches .error _

-- Module constants decode strictly, reads and declarations alike.
#guard
  (decodeExpr (Json.mkObj [("kind", "const-read"), ("name", "cap")]))
  matches .ok (.constRead "cap" none)
#guard
  (decodeExpr (Json.mkObj
    [("kind", "const-read"), ("name", "cap"), ("module", "constants.mts")]))
  matches .ok (.constRead "cap" (some "constants.mts"))
#guard (decodeExpr (Json.mkObj [("kind", "const-read")])) matches .error _
#guard
  (decodeDecl (Json.mkObj
    [("kind", "constant"), ("name", "cap"),
     ("init", Json.mkObj [("kind", "num"), ("lit", "-10")]),
     ("source", "const cap = -10;")]))
  matches .ok (.const { name := "cap", module := none, init := .num "-10",
                        source := "const cap = -10;" })
#guard
  (decodeDecl (Json.mkObj
    [("kind", "constant"), ("name", "m"),
     ("init", Json.mkObj
       [("kind", "binop"), ("op", "*"),
        ("left", Json.mkObj [("kind", "const-read"), ("name", "s")]),
        ("right", Json.mkObj [("kind", "num"), ("lit", "60")])]),
     ("source", "const m = s * 60;")]))
  matches .ok (.const { name := "m", module := none,
                        init := .binop "*" (.constRead "s" none) (.num "60"),
                        source := "const m = s * 60;" })
-- The literal field is gone from the wire: a constant with no initializer
-- expression is a decode error, not a literal.
#guard
  (decodeDecl (Json.mkObj
    [("kind", "constant"), ("name", "cap"), ("lit", "1000"), ("source", "")]))
  matches .error _
#guard
  (decodeDecl (Json.mkObj [("kind", "constant"), ("name", "cap")]))
  matches .error _

-- Guards are optional, decode in order, and name their own field when
-- they break the schema.
def payloadShell (guards : Json) : Json :=
  Json.mkObj
    [("kind", "structured"), ("binders", Json.arr #[]), ("guards", guards),
     ("conclusion", Json.mkObj
       [("kind", "istrue"), ("expr", Json.mkObj [("kind", "id"), ("name", "b")])])]

#guard
  (decodePayload (payloadShell (Json.arr
    #[Json.mkObj [("kind", "id"), ("name", "g")],
      Json.mkObj [("kind", "id"), ("name", "h")]])))
  matches .ok (.structured #[] #[.id "g", .id "h"] (.istrue (.id "b")))
#guard (decodePayload (payloadShell "g")) matches .error "field 'guards' is not an array"
#guard
  (decodePayload (payloadShell (Json.arr #[Json.mkObj [("kind", "typeof")]])))
  matches .error "field 'guards': unknown expression kind 'typeof'"

-- The statement decoding round-trips strictly, else arm optional.
#guard
  (decodeStmt (Json.mkObj [("kind", "throw"), ("error", "RangeError")]))
  matches .ok (.throwErr "RangeError")
#guard
  (decodeStmt (Json.mkObj
    [("kind", "let"), ("name", "y"),
     ("init", Json.mkObj [("kind", "id"), ("name", "x")])]))
  matches .ok (.letDecl "y" .number (.id "x"))
#guard
  (decodeStmt (Json.mkObj
    [("kind", "const"), ("name", "w"),
     ("type", Json.arr #[Json.str "number", Json.str "string"]),
     ("init", Json.mkObj [("kind", "id"), ("name", "v")])]))
  matches .ok (.constDecl "w" (.union #[.number, .string]) (.id "v"))
#guard
  (decodeStmt (Json.mkObj
    [("kind", "const"), ("name", "w"),
     ("type", Json.arr #[Json.str "number"]),
     ("init", Json.mkObj [("kind", "id"), ("name", "v")])]))
  matches .error _
#guard
  (decodeStmt (Json.mkObj
    [("kind", "if"),
     ("cond", Json.mkObj [("kind", "id"), ("name", "b")]),
     ("then", Json.arr #[Json.mkObj [("kind", "throw"), ("error", "E")]])]))
  matches .ok (.ite (.id "b") #[.throwErr "E"] none)
#guard (decodeStmt (Json.mkObj [("kind", "while")])) matches .error _

-- NaN is a num lit like Infinity already is: no decoder change, only a
-- renderer one.
#guard (decodeExpr (Json.mkObj [("kind", "num"), ("lit", "NaN")])) matches .ok (.num "NaN")
