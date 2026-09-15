import Tarski.Eval
import Tarski.Format

/-! Object-literal members: shorthand, computed and numeric keys,
methods, getters and setters, and `__proto__`.

PropertyDefinitionEvaluation in one file. What it pins is the order —
key before value, members left to right — and that every member is a
*definition* rather than a write, so a data member replaces an accessor
of the same name rather than calling its setter.

A literal's accessors are enumerable, unlike a class's, and every member
takes its place in source order; the case at the end of this file pins
that. -/

open Tarski

/-- What the binary would print, so a case reads as its own stdout. -/
private def outcome (p : Program) : String :=
  match runScript p with
  | none => "<diverges>"
  | some (.error (.throw v), h) => s!"uncaught: {describeThrown h v}"
  | some (.error _, _) => "<abrupt>"
  | some (.ok none, _) => "<empty>"
  | some (.ok (some v), _) => formatValue v

private def expr (e : Expr) : Program := [.exprStmt e]

/-- `Object.keys(<e>).join()` -/
private def keysJoined (e : Expr) : Expr :=
  .call (.member (.call (.member (.ident "Object") "keys") [e]) "join") []

/-- `function t(s, v) { log = log + s; return v; }` — a probe that
records that it ran and answers its second argument, so a case can read
the order its members were evaluated in off `log`. -/
private def declareLog : List Stmt :=
  [ .varDecl .«let» [{ target := "log", init := some (.strLit "") }],
    .funcDecl "t" ["s", "v"]
      [ .exprStmt (.assign (.ident "log") (.binary .add (.ident "log") (.ident "s"))),
        .returnStmt (some (.ident "v")) ] ]

/-- `t(<s>, <v>)` -/
private def probe (s : String) (v : Expr) : Expr :=
  .call (.ident "t") [.strLit s, v]

/-! ## Shorthand

A shorthand's value is its own `Identifier`, so it is an ordinary data
member and `{ undefined }` binds the literal `undefined` binds. -/

-- `const v = 2; ({ v }).v;`
#guard outcome
    [ .varDecl .«const» [{ target := "v", init := some (.numLit 2.0) }],
      .exprStmt (.member (.objectLit [.init "v" (.ident "v")]) "v") ]
  == "2"

-- `({ undefined }).undefined;`
#guard outcome (expr (.member (.objectLit [.init "undefined" .undefLit]) "undefined"))
  == "undefined"

-- `const v = 2; Object.keys({ v }).join();`
#guard outcome
    [ .varDecl .«const» [{ target := "v", init := some (.numLit 2.0) }],
      .exprStmt (keysJoined (.objectLit [.init "v" (.ident "v")])) ]
  == "v"

/-! ## Computed keys -/

-- `const k = "dyn"; ({ [k + "1"]: 1 }).dyn1;`
#guard outcome
    [ .varDecl .«const» [{ target := "k", init := some (.strLit "dyn") }],
      .exprStmt (.member (.objectLit
        [.init (.computed (.binary .add (.ident "k") (.strLit "1"))) (.numLit 1.0)]) "dyn1") ]
  == "1"

-- `({ [1]: "a" })["1"];` — ToPropertyKey, so the key is its string.
#guard outcome
    (expr (.index (.objectLit [.init (.computed (.numLit 1.0)) (.strLit "a")]) (.strLit "1")))
  == "a"

-- `({ [{ toString() { return "t"; } }]: 1 }).t;` — a computed key is
-- ToPropertyKey'd, which runs ToPrimitive on an object.
#guard outcome
    (expr (.member (.objectLit
      [ .init (.computed (.objectLit
          [.method .method "toString" [] [.returnStmt (some (.strLit "t"))]]))
          (.numLit 1.0) ]) "t"))
  == "1"

/-! ## Order: key before value, members left to right -/

-- `let log = ""; ({ [t("k1", "a")]: t("v1", 1), [t("k2", "b")]: t("v2", 2) }); log;`
#guard outcome
    (declareLog ++
      [ .exprStmt (.objectLit
          [ .init (.computed (probe "k1" (.strLit "a"))) (probe "v1" (.numLit 1.0)),
            .init (.computed (probe "k2" (.strLit "b"))) (probe "v2" (.numLit 2.0)) ]),
        .exprStmt (.ident "log") ])
  == "k1v1k2v2"

-- A throwing key abandons the literal where it stands: nothing after it
-- runs, and the members before it are already gone with the object.
#guard outcome
    (declareLog ++
      [ .tryStmt
          [ .exprStmt (.objectLit
              [ .init (.computed (probe "k1" (.strLit "a"))) (probe "v1" (.numLit 1.0)),
                .init (.computed (.call
                  (.funcExpr none [] [.throwStmt (.new (.ident "TypeError") [])]) []))
                  (probe "v2" (.numLit 2.0)),
                .init (.computed (probe "k3" (.strLit "c"))) (.numLit 3.0) ]) ]
          (some { param := some "e", body := [] }) none,
        .exprStmt (.ident "log") ])
  == "k1v1"

/-! ## Numeric keys

A numeric key decodes as a computed key over its literal, so its
spelling is the library's `Number::toString` at evaluation rather than a
second copy of that algorithm in the decoder. -/

-- `({ 1: "a" })["1"];`
#guard outcome
    (expr (.index (.objectLit [.init (.computed (.numLit 1.0)) (.strLit "a")]) (.strLit "1")))
  == "a"

-- `({ 1.5: "b" })["1.5"];`
#guard outcome
    (expr (.index (.objectLit [.init (.computed (.numLit 1.5)) (.strLit "b")]) (.strLit "1.5")))
  == "b"

-- `({ 0x10: "c" })["16"];`
#guard outcome
    (expr (.index (.objectLit [.init (.computed (.numLit 16.0)) (.strLit "c")]) (.strLit "16")))
  == "c"

-- `({ 1e21: "d" })["1e+21"];`
#guard outcome
    (expr (.index (.objectLit [.init (.computed (.numLit 1e21)) (.strLit "d")])
      (.strLit "1e+21")))
  == "d"

/-! ## Methods

A literal's method is the closure a class's method is: a `this`, no
`prototype`, and no `[[Construct]]`. -/

-- `({ v: 2, m() { return this.v; } }).m();`
#guard outcome
    (expr (.call (.member (.objectLit
      [ .init "v" (.numLit 2.0),
        .method .method "m" [] [.returnStmt (some (.member .this "v"))] ]) "m") []))
  == "2"

-- `typeof ({ m() {} }).m;`
#guard outcome
    (expr (.unary .typeof (.member (.objectLit [.method .method "m" [] []]) "m")))
  == "function"

-- `new (({ m() {} }).m)();`
#guard outcome (expr (.new (.member (.objectLit [.method .method "m" [] []]) "m") []))
  == "uncaught: TypeError: not a constructor"

-- `typeof ({ m() {} }).m.prototype;` — a method has none, where an
-- ordinary function expression does.
#guard outcome
    (expr (.unary .typeof
      (.member (.member (.objectLit [.method .method "m" [] []]) "m") "prototype")))
  == "undefined"

-- `typeof (function () {}).prototype;`
#guard outcome
    (expr (.unary .typeof (.member (.funcExpr none [] []) "prototype")))
  == "object"

-- `({ m(a, b = 1) {} }).m.length;` — ExpectedArgumentCount, so the
-- parameters before the first default.
#guard outcome
    (expr (.member (.member (.objectLit
      [.method .method "m" ["a", ⟨"b", some (.numLit 1.0), false⟩] []]) "m") "length"))
  == "1"

-- `const p = { x() { return 1; } };`
-- `({ __proto__: p, x() { return super.x() + 1; } }).x();` — the home
-- object of a literal's method is the literal, so `super` reads through
-- the literal's own prototype.
#guard outcome
    [ .varDecl .«const»
        [ { target := "p",
            init := some (.objectLit
              [.method .method "x" [] [.returnStmt (some (.numLit 1.0))]]) } ],
      .exprStmt (.call (.member (.objectLit
        [ .proto (.ident "p"),
          .method .method "x" []
            [.returnStmt (some (.binary .add (.call (.superMember "x") []) (.numLit 1.0)))] ])
        "x") []) ]
  == "2"

-- `function f() { return ({ m() { return arguments.length; } }).m(1, 2); } f(9);`
-- A method has an `arguments` of its own.
#guard outcome
    [ .funcDecl "f" []
        [ .returnStmt (some (.call (.member (.objectLit
            [ .method .method "m" []
                [.returnStmt (some (.member (.ident "arguments") "length"))] ]) "m")
            [.numLit 1.0, .numLit 2.0])) ],
      .exprStmt (.call (.ident "f") [.numLit 9.0]) ]
  == "2"

-- `function f() { return { [arguments[0]]: 1 }; } Object.keys(f("k")).join();`
-- A computed key is evaluated where the literal is written, so its
-- `arguments` is the enclosing function's.
#guard outcome
    [ .funcDecl "f" []
        [ .returnStmt (some (.objectLit
            [.init (.computed (.index (.ident "arguments") (.numLit 0.0))) (.numLit 1.0)])) ],
      .exprStmt (keysJoined (.call (.ident "f") [.strLit "k"])) ]
  == "k"

/-! ## Getters and setters -/

-- `({ get g() { return 3; } }).g;`
#guard outcome
    (expr (.member (.objectLit
      [.method .getter "g" [] [.returnStmt (some (.numLit 3.0))]]) "g"))
  == "3"

-- `const o = { set s(v) { this.w = v * 2; } }; o.s = 2; o.w;`
#guard outcome
    [ .varDecl .«const»
        [ { target := "o",
            init := some (.objectLit
              [ .method .setter "s" ["v"]
                  [.exprStmt (.assign (.member .this "w")
                    (.binary .mul (.ident "v") (.numLit 2.0)))] ]) } ],
      .exprStmt (.assign (.member (.ident "o") "s") (.numLit 2.0)),
      .exprStmt (.member (.ident "o") "w") ]
  == "4"

-- A `get` and a `set` of one name make one property with two halves.
-- `const o = { get a() { return this._a; }, set a(v) { this._a = v * 2; } };`
-- `o.a = 3; o.a;`
#guard outcome
    [ .varDecl .«const»
        [ { target := "o",
            init := some (.objectLit
              [ .method .getter "a" [] [.returnStmt (some (.member .this "_a"))],
                .method .setter "a" ["v"]
                  [.exprStmt (.assign (.member .this "_a")
                    (.binary .mul (.ident "v") (.numLit 2.0)))] ]) } ],
      .exprStmt (.assign (.member (.ident "o") "a") (.numLit 3.0)),
      .exprStmt (.member (.ident "o") "a") ]
  == "6"

-- `const o = { get a() { return 1; } }; o.a = 2;`
#guard outcome
    [ .varDecl .«const»
        [ { target := "o",
            init := some (.objectLit
              [.method .getter "a" [] [.returnStmt (some (.numLit 1.0))]]) } ],
      .exprStmt (.assign (.member (.ident "o") "a") (.numLit 2.0)) ]
  == "uncaught: TypeError: Cannot set property a of #<Object> which has only a getter"

-- A data member after a getter *replaces* it: every member is a
-- definition, so the setter is never called and the accessor is gone.
-- `({ get a() { return 1; }, a: 2 }).a;`
#guard outcome
    (expr (.member (.objectLit
      [ .method .getter "a" [] [.returnStmt (some (.numLit 1.0))],
        .init "a" (.numLit 2.0) ]) "a"))
  == "2"

-- And a getter after a data member replaces that.
-- `({ a: 2, get a() { return 1; } }).a;`
#guard outcome
    (expr (.member (.objectLit
      [ .init "a" (.numLit 2.0),
        .method .getter "a" [] [.returnStmt (some (.numLit 1.0))] ]) "a"))
  == "1"

/-! ## Duplicate keys -/

-- `({ a: 1, b: 2, a: 3 }).a;` — the last one wins.
#guard outcome
    (expr (.member (.objectLit
      [.init "a" (.numLit 1.0), .init "b" (.numLit 2.0), .init "a" (.numLit 3.0)]) "a"))
  == "3"

-- `Object.keys({ a: 1, b: 2, a: 3 }).join();` — and the first
-- occurrence's position is kept.
#guard outcome
    (expr (keysJoined (.objectLit
      [.init "a" (.numLit 1.0), .init "b" (.numLit 2.0), .init "a" (.numLit 3.0)])))
  == "a,b"

/-! ## `__proto__`

B.3.1: a written, non-shorthand `__proto__` key sets `[[Prototype]]`
when its value is an object or `null`, and does nothing at all
otherwise. Every other spelling of the name is an ordinary member. -/

-- `({ __proto__: null }).hasOwnProperty;`
#guard outcome (expr (.member (.objectLit [.proto .nullLit]) "hasOwnProperty"))
  == "undefined"

-- `const p = { x: 1 }; ({ "__proto__": p }).x;` — a string-literal key
-- counts, which is what the decoder's `.name` arm says.
#guard outcome
    [ .varDecl .«const»
        [ { target := "p",
            init := some (.objectLit [.init "x" (.numLit 1.0)]) } ],
      .exprStmt (.member (.objectLit [.proto (.ident "p")]) "x") ]
  == "1"

-- `const f = function () {}; f.tag = 1; ({ __proto__: f }).tag;` — a
-- function is an object, so it links.
#guard outcome
    [ .varDecl .«const» [{ target := "f", init := some (.funcExpr none [] []) }],
      .exprStmt (.assign (.member (.ident "f") "tag") (.numLit 1.0)),
      .exprStmt (.member (.objectLit [.proto (.ident "f")]) "tag") ]
  == "1"

-- `({ __proto__: 1 }).hasOwnProperty === Object.prototype.hasOwnProperty;`
-- A primitive other than `null` does nothing: the prototype is still
-- `Object.prototype`.
#guard outcome
    (expr (.binary .strictEq
      (.member (.objectLit [.proto (.numLit 1.0)]) "hasOwnProperty")
      (.member (.member (.ident "Object") "prototype") "hasOwnProperty")))
  == "true"

-- And it makes no own property either.
#guard outcome (expr (keysJoined (.objectLit [.proto (.numLit 1.0)]))) == ""

-- `const p = { x: 1 }; ({ ["__proto__"]: p }).hasOwnProperty("__proto__");`
-- A computed key is an ordinary member, however it spells out.
#guard outcome
    [ .varDecl .«const»
        [ { target := "p",
            init := some (.objectLit [.init "x" (.numLit 1.0)]) } ],
      .exprStmt (.call (.member (.objectLit
        [.init (.computed (.strLit "__proto__")) (.ident "p")]) "hasOwnProperty")
        [.strLit "__proto__"]) ]
  == "true"

-- `const __proto__ = p; ({ __proto__ }).hasOwnProperty("__proto__");`
-- So is a shorthand.
#guard outcome
    [ .varDecl .«const»
        [ { target := "p",
            init := some (.objectLit [.init "x" (.numLit 1.0)]) } ],
      .varDecl .«const» [{ target := "__proto__", init := some (.ident "p") }],
      .exprStmt (.call (.member (.objectLit [.init "__proto__" (.ident "__proto__")])
        "hasOwnProperty") [.strLit "__proto__"]) ]
  == "true"

/-! ## Members keep source order, accessors included

A getter is an enumerable own property like any other member, so
`Object.keys` lists it where it was written. -/

-- `Object.keys({ get g() {}, a: 1 }).join();`
#guard outcome
    (expr (keysJoined (.objectLit
      [.method .getter "g" [] [], .init "a" (.numLit 1.0)])))
  == "g,a"
