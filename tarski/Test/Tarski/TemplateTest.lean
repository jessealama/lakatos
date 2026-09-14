import Tarski.Eval
import Tarski.Format

/-! Template literals, tagged and untagged.

An untagged template is a string built one substitution at a time, each
value run through ToString as it is reached. A tagged one is a call: the
tag is resolved the way a call's callee is, the template object comes
first, and the substitutions follow.

The template object is cached per *site* — one Parse Node, one object —
so a template inside a function hands the same object to its tag at every
call, and two templates with the same text do not share one. The site
number is the decoder's, in document order; the cases here write it out
by hand.

The template object and its `raw` are frozen, as GetTemplateObject has
them, and `raw` is a non-enumerable constant; the last two cases pin
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

/-- A quasi with the same cooked and raw text, which is every piece that
carries no escape. -/
private def piece (s : String) : TemplateString := { cooked := some s, raw := s }

/-- `const tag = function (s) { return s; };`, the tag that answers the
template object itself. -/
private def declareIdTag : Stmt :=
  .varDecl .«const»
    [ { target := "tag",
        init := some (.funcExpr none ["s"] [.returnStmt (some (.ident "s"))]) } ]

/-! ## Untagged -/

-- `` `a${1}b` ``
#guard outcome (expr (.template ["a", "b"] [.numLit 1.0])) == "a1b"

-- `` ` ` `` with nothing in it is one empty string.
#guard outcome (expr (.template [""] [])) == ""

-- `` `x` ``
#guard outcome (expr (.template ["x"] [])) == "x"

-- `` `\n`.length `` — the cooked value is the escape resolved, so one
-- code unit.
#guard outcome (expr (.member (.template ["\n"] []) "length")) == "1"

-- `const o = { v: 2, dyn1: 1 }; `${o.v}-${o.dyn1}`;` — #395's example's
-- first conjunct.
#guard outcome
    [ .varDecl .«const»
        [ { target := "o",
            init := some (.objectLit
              [.init "v" (.numLit 2.0), .init "dyn1" (.numLit 1.0)]) } ],
      .exprStmt (.template ["", "-", ""]
        [.member (.ident "o") "v", .member (.ident "o") "dyn1"]) ]
  == "2-1"

-- A substitution is ToString, which is ToPrimitive with the string hint
-- and then ToString on the primitive.
-- `` `${{ toString() { return "t"; } }}` ``
#guard outcome
    (expr (.template ["", ""]
      [.objectLit [.method .method "toString" [] [.returnStmt (some (.strLit "t"))]]]))
  == "t"

-- The string hint tries `toString` first, and `Object.prototype` has
-- one, so an object's own `valueOf` is never reached.
-- `` `${{ valueOf() { return 1; } }}` ``
#guard outcome
    (expr (.template ["", ""]
      [.objectLit [.method .method "valueOf" [] [.returnStmt (some (.numLit 1.0))]]]))
  == "[object Object]"

-- A throwing `toString` throws out of the template.
#guard outcome
    (expr (.template ["", ""]
      [.objectLit
        [.method .method "toString" [] [.throwStmt (.new (.ident "TypeError") [])]]]))
  == "uncaught: TypeError"

-- Left to right, one substitution at a time.
-- `let i = 0; `a${i++}b${i++}c${i++}d`;`
#guard outcome
    [ .varDecl .«let» [{ target := "i", init := some (.numLit 0.0) }],
      .exprStmt (.template ["a", "b", "c", "d"]
        [ .update .inc false (.ident "i"),
          .update .inc false (.ident "i"),
          .update .inc false (.ident "i") ]) ]
  == "a0b1c2d"

-- ToString runs after each expression is evaluated, so an earlier
-- value's `toString` has already run when a later expression throws.
-- `let log = ""; try { `${{ toString() { log = log + "t"; return ""; } }}${(function () { throw new TypeError(); })()}`; } catch (e) {} log;`
#guard outcome
    [ .varDecl .«let» [{ target := "log", init := some (.strLit "") }],
      .tryStmt
        [ .exprStmt (.template ["", "", ""]
            [ .objectLit
                [ .method .method "toString" []
                    [ .exprStmt (.assign (.ident "log")
                        (.binary .add (.ident "log") (.strLit "t"))),
                      .returnStmt (some (.strLit "")) ] ],
              .call (.funcExpr none [] [.throwStmt (.new (.ident "TypeError") [])]) [] ]) ]
        (some { param := some "e", body := [] }) none,
      .exprStmt (.ident "log") ]
  == "t"

-- A template nests inside a substitution like any other expression.
-- `` `a${`b${1}c`}d` ``
#guard outcome
    (expr (.template ["a", "d"] [.template ["b", "c"] [.numLit 1.0]]))
  == "ab1cd"

/-! ## Tagged: the argument list -/

-- ``const tag = function (s) { return s; }; tag`a${1}b`.length;`` — the
-- template object is an array of the cooked strings.
#guard outcome
    [ declareIdTag,
      .exprStmt (.member
        (.taggedTemplate (.ident "tag") 0 [piece "a", piece "b"] [.numLit 1.0]) "length") ]
  == "2"

-- ``tag`a${1}b`.raw.join("|");``
#guard outcome
    [ declareIdTag,
      .exprStmt (.call (.member (.member
        (.taggedTemplate (.ident "tag") 0 [piece "a", piece "b"] [.numLit 1.0]) "raw")
        "join") [.strLit "|"]) ]
  == "a|b"

-- The substitutions come after the template object, in order.
-- ``const tag = function (s, a, b) { return a + "," + b; }; tag`a${1}b${2}c`;``
#guard outcome
    [ .varDecl .«const»
        [ { target := "tag",
            init := some (.funcExpr none ["s", "a", "b"]
              [ .returnStmt (some (.binary .add
                  (.binary .add (.ident "a") (.strLit ",")) (.ident "b"))) ]) } ],
      .exprStmt (.taggedTemplate (.ident "tag") 0
        [piece "a", piece "b", piece "c"] [.numLit 1.0, .numLit 2.0]) ]
  == "1,2"

-- Both the template object and its `raw` are arrays.
#guard outcome
    [ declareIdTag,
      .exprStmt (.call (.member (.ident "Array") "isArray")
        [.taggedTemplate (.ident "tag") 0 [piece "x"] []]) ]
  == "true"

#guard outcome
    [ declareIdTag,
      .exprStmt (.call (.member (.ident "Array") "isArray")
        [.member (.taggedTemplate (.ident "tag") 0 [piece "x"] []) "raw"]) ]
  == "true"

-- An escape the cooked grammar refuses is `undefined` in the template
-- object and still there in `raw`. Only a tagged template may carry one:
-- untagged, the escape is a parse error the bridge refuses.
-- ``const tag = function (s) { return typeof s[0] + ":" + s.raw[0]; }; tag`\unicode`;``
#guard outcome
    [ .varDecl .«const»
        [ { target := "tag",
            init := some (.funcExpr none ["s"]
              [ .returnStmt (some (.binary .add
                  (.binary .add
                    (.unary .typeof (.index (.ident "s") (.numLit 0.0)))
                    (.strLit ":"))
                  (.index (.member (.ident "s") "raw") (.numLit 0.0)))) ]) } ],
      .exprStmt (.taggedTemplate (.ident "tag") 0
        [{ cooked := none, raw := "\\unicode" }] []) ]
  == "undefined:\\unicode"

-- A non-callable tag is the same `TypeError` a non-callable callee is.
#guard outcome (expr (.taggedTemplate (.numLit 1.0) 0 [piece "x"] []))
  == "uncaught: TypeError: not a function"

/-! ## Tagged: the template object is cached per site -/

-- One site, two evaluations, one object.
-- ``function run() { return tag`h${1}t`; } run() === run();``
#guard outcome
    [ declareIdTag,
      .funcDecl "run" []
        [ .returnStmt (some (.taggedTemplate (.ident "tag") 0
            [piece "h", piece "t"] [.numLit 1.0])) ],
      .exprStmt (.binary .strictEq
        (.call (.ident "run") []) (.call (.ident "run") [])) ]
  == "true"

-- Two sites with the same text are two objects.
-- ``tag`h${1}t` === tag`h${1}t`;``
#guard outcome
    [ declareIdTag,
      .exprStmt (.binary .strictEq
        (.taggedTemplate (.ident "tag") 0 [piece "h", piece "t"] [.numLit 1.0])
        (.taggedTemplate (.ident "tag") 1 [piece "h", piece "t"] [.numLit 1.0])) ]
  == "false"

-- Five evaluations of two sites: the four from one site are all the same
-- object and the fifth is not.
#guard outcome
    [ declareIdTag,
      .funcDecl "here" []
        [.returnStmt (some (.taggedTemplate (.ident "tag") 0 [piece "q"] []))],
      .funcDecl "there" []
        [.returnStmt (some (.taggedTemplate (.ident "tag") 1 [piece "q"] []))],
      .exprStmt (.logical .and
        (.logical .and
          (.binary .strictEq (.call (.ident "here") []) (.call (.ident "here") []))
          (.binary .strictEq (.call (.ident "here") []) (.call (.ident "here") [])))
        (.binary .strictNe (.call (.ident "here") []) (.call (.ident "there") []))) ]
  == "true"

/-! ## Tagged: the tag is a call's callee -/

-- A member tag passes its object as `this`, exactly as `o.f()` does.
-- ``const obj = { v: 5, fn(s) { return this.v; } }; obj.fn`x`;``
#guard outcome
    [ .varDecl .«const»
        [ { target := "obj",
            init := some (.objectLit
              [ .init "v" (.numLit 5.0),
                .method .method "fn" ["s"] [.returnStmt (some (.member .this "v"))] ]) } ],
      .exprStmt (.taggedTemplate (.member (.ident "obj") "fn") 0 [piece "x"] []) ]
  == "5"

-- A call-expression tag is evaluated first, and its answer is the tag.
-- ``const make = function () { return tag; }; make()`x`[0];``
#guard outcome
    [ declareIdTag,
      .varDecl .«const»
        [ { target := "make",
            init := some (.funcExpr none [] [.returnStmt (some (.ident "tag"))]) } ],
      .exprStmt (.index
        (.taggedTemplate (.call (.ident "make") []) 0 [piece "x"] []) (.numLit 0.0)) ]
  == "x"

-- ``new tag`x` `` is a `new` over the tagged node: the tag runs first,
-- and what it answered is what `new` constructs.
#guard outcome
    [ .varDecl .«const»
        [ { target := "tag",
            init := some (.funcExpr none ["s"]
              [ .returnStmt (some (.funcExpr none ["a"]
                  [.exprStmt (.assign (.member .this "got") (.ident "a"))])) ]) } ],
      .exprStmt (.member
        (.new (.taggedTemplate (.ident "tag") 0 [piece "x"] []) [.strLit "arg"]) "got") ]
  == "arg"

-- A chain applies the tags left to right.
-- ``let log = ""; const tag = function (s) { log = log + s[0]; return tag; }; tag`a``b``c`; log;``
#guard outcome
    [ .varDecl .«let» [{ target := "log", init := some (.strLit "") }],
      .varDecl .«const»
        [ { target := "tag",
            init := some (.funcExpr none ["s"]
              [ .exprStmt (.assign (.ident "log") (.binary .add (.ident "log")
                  (.index (.ident "s") (.numLit 0.0)))),
                .returnStmt (some (.ident "tag")) ]) } ],
      .exprStmt (.taggedTemplate
        (.taggedTemplate
          (.taggedTemplate (.ident "tag") 0 [piece "a"] []) 1 [piece "b"] [])
        2 [piece "c"] []),
      .exprStmt (.ident "log") ]
  == "abc"

/-! ## Tagged: the template object is frozen

GetTemplateObject freezes the template object and its `raw` (13.2.8.4
steps 12 and 15) and defines `raw` non-enumerable, so `Object.keys` lists
the cooked strings' indices alone and a write to an element is the
strict-mode `TypeError` a frozen write is. -/

-- ``Object.keys(tag`a`).join();``
#guard outcome
    [ declareIdTag,
      .exprStmt (.call (.member
        (.call (.member (.ident "Object") "keys")
          [.taggedTemplate (.ident "tag") 0 [piece "a"] []]) "join") []) ]
  == "0"

-- ``const t = tag`a`; t[0] = 1; t[0];``
#guard outcome
    [ declareIdTag,
      .varDecl .«const»
        [ { target := "t",
            init := some (.taggedTemplate (.ident "tag") 0 [piece "a"] []) } ],
      .exprStmt (.assign (.index (.ident "t") (.numLit 0.0)) (.numLit 1.0)),
      .exprStmt (.index (.ident "t") (.numLit 0.0)) ]
  == "uncaught: TypeError: Cannot assign to read only property '0' of object '#<Object>'"
