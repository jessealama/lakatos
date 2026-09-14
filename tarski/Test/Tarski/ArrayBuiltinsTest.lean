import Tarski.Eval
import Tarski.Format

/-! `Array.prototype`'s members that no callback enters, and the issue's
own example.

`Test/Tarski/ArraysTest.lean` has the literal, the live `length`, `push`,
`join`, `Array.isArray`, and the `Array` constructor;
`Test/Tarski/ArrayIterationTest.lean` has the seven callback members,
`reduce`, `flat`, `sort`, and the two statics. This file is the rest of
23.1.3: `toString`, `toLocaleString`, `at`, `concat`, `copyWithin`,
`fill`, `includes`, `indexOf`, `lastIndexOf`, `pop`, `reverse`, `shift`,
`slice`, `splice`, and `unshift`.

**Every one of them is generic over an array-like**, which is what the
plain-object cases below pin: ToObject on the receiver,
LengthOfArrayLike for its length, and the four internal methods for its
elements. A hole is a key that is not there, so each member's treatment
of one is its own — `slice` and `concat` keep a hole, `flat` drops one,
`includes` reads one as `undefined` where `indexOf` skips it, and
`sort` moves them all to the end and then deletes them. -/

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

/-- An array literal of number literals. -/
private def nums (xs : List Float) : Expr := .arrayLit (xs.map (.numLit ·))

/-- `<recv>.<name>(<args>)`. -/
private def callOn (recv : Expr) (name : String) (args : List Expr) : Expr :=
  .call (.member recv name) args

/-- `Array.prototype.<name>` -/
private def protoMember (name : String) : Expr :=
  .member (.member (.ident "Array") "prototype") name

/-- `Array.prototype.<name>.call(<args>)` — the generic form, spelled the
way the harness spells it. -/
private def protoCall (name : String) (args : List Expr) : Expr :=
  .call (.member (protoMember name) "call") args

/-- `{ length: 2, 0: "a", 1: "b" }`, the array-like the specification's
"generic" means. -/
private def arrayLike : Expr :=
  .objectLit [.init "length" (.numLit 2.0), .init "0" (.strLit "a"), .init "1" (.strLit "b")]

/-! ## The issue's example

```js
"use strict";
const xs = [3, 1, 2];
xs.sort((a, b) => a - b);
const ys = xs.map((x) => x * 2).filter((x) => x > 2);
ys.length === 2 && ys.indexOf(6) === 1 && [1, [2, [3]]].flat(Infinity).length === 3 &&
  Array.from({ length: 2 }, (_, i) => i).join() === "0,1";
```

A comparator sort, `map` and `filter` through ArraySpeciesCreate,
`indexOf`, an unbounded `flat`, and `Array.from` over an array-like with
a mapper — the whole of what this slice is for, in one program. It is
`Test/Tarski/fixtures/array-builtins.json` too, run on the binary by
`tarski.yml`. -/

/-- `(a, b) => a - b` -/
private def comparator : Expr :=
  .arrow [{ target := "a", default := none }, { target := "b", default := none }]
    (.expr (.binary .sub (.ident "a") (.ident "b")))

#guard outcome
    [ .varDecl .«const» [{ target := "xs", init := some (nums [3.0, 1.0, 2.0]) }],
      .exprStmt (callOn (.ident "xs") "sort" [comparator]),
      .varDecl .«const» [{ target := "ys", init := some (callOn
        (callOn (.ident "xs") "map"
          [.arrow [{ target := "x", default := none }]
            (.expr (.binary .mul (.ident "x") (.numLit 2.0)))])
        "filter"
        [.arrow [{ target := "x", default := none }]
          (.expr (.binary .gt (.ident "x") (.numLit 2.0)))]) }],
      .exprStmt (.logical .and
        (.logical .and
          (.logical .and
            (.binary .strictEq (.member (.ident "ys") "length") (.numLit 2.0))
            (.binary .strictEq (callOn (.ident "ys") "indexOf" [.numLit 6.0]) (.numLit 1.0)))
          (.binary .strictEq
            (.member
              (callOn (.arrayLit [.numLit 1.0, .arrayLit [.numLit 2.0, nums [3.0]]]) "flat"
                [.ident "Infinity"])
              "length")
            (.numLit 3.0)))
        (.binary .strictEq
          (callOn
            (.call (.member (.ident "Array") "from")
              [.objectLit [.init "length" (.numLit 2.0)],
               .arrow [{ target := "_", default := none }, { target := "i", default := none }]
                 (.expr (.ident "i"))])
            "join" [])
          (.strLit "0,1"))) ]
  == "true"

/-! ## `toString` and `toLocaleString`

23.1.3.36 calls the receiver's *own* `join` when it has a callable one,
and `Object.prototype.toString` when it does not — which is why an
array's ToString is its elements and a receiver that has shadowed `join`
with a non-function gets a tag. -/

#guard outcome (expr (callOn (nums [1.0, 2.0]) "toString" [])) == "1,2"
#guard outcome (expr (.call (.ident "String") [.arrayLit [.numLit 1.0, nums [2.0, 3.0]]]))
  == "1,2,3"
#guard outcome (expr (.binary .add (.strLit "") (nums [1.0]))) == "1"
#guard outcome (expr (protoCall "toString" [.objectLit [.init "join" (.numLit 1.0)]]))
  == "[object Object]"
#guard outcome (expr (callOn (nums [1.0, 2.0]) "toLocaleString" [])) == "1,2"
-- A nullish element contributes nothing, as it does to `join`.
#guard outcome
    (expr (callOn (.arrayLit [.numLit 1.0, .nullLit, .undefLit]) "toLocaleString" []))
  == "1,,"

/-! ## `at`

23.1.3.1 is the one member that does not clamp: an index off either end
is `undefined`, and so is either infinity. -/

#guard outcome (expr (callOn (nums [1.0, 2.0, 3.0]) "at" [.numLit 0.0])) == "1"
#guard outcome (expr (callOn (nums [1.0, 2.0, 3.0]) "at" [.unary .neg (.numLit 1.0)])) == "3"
#guard outcome (expr (callOn (nums [1.0, 2.0]) "at" [.unary .neg (.numLit 5.0)])) == "undefined"
#guard outcome (expr (callOn (nums [1.0, 2.0]) "at" [.numLit 5.0])) == "undefined"
#guard outcome (expr (callOn (nums [1.0, 2.0]) "at" [.ident "Infinity"])) == "undefined"
#guard outcome
    (expr (callOn (nums [1.0, 2.0]) "at" [.unary .neg (.ident "Infinity")]))
  == "undefined"
#guard outcome (expr (protoCall "at" [arrayLike, .numLit 1.0])) == "b"

/-! ## `concat`

23.1.3.2 spreads an array argument and appends anything else whole. The
receiver is the first item, so `[1].concat([2], 3)` and a `call` with the
same three differ only in where the receiver lands. -/

#guard outcome
    (expr (callOn (callOn (nums [1.0]) "concat"
      [nums [2.0], .numLit 3.0, .arrayLit [nums [4.0]]]) "join" []))
  == "1,2,3,4"
-- The nested array is one element, not two: spreading is one level.
#guard outcome
    (expr (.member (callOn (nums [1.0]) "concat" [.arrayLit [nums [4.0]]]) "length"))
  == "2"
-- A hole in a spread argument stays a hole. There is no elision in this
-- AST (`[1, , 2]` is #394's), so the hole is a write past the end.
#guard outcome
    [ .varDecl .«const» [{ target := "xs", init := some (nums [1.0]) }],
      .exprStmt (.assign (.index (.ident "xs") (.numLit 2.0)) (.numLit 2.0)),
      .exprStmt (callOn (callOn (.ident "xs") "concat" []) "hasOwnProperty" [.numLit 1.0]) ]
  == "false"
-- An array-like is *not* spread: IsConcatSpreadable is IsArray here.
#guard outcome (expr (.member (callOn (nums [1.0]) "concat" [arrayLike]) "length")) == "2"
-- The species is the receiver's `constructor`: a subclass of `Array`
-- builds a subclass instance.
#guard outcome
    [ .classDecl "A" { name := some "A", superClass := some (.ident "Array"), elements := [] },
      .exprStmt (.binary .instanceof
        (callOn (.new (.ident "A") [.numLit 1.0]) "concat" [.arrayLit []]) (.ident "A")) ]
  == "true"
-- A `constructor` that is not an object at all is IsConstructor's refusal.
#guard outcome
    [ .varDecl .«const» [{ target := "xs", init := some (nums [1.0]) }],
      .exprStmt (.assign (.member (.ident "xs") "constructor") .nullLit),
      .exprStmt (callOn (.ident "xs") "concat" []) ]
  == "uncaught: TypeError: not a constructor"
-- An ordinary object `constructor` has no species, so the result is a
-- plain array.
#guard outcome
    [ .varDecl .«const» [{ target := "xs", init := some (nums [1.0]) }],
      .exprStmt (.assign (.member (.ident "xs") "constructor") (.objectLit [])),
      .exprStmt (.binary .instanceof (callOn (.ident "xs") "concat" []) (.ident "Array")) ]
  == "true"

/-! ## `slice` -/

#guard outcome (expr (callOn (callOn (nums [1.0, 2.0, 3.0]) "slice" [.numLit 1.0]) "join" []))
  == "2,3"
#guard outcome
    (expr (callOn (callOn (nums [1.0, 2.0, 3.0]) "slice"
      [.unary .neg (.numLit 2.0)]) "join" []))
  == "2,3"
#guard outcome
    (expr (callOn (callOn (nums [1.0, 2.0, 3.0]) "slice"
      [.unary .neg (.ident "Infinity")]) "join" []))
  == "1,2,3"
#guard outcome
    (expr (callOn (callOn (nums [1.0, 2.0]) "slice" [.numLit 1.0, .ident "Infinity"]) "join" []))
  == "2"
#guard outcome (expr (.member (callOn (nums [1.0, 2.0]) "slice" [.numLit 5.0]) "length")) == "0"
-- A hole stays a hole: `copyElements` asks HasProperty first.
#guard outcome
    [ .varDecl .«const» [{ target := "xs", init := some (.call (.ident "Array") [.numLit 2.0]) }],
      .exprStmt (.assign (.index (.ident "xs") (.numLit 0.0)) (.numLit 1.0)),
      .exprStmt (callOn (callOn (.ident "xs") "slice" []) "hasOwnProperty" [.numLit 1.0]) ]
  == "false"
#guard outcome (expr (callOn (protoCall "slice" [arrayLike]) "join" [])) == "a,b"

/-! ## `includes`, `indexOf`, and `lastIndexOf`

The three differ in their equality and in what they do with a hole:
`includes` is SameValueZero and reads a hole as `undefined`, while the
two `indexOf`s are `===` and skip one. -/

#guard outcome (expr (callOn (.arrayLit [.ident "NaN"]) "includes" [.ident "NaN"])) == "true"
#guard outcome (expr (callOn (.arrayLit [.ident "NaN"]) "indexOf" [.ident "NaN"])) == "-1"
#guard outcome
    (expr (callOn (nums [0.0]) "includes" [.unary .neg (.numLit 0.0)]))
  == "true"
-- A hole reads `undefined` for `includes`.
#guard outcome
    (expr (callOn (.call (.ident "Array") [.numLit 2.0]) "includes" [.undefLit]))
  == "true"
#guard outcome (expr (callOn (nums [1.0, 2.0]) "includes" [.numLit 1.0, .numLit 1.0])) == "false"
#guard outcome
    (expr (callOn (nums [1.0, 2.0]) "includes" [.numLit 1.0, .unary .neg (.numLit 2.0)]))
  == "true"
#guard outcome (expr (callOn (nums [1.0]) "includes" [.numLit 1.0, .ident "Infinity"])) == "false"
-- An empty receiver answers before `fromIndex` is coerced, so the
-- throwing `valueOf` never runs (23.1.3.16 step 3).
#guard outcome
    [ .varDecl .«const» [{ target := "poison", init := some (.objectLit
        [.init "valueOf" (.arrow [] (.block [.throwStmt (.new (.ident "Error") [])]))]) }],
      .exprStmt (callOn (.arrayLit []) "includes" [.undefLit, .ident "poison"]) ]
  == "false"
#guard outcome (expr (callOn (nums [1.0, 2.0, 1.0]) "indexOf" [.numLit 1.0])) == "0"
#guard outcome (expr (callOn (nums [1.0, 2.0, 1.0]) "lastIndexOf" [.numLit 1.0])) == "2"
#guard outcome
    (expr (callOn (nums [1.0, 2.0, 1.0]) "lastIndexOf" [.numLit 1.0, .unary .neg (.numLit 2.0)]))
  == "0"
#guard outcome
    (expr (callOn (nums [1.0]) "lastIndexOf" [.numLit 1.0, .unary .neg (.ident "Infinity")]))
  == "-1"
#guard outcome (expr (callOn (nums [1.0]) "indexOf" [.numLit 1.0, .numLit 5.0])) == "-1"
-- and is skipped for `indexOf`.
#guard outcome
    (expr (callOn (.call (.ident "Array") [.numLit 2.0]) "indexOf" [.undefLit])) == "-1"
#guard outcome (expr (protoCall "indexOf" [arrayLike, .strLit "b"])) == "1"

/-! ## `reverse` -/

#guard outcome (expr (callOn (callOn (nums [1.0, 2.0, 3.0]) "reverse" []) "join" []))
  == "3,2,1"
#guard outcome (expr (callOn (callOn (nums [1.0, 2.0]) "reverse" []) "join" [])) == "2,1"
-- A hole is swapped as a hole, not filled in: the element moves and the
-- key it left behind goes away.
#guard outcome
    [ .varDecl .«const» [{ target := "xs", init := some (.call (.ident "Array") [.numLit 2.0]) }],
      .exprStmt (.assign (.index (.ident "xs") (.numLit 0.0)) (.numLit 1.0)),
      .exprStmt (callOn (.ident "xs") "reverse" []),
      .exprStmt (.logical .and
        (callOn (.ident "xs") "hasOwnProperty" [.numLit 1.0])
        (.unary .not (callOn (.ident "xs") "hasOwnProperty" [.numLit 0.0]))) ]
  == "true"
-- It answers the receiver itself.
#guard outcome
    [ .varDecl .«const» [{ target := "xs", init := some (nums [1.0]) }],
      .exprStmt (.binary .strictEq (callOn (.ident "xs") "reverse" []) (.ident "xs")) ]
  == "true"

/-! ## `pop`, `shift`, and `unshift`

All three write `length` back when they are done, on an array and on an
array-like alike. -/

#guard outcome (expr (callOn (nums [1.0, 2.0]) "pop" [])) == "2"
#guard outcome (expr (callOn (.arrayLit []) "pop" [])) == "undefined"
#guard outcome
    [ .varDecl .«const» [{ target := "xs", init := some (nums [1.0, 2.0]) }],
      .exprStmt (callOn (.ident "xs") "pop" []),
      .exprStmt (.member (.ident "xs") "length") ]
  == "1"
#guard outcome (expr (callOn (nums [1.0, 2.0]) "shift" [])) == "1"
#guard outcome
    [ .varDecl .«const» [{ target := "xs", init := some (nums [1.0, 2.0, 3.0]) }],
      .exprStmt (callOn (.ident "xs") "shift" []),
      .exprStmt (callOn (.ident "xs") "join" []) ]
  == "2,3"
#guard outcome (expr (callOn (nums [2.0, 3.0]) "unshift" [.numLit 1.0])) == "3"
#guard outcome
    [ .varDecl .«const» [{ target := "xs", init := some (nums [2.0, 3.0]) }],
      .exprStmt (callOn (.ident "xs") "unshift" [.numLit 0.0, .numLit 1.0]),
      .exprStmt (callOn (.ident "xs") "join" []) ]
  == "0,1,2,3"
-- Generic: the array-like has its `length` written back too.
#guard outcome
    [ .varDecl .«const» [{ target := "o", init := some arrayLike }],
      .exprStmt (protoCall "pop" [.ident "o"]),
      .exprStmt (.member (.ident "o") "length") ]
  == "1"
#guard outcome (expr (protoCall "shift" [arrayLike])) == "a"
-- `shift` on a zero-length array-like still writes `length`.
#guard outcome
    [ .varDecl .«const» [{ target := "o", init := some (.objectLit []) }],
      .exprStmt (protoCall "shift" [.ident "o"]),
      .exprStmt (.member (.ident "o") "length") ]
  == "0"
-- The final `length` write is observable even with no argument at all.
#guard outcome
    (expr (callOn (.call (.member (.ident "Object") "freeze") [nums [1.0]]) "unshift" []))
  == "uncaught: TypeError: Cannot assign to read only property 'length' of object '#<Object>'"

/-! ## `splice`

23.1.3.31's `deleteCount` has three cases, and the second and third are
not the same: an *absent* one takes the whole tail where a *present*
`undefined` one is ToIntegerOrInfinity's 0. -/

#guard outcome (expr (.member (callOn (nums [1.0, 2.0]) "splice" [.numLit 0.0]) "length")) == "2"
#guard outcome
    (expr (.member (callOn (nums [1.0, 2.0]) "splice" [.numLit 0.0, .undefLit]) "length"))
  == "0"
#guard outcome
    (expr (callOn (callOn (nums [1.0, 2.0, 3.0]) "splice" [.numLit 1.0, .numLit 1.0]) "join" []))
  == "2"
#guard outcome
    [ .varDecl .«const» [{ target := "xs", init := some (nums [1.0, 2.0, 3.0]) }],
      .exprStmt (callOn (.ident "xs") "splice" [.numLit 1.0, .numLit 1.0]),
      .exprStmt (callOn (.ident "xs") "join" []) ]
  == "1,3"
-- Insert only: nothing is deleted and the tail moves up.
#guard outcome
    [ .varDecl .«const» [{ target := "xs", init := some (nums [1.0, 4.0]) }],
      .exprStmt (callOn (.ident "xs") "splice" [.numLit 1.0, .numLit 0.0,
        .numLit 2.0, .numLit 3.0]),
      .exprStmt (callOn (.ident "xs") "join" []) ]
  == "1,2,3,4"
-- Delete and insert at once, with a negative start.
#guard outcome
    [ .varDecl .«const» [{ target := "xs", init := some (nums [1.0, 2.0, 3.0]) }],
      .exprStmt (callOn (.ident "xs") "splice"
        [.unary .neg (.numLit 1.0), .numLit 1.0, .numLit 9.0]),
      .exprStmt (callOn (.ident "xs") "join" []) ]
  == "1,2,9"
-- `length` is written, so a shrink is visible.
#guard outcome
    [ .varDecl .«const» [{ target := "xs", init := some (nums [1.0, 2.0, 3.0]) }],
      .exprStmt (callOn (.ident "xs") "splice" [.numLit 1.0]),
      .exprStmt (.member (.ident "xs") "length") ]
  == "1"
-- The result is built by ArraySpeciesCreate, like `slice`'s and
-- `concat`'s.
#guard outcome
    [ .classDecl "A" { name := some "A", superClass := some (.ident "Array"), elements := [] },
      .exprStmt (.binary .instanceof
        (callOn (.new (.ident "A") [.numLit 1.0]) "splice" [.numLit 0.0]) (.ident "A")) ]
  == "true"
-- A frozen receiver refuses the `length` write.
#guard outcome
    (expr (callOn (.call (.member (.ident "Object") "freeze") [nums [1.0]]) "splice"
      [.numLit 0.0, .numLit 1.0]))
  == "uncaught: TypeError: Cannot delete property '0' of #<Object>"

/-! ## `fill` and `copyWithin` -/

#guard outcome (expr (callOn (callOn (nums [1.0, 2.0, 3.0]) "fill" [.numLit 0.0]) "join" []))
  == "0,0,0"
#guard outcome
    (expr (callOn (callOn (nums [1.0, 2.0, 3.0]) "fill"
      [.numLit 0.0, .numLit 1.0, .unary .neg (.numLit 1.0)]) "join" []))
  == "1,0,3"
#guard outcome
    [ .varDecl .«const» [{ target := "o", init := some (.objectLit [.init "length" (.numLit 2.0)]) }],
      .exprStmt (protoCall "fill" [.ident "o", .numLit 7.0]),
      .exprStmt (.index (.ident "o") (.numLit 1.0)) ]
  == "7"
-- The two directions of 23.1.3.4 step 13's overlap test.
#guard outcome
    (expr (callOn (callOn (nums [1.0, 2.0, 3.0, 4.0, 5.0]) "copyWithin"
      [.numLit 0.0, .numLit 3.0]) "join" []))
  == "4,5,3,4,5"
#guard outcome
    (expr (callOn (callOn (nums [1.0, 2.0, 3.0, 4.0, 5.0]) "copyWithin"
      [.numLit 1.0, .numLit 0.0]) "join" []))
  == "1,1,2,3,4"
-- A missing source deletes the target rather than writing `undefined`.
#guard outcome
    [ .varDecl .«const» [{ target := "xs", init := some (.call (.ident "Array") [.numLit 2.0]) }],
      .exprStmt (.assign (.index (.ident "xs") (.numLit 1.0)) (.numLit 2.0)),
      .exprStmt (callOn (.ident "xs") "copyWithin" [.numLit 1.0, .numLit 0.0]),
      .exprStmt (callOn (.ident "xs") "hasOwnProperty" [.numLit 1.0]) ]
  == "false"

/-! ## The surface itself

17.1's shape for every one of them, and 23.1.3's order for the prototype
— `length` first, since an array's own `length` sorts after its index
keys and `Array.prototype` has none. -/

#guard outcome (expr (.member (.member (.ident "Array") "prototype") "length")) == "0"
#guard outcome (expr (.member (protoMember "at") "length")) == "1"
#guard outcome (expr (.member (protoMember "copyWithin") "length")) == "2"
#guard outcome (expr (.member (protoMember "flat") "name")) == "flat"
#guard outcome (expr (.member (.member (.ident "Array") "of") "length")) == "0"
#guard outcome (expr (.member (.member (.ident "Array") "from") "length")) == "1"

#guard outcome
    (expr (callOn (.call (.member (.ident "Object") "getOwnPropertyNames")
      [.member (.ident "Array") "prototype"]) "join" []))
  == ("length,at,concat,constructor,copyWithin,entries,every,fill,filter,find,findIndex," ++
      "flat,flatMap,forEach,includes,indexOf,join,keys,lastIndexOf,map,pop,push,reduce," ++
      "reduceRight,reverse,shift,slice,some,sort,splice,toLocaleString,toString,unshift," ++
      "values")

-- ToObject is the first step of every one of them, so a nullish receiver
-- is its refusal.
#guard outcome (expr (protoCall "map" [.undefLit, .ident "String"]))
  == "uncaught: TypeError: Cannot convert undefined or null to object"
-- A string receiver is boxed by ToObject (#391's wrapper) and read
-- through its index keys, as 23.1.3's generic members have it.
#guard outcome (expr (.call (.member (protoCall "slice" [.strLit "ab"]) "join") []))
  == "a,b"
