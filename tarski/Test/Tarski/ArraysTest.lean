import Tarski.Eval
import Tarski.Format

/-! Arrays: literals, the live `length`, index reads and writes, `push`,
`join`, `Array.isArray`, and the `Array` constructor.

An array is an ordinary object tagged `ObjKind.array length`. Its
elements are index-keyed own properties, so a hole is simply a key that
is not there, and its `length` lives in the tag, so `Object.keys` never
lists it and truncation is one write. What that buys is pinned below:
`xs[5] = 1` on an empty array makes `length` 6 without making five
properties, and `xs.length = 1` drops what it passes.

`push` and `join` are **generic over an array-like**, as 23.1.3 has every
member of `Array.prototype`: the receiver goes through ToObject, its
length through LengthOfArrayLike, and the elements through `getProp` and
`setProp`. The rest of the prototype is
`Test/Tarski/ArrayBuiltinsTest.lean`'s and
`Test/Tarski/ArrayIterationTest.lean`'s. -/

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

/-- `const xs = <init>;` -/
private def declareXs (init : Expr) : Stmt :=
  .varDecl .«const» [{ target := "xs", init := some init }]

/-- An array literal of number literals. -/
private def nums (xs : List Float) : Expr := .arrayLit (xs.map (.numLit ·))

/-- `xs.<name>(<args>)`. -/
private def callOnXs (name : String) (args : List Expr) : Expr :=
  .call (.member (.ident "xs") name) args

/-! ## The issue's example

```js
"use strict";
const xs = [1, 2];
xs.push(3);
const s = "n=" + xs.length + ":" + xs.join(",");
s === "n=3:1,2,3" && "a" < "b" && Array.isArray(xs) && Object.is(-0, -0) && !Object.is(0, -0);
```
-/

/-- `-0`, which is `Object.is`'s whole point. -/
private def negZero : Expr := .unary .neg (.numLit 0.0)

#guard outcome
    [ declareXs (nums [1.0, 2.0]),
      .exprStmt (callOnXs "push" [.numLit 3.0]),
      .varDecl .«const» [{ target := "s", init := some (.binary .add
        (.binary .add
          (.binary .add (.strLit "n=") (.member (.ident "xs") "length"))
          (.strLit ":"))
        (callOnXs "join" [.strLit ","])) }],
      .exprStmt (.logical .and
        (.logical .and
          (.logical .and
            (.logical .and
              (.binary .strictEq (.ident "s") (.strLit "n=3:1,2,3"))
              (.binary .lt (.strLit "a") (.strLit "b")))
            (.call (.member (.ident "Array") "isArray") [.ident "xs"]))
          (.call (.member (.ident "Object") "is") [negZero, negZero]))
        (.unary .not (.call (.member (.ident "Object") "is") [.numLit 0.0, negZero]))) ]
  == "true"

/-! ## Literals and `length` -/

-- `[].length;`
#guard outcome (expr (.member (.arrayLit []) "length")) == "0"

-- `[1, 2, 3].length;`
#guard outcome (expr (.member (nums [1.0, 2.0, 3.0]) "length")) == "3"

-- `[1, 2, 3][1];`
#guard outcome (expr (.index (nums [1.0, 2.0, 3.0]) (.numLit 1.0))) == "2"

-- `typeof [];`
#guard outcome (expr (.unary .typeof (.arrayLit []))) == "object"

/-! ## An index write past the end grows `length`

The acceptance criterion: a write at 5 on an empty array makes `length`
6 and leaves 0 through 4 absent, so `Object.keys` has one entry. -/

-- `const xs = []; xs[5] = 1; xs.length;`
#guard outcome
    [ declareXs (.arrayLit []),
      .exprStmt (.assign (.index (.ident "xs") (.numLit 5.0)) (.numLit 1.0)),
      .exprStmt (.member (.ident "xs") "length") ]
  == "6"

-- `const xs = []; xs[5] = 1; xs[2];`
#guard outcome
    [ declareXs (.arrayLit []),
      .exprStmt (.assign (.index (.ident "xs") (.numLit 5.0)) (.numLit 1.0)),
      .exprStmt (.index (.ident "xs") (.numLit 2.0)) ]
  == "undefined"

-- `const xs = []; xs[5] = 1; Object.keys(xs).join();`
#guard outcome
    [ declareXs (.arrayLit []),
      .exprStmt (.assign (.index (.ident "xs") (.numLit 5.0)) (.numLit 1.0)),
      .exprStmt (.call (.member
        (.call (.member (.ident "Object") "keys") [.ident "xs"]) "join") []) ]
  == "5"

-- `const xs = ["a"]; xs[2] = "c"; xs.join();` — the hole joins as empty.
#guard outcome
    [ declareXs (.arrayLit [.strLit "a"]),
      .exprStmt (.assign (.index (.ident "xs") (.numLit 2.0)) (.strLit "c")),
      .exprStmt (callOnXs "join" []) ]
  == "a,,c"

-- `const xs = []; xs["1"] = 1; xs.length;` — a canonical index under its
-- string spelling is still an index.
#guard outcome
    [ declareXs (.arrayLit []),
      .exprStmt (.assign (.index (.ident "xs") (.strLit "1")) (.numLit 1.0)),
      .exprStmt (.member (.ident "xs") "length") ]
  == "2"

-- `const xs = []; xs["01"] = 1; xs.length;` — and a non-canonical one is
-- an ordinary key, which does not grow anything.
#guard outcome
    [ declareXs (.arrayLit []),
      .exprStmt (.assign (.index (.ident "xs") (.strLit "01")) (.numLit 1.0)),
      .exprStmt (.member (.ident "xs") "length") ]
  == "0"

/-! ## Writing `length`

Shortening drops the elements it passes; growing adds none. Anything
that is not a uint32 is a `RangeError`; `"2"` is one, ToNumber of a
string being StringToNumber, so it truncates like the number. -/

/-- `const xs = ["a", "b", "c"]; xs.length = <v>; <then>;` -/
private def setLength (v : Expr) (thenExpr : Expr) : Program :=
  [ declareXs (.arrayLit [.strLit "a", .strLit "b", .strLit "c"]),
    .exprStmt (.assign (.member (.ident "xs") "length") v),
    .exprStmt thenExpr ]

#guard outcome (setLength (.numLit 1.0) (callOnXs "join" [])) == "a"
#guard outcome (setLength (.numLit 1.0) (.member (.ident "xs") "length")) == "1"
#guard outcome (setLength (.numLit 1.0)
    (.member (.call (.member (.ident "Object") "keys") [.ident "xs"]) "length")) == "1"
#guard outcome (setLength (.numLit 5.0) (.member (.ident "xs") "length")) == "5"
#guard outcome (setLength (.numLit 5.0) (callOnXs "join" [])) == "a,b,c,,"
#guard outcome (setLength (.unary .neg (.numLit 1.0)) (.numLit 0.0))
  == "uncaught: RangeError: Invalid array length"
#guard outcome (setLength (.numLit 2.5) (.numLit 0.0))
  == "uncaught: RangeError: Invalid array length"
#guard outcome (setLength (.strLit "2") (callOnXs "join" [])) == "a,b"

/-! ## `push` -/

-- `const xs = []; xs.push(1);` — the answer is the new length.
#guard outcome [declareXs (.arrayLit []), .exprStmt (callOnXs "push" [.numLit 1.0])] == "1"

-- `const xs = []; xs.push(1, 2); xs.join();`
#guard outcome
    [ declareXs (.arrayLit []),
      .exprStmt (callOnXs "push" [.numLit 1.0, .numLit 2.0]),
      .exprStmt (callOnXs "join" []) ]
  == "1,2"

-- `const xs = []; xs.push(1, 2);`
#guard outcome
    [declareXs (.arrayLit []), .exprStmt (callOnXs "push" [.numLit 1.0, .numLit 2.0])] == "2"

-- `const xs = ["a"]; xs.push();` — no argument, so the length stands.
#guard outcome [declareXs (.arrayLit [.strLit "a"]), .exprStmt (callOnXs "push" [])] == "1"

/-! ### `push` on an array-like

23.1.3.23 is generic: a plain object with a `length` takes the write and
has its `length` written back. -/

/-- `const o = {}; o.push = Array.prototype.push; o.push(1); <tail>` -/
private def pushOnPlainObject (tail : Expr) : Program :=
  [ .varDecl .«const» [{ target := "o", init := some (.objectLit []) }],
    .exprStmt (.assign (.member (.ident "o") "push")
      (.member (.member (.ident "Array") "prototype") "push")),
    .exprStmt (.call (.member (.ident "o") "push") [.numLit 1.0]),
    .exprStmt tail ]

-- An absent `length` is ToLength of `undefined`, which is 0, so the one
-- element lands at `0` and `length` is written back as 1.
#guard outcome (pushOnPlainObject (.member (.ident "o") "length")) == "1"
#guard outcome (pushOnPlainObject (.index (.ident "o") (.numLit 0.0))) == "1"

-- A `length` already past 2^53 - 1 refuses before anything is written
-- (23.1.3.23 step 4).
#guard outcome
    [ .varDecl .«const» [{ target := "o", init := some (.objectLit
        [.init "length" (.numLit 9007199254740991.0)]) }],
      .exprStmt (.assign (.member (.ident "o") "push")
        (.member (.member (.ident "Array") "prototype") "push")),
      .exprStmt (.call (.member (.ident "o") "push") [.numLit 1.0]) ]
  == "uncaught: TypeError: Array length exceeds 2**53 - 1"

-- The final `length` write is observable: a frozen array refuses a
-- zero-argument `push`, which an engine does too.
#guard outcome
    [ declareXs (.call (.member (.ident "Object") "freeze") [nums [1.0]]),
      .exprStmt (callOnXs "push" []) ]
  == "uncaught: TypeError: Cannot assign to read only property 'length' of object '#<Object>'"

-- A string receiver is boxed by ToObject (#391's wrapper), and a String
-- exotic object's `length` is not writable, so `push`'s final write is
-- what refuses rather than ToObject.
#guard outcome
    (expr (.call (.member (.member (.member (.ident "Array") "prototype") "push") "call")
      [.strLit "abc"]))
  == "uncaught: TypeError: Cannot assign to read only property 'length' of object '#<Object>'"

/-! ## `join`

The acceptance criterion includes the empty array, which joins to the
empty string. `undefined` and `null` elements contribute nothing; every
other element is ToString'd, which for a nested array is
`Array.prototype.toString` and so that array's own `join`. -/

#guard outcome (expr (.call (.member (.arrayLit []) "join") [])) == ""
#guard outcome (expr (.call (.member (nums [1.0, 2.0]) "join") [])) == "1,2"
#guard outcome (expr (.call (.member (nums [1.0, 2.0]) "join") [.strLit "-"])) == "1-2"
#guard outcome (expr (.call (.member (nums [1.0, 2.0]) "join") [.strLit ""])) == "12"
#guard outcome (expr (.call (.member (.arrayLit [.undefLit, .nullLit, .numLit 1.0]) "join") []))
  == ",,1"
#guard outcome
    (expr (.call (.member (.arrayLit [.strLit "a", .boolLit true, .numLit 2.5]) "join")
      [.strLit " "]))
  == "a true 2.5"
-- A nested array's ToString is `Array.prototype.toString`, which is its
-- own `join`.
#guard outcome (expr (.call (.member (.arrayLit [nums [1.0]]) "join") [])) == "1"

-- `Array.prototype.join.call({ length: 2, 0: "a", 1: "b" });` — generic
-- over an array-like, as 23.1.3.18 has it.
#guard outcome
    (expr (.call (.member (.member (.member (.ident "Array") "prototype") "join") "call")
      [.objectLit [.init "length" (.numLit 2.0), .init "0" (.strLit "a"), .init "1" (.strLit "b")]]))
  == "a,b"

/-! ## `Array.isArray` -/

/-- `Array.isArray(<arg>);` -/
private def isArray (e : Expr) : Program :=
  expr (.call (.member (.ident "Array") "isArray") [e])

#guard outcome (isArray (.arrayLit [])) == "true"
#guard outcome (isArray (.objectLit [])) == "false"
#guard outcome (isArray (.numLit 1.0)) == "false"
#guard outcome (isArray (.strLit "a")) == "false"
-- `Array.prototype` is itself an array, as the spec has it.
#guard outcome (isArray (.member (.ident "Array") "prototype")) == "true"

/-! ## The `Array` constructor

One Number argument is a length, not an element. `new` and a plain call
build the same thing: `Array` allocates its own instance either way, and
NewTarget's `prototype` is ignored until subclassing (#384). -/

#guard outcome (expr (.member (.call (.ident "Array") []) "length")) == "0"
#guard outcome (expr (.member (.call (.ident "Array") [.numLit 3.0]) "length")) == "3"
#guard outcome (expr (.member (.new (.ident "Array") [.numLit 2.0]) "length")) == "2"
#guard outcome (expr (.call (.member (.call (.ident "Array") [.numLit 1.0, .numLit 2.0]) "join") []))
  == "1,2"
#guard outcome (expr (.member (.call (.ident "Array") [.strLit "3"]) "length")) == "1"
#guard outcome (expr (.call (.ident "Array") [.unary .neg (.numLit 1.0)]))
  == "uncaught: RangeError: Invalid array length"

/-! ## An array's place in the object graph -/

-- `[] instanceof Array;`
#guard outcome (expr (.binary .instanceof (.arrayLit []) (.ident "Array"))) == "true"

-- `[] instanceof Object;` — `Array.prototype` chains to
-- `Object.prototype`.
#guard outcome (expr (.binary .instanceof (.arrayLit []) (.ident "Object"))) == "true"

-- `[].constructor === Array;`
#guard outcome
    (expr (.binary .strictEq (.member (.arrayLit []) "constructor") (.ident "Array")))
  == "true"

-- `typeof Array;`
#guard outcome (expr (.unary .typeof (.ident "Array"))) == "function"
