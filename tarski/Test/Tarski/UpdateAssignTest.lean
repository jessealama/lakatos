import Tarski.Eval
import Tarski.Format

/-! `++`, `--`, compound assignment, and `void`.

All three read a target and then write it, and what they share is the
order they do it in. The target's *reference* is computed once — so a
computed key is evaluated once, not twice — the old value is read before
the right-hand side runs, and the write goes through the same dead-zone
and `const` checks a plain assignment does.

`++` and `--` coerce with ToNumeric, so `true++` is 2 and a missing
property steps to NaN. Compound assignment does not coerce to a number
first: `+=` is `+`, so a string operand concatenates. -/

open Tarski

/-- What the binary would print, so a case reads as its own stdout. -/
private def outcome (p : Program) : String :=
  match runScript p with
  | none => "<diverges>"
  | some (.error (.throw v), h) => s!"uncaught: {describeThrown h v}"
  | some (.error _, _) => "<abrupt>"
  | some (.ok none, _) => "<empty>"
  | some (.ok (some v), _) => formatValue v

private def num (x : Float) : Expr := .numLit x

/-- `let x = <value>;` -/
private def letX (value : Expr) : Stmt :=
  .varDecl .«let» [{ name := "x", init := some value }]

private def x : Expr := .ident "x"

/-! ## `++` and `--` on an identifier -/

-- `let x = 1; x++;` — the postfix form answers the old value.
#guard outcome [letX (num 1.0), .exprStmt (.update .inc false (.ident "x"))] == "1"

-- `let x = 1; x++; x;` — and leaves the new one behind.
#guard outcome
    [letX (num 1.0), .exprStmt (.update .inc false (.ident "x")), .exprStmt x] == "2"

-- `let x = 1; ++x;` — the prefix form answers the new value.
#guard outcome [letX (num 1.0), .exprStmt (.update .inc true (.ident "x"))] == "2"

-- `let x = 1; x--;` and `let x = 1; --x;`
#guard outcome [letX (num 1.0), .exprStmt (.update .dec false (.ident "x"))] == "1"
#guard outcome [letX (num 1.0), .exprStmt (.update .dec true (.ident "x"))] == "0"

-- `let b = true; b++; b;` — ToNumeric first, so a boolean becomes a
-- number and then steps.
#guard outcome
    [ .varDecl .«let» [{ name := "b", init := some (.boolLit true) }],
      .exprStmt (.update .inc false (.ident "b")),
      .exprStmt (.ident "b") ]
  == "2"

-- `let x = 1; x += 0 / 0; x++;` — NaN steps to NaN.
#guard outcome
    [ letX (.binary .div (num 0.0) (num 0.0)),
      .exprStmt (.update .inc true (.ident "x")) ]
  == "NaN"

-- `Infinity++` through a binding: the arithmetic is binary64, so it does
-- not move.
#guard outcome [letX (.ident "Infinity"), .exprStmt (.update .inc true (.ident "x"))]
  == "Infinity"

/-! ## The same checks a plain assignment makes -/

-- `const c = 1; c++;`
#guard outcome
    [ .varDecl .«const» [{ name := "c", init := some (num 1.0) }],
      .exprStmt (.update .inc false (.ident "c")) ]
  == "uncaught: TypeError: Assignment to constant variable."

-- `{ x++; let x = 1; }` — a write in the dead zone throws where the read
-- would have.
#guard outcome
    [.block [.exprStmt (.update .inc false (.ident "x")), letX (num 1.0)]]
  == "uncaught: ReferenceError: Cannot access 'x' before initialization"

-- `nope++;`
#guard outcome [.exprStmt (.update .inc false (.ident "nope"))]
  == "uncaught: ReferenceError: nope is not defined"

-- `NaN++` — the global value properties are not writable.
#guard outcome [.exprStmt (.update .inc false (.ident "NaN"))]
  == "uncaught: TypeError: Assignment to constant variable."

/-! ## `++` on a property, and the reference evaluated once -/

-- `const o = { n: 1 }; o.n++; o["n"];`
#guard outcome
    [ .varDecl .«const» [{ name := "o", init := some (.objectLit [.init "n" (num 1.0)]) }],
      .exprStmt (.update .inc false (.member (.ident "o") "n")),
      .exprStmt (.index (.ident "o") (.strLit "n")) ]
  == "2"

-- `const o = {}; o.p++;` — a missing property reads `undefined`, which
-- ToNumeric makes NaN.
#guard outcome
    [ .varDecl .«const» [{ name := "o", init := some (.objectLit []) }],
      .exprStmt (.update .inc true (.member (.ident "o") "p")) ]
  == "NaN"

-- `const xs = [0, 0]; let i = 0; xs[i++] = 5; i + ":" + xs[0];` — the
-- index expression runs once, so the write lands at 0 and `i` ends at 1.
#guard outcome
    [ .varDecl .«const» [{ name := "xs", init := some (.arrayLit [num 0.0, num 0.0]) }],
      .varDecl .«let» [{ name := "i", init := some (num 0.0) }],
      .exprStmt (.assign (.index (.ident "xs") (.update .inc false (.ident "i"))) (num 5.0)),
      .exprStmt
        (.binary .add
          (.binary .add (.ident "i") (.strLit ":"))
          (.index (.ident "xs") (num 0.0))) ]
  == "1:5"

-- `const xs = [1, 1]; let i = 0; xs[i++]++; i + ":" + xs[0] + ":" + xs[1];`
-- — and an update through a computed key evaluates that key once too.
#guard outcome
    [ .varDecl .«const» [{ name := "xs", init := some (.arrayLit [num 1.0, num 1.0]) }],
      .varDecl .«let» [{ name := "i", init := some (num 0.0) }],
      .exprStmt (.update .inc false (.index (.ident "xs") (.update .inc false (.ident "i")))),
      .exprStmt
        (.binary .add
          (.binary .add
            (.binary .add
              (.binary .add (.ident "i") (.strLit ":"))
              (.index (.ident "xs") (num 0.0)))
            (.strLit ":"))
          (.index (.ident "xs") (num 1.0))) ]
  == "1:2:1"

/-! ## The five compound operators -/

private def compound (op : BinaryOp) (start amount : Float) : String :=
  outcome [letX (num start), .exprStmt (.compoundAssign op (.ident "x") (num amount))]

#guard compound .add 1.0 2.0 == "3"
#guard compound .sub 1.0 1.0 == "0"
#guard compound .mul 2.0 3.0 == "6"
#guard compound .div 6.0 2.0 == "3"
#guard compound .rem 6.0 4.0 == "2"

-- `let s = "a"; s += 1; s;` — `+=` is `+`, so a string operand
-- concatenates rather than coercing to a number.
#guard outcome
    [ .varDecl .«let» [{ name := "s", init := some (.strLit "a") }],
      .exprStmt (.compoundAssign .add (.ident "s") (num 1.0)),
      .exprStmt (.ident "s") ]
  == "a1"

-- `let x = 1; x += (x = 2); x;` — 13.15.2's order: the left side is read
-- before the right side runs, so this is 3 and not 4.
#guard outcome
    [ letX (num 1.0),
      .exprStmt (.compoundAssign .add (.ident "x") (.assign (.ident "x") (num 2.0))),
      .exprStmt x ]
  == "3"

-- `const o = {}; o.p += 1;` — `undefined + 1` is NaN.
#guard outcome
    [ .varDecl .«const» [{ name := "o", init := some (.objectLit []) }],
      .exprStmt (.compoundAssign .add (.member (.ident "o") "p") (num 1.0)) ]
  == "NaN"

-- `const o = { n: 1 }; o.n += 2; o.n;`
#guard outcome
    [ .varDecl .«const» [{ name := "o", init := some (.objectLit [.init "n" (num 1.0)]) }],
      .exprStmt (.compoundAssign .add (.member (.ident "o") "n") (num 2.0)),
      .exprStmt (.member (.ident "o") "n") ]
  == "3"

-- `const c = 1; c += 1;` — the same `const` refusal.
#guard outcome
    [ .varDecl .«const» [{ name := "c", init := some (num 1.0) }],
      .exprStmt (.compoundAssign .add (.ident "c") (num 1.0)) ]
  == "uncaught: TypeError: Assignment to constant variable."

/-! ## `void` and the empty statement -/

-- `void 0 === undefined;`
#guard outcome
    [.exprStmt (.binary .strictEq (.unary .void (num 0.0)) .undefLit)] == "true"

-- `let n = 0; void n++; n;` — the operand is evaluated, and its value
-- dropped.
#guard outcome
    [ .varDecl .«let» [{ name := "n", init := some (num 0.0) }],
      .exprStmt (.unary .void (.update .inc false (.ident "n"))),
      .exprStmt (.ident "n") ]
  == "1"

-- `void {};` — the value is never coerced, so an object with no
-- `valueOf` does not throw where `+{}` would.
#guard outcome [.exprStmt (.unary .void (.objectLit []))] == "undefined"

-- `1; ;` — and the empty statement completes empty.
#guard outcome [.exprStmt (num 1.0), .empty] == "1"
