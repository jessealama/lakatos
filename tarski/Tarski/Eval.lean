import Js
import Tarski.Ast
import Tarski.Monad

/-! The evaluator: a definitional interpreter over `EvalM`.

Every primitive operation delegates to the `Js` library — the same
definitions `lakatos prove` proves against — and the evaluator adds only
dispatch. Nothing here is `partial` in Lean's sense: the recursion is
defined by `partial_fixpoint`, so the equations are theorems and a
non-terminating program is `none`, not an axiom.

The non-recursive helpers live outside the `mutual` block on purpose:
their equations are ordinary and `simp` may use them freely, while the
recursive equations — `evalWhile`'s above all — are unfolded one step at
a time with `rw`, never added to a simp set. -/

namespace Tarski

open Js

/-- Whether a declaration form produces writable bindings. -/
def DeclKind.isMutable : DeclKind → Bool
  | .«let» => true
  | .«const» => false

/-- ToNumber on this slice's values. Not `JsVal.toNumber`, whose wrong-tag
throw is the prover refusing a coercion rather than JS performing one:
here the coercion is the semantics. The three arms after `null` are
unreachable — no node kind in `Ast` builds a string, a bigint, or an
object — and #380 and #378 replace them with the real conversions. -/
def toNumberPrim : Value → Float
  | .prim (.num x) => x
  | .prim (.bool b) => if b then 1.0 else 0.0
  | .prim .undef => floatNaN
  | .prim .null => 0.0
  | .prim (.str _) => floatNaN
  | .prim (.bigint _) => floatNaN
  | .obj _ => floatNaN

/-- ToBoolean on this slice's values: total, and already correct for the
tags later slices add. -/
def toBooleanPrim : Value → Bool
  | .prim (.num x) => !(x == 0.0) && !x.isNaN
  | .prim (.bool b) => b
  | .prim .undef => false
  | .prim .null => false
  | .prim (.str s) => !s.isEmpty
  | .prim (.bigint i) => i != 0
  | .obj _ => true

/-- `===` on values: the library's test on primitives, reference identity
on objects, and `false` across the two. -/
def strictEqValue : Value → Value → Bool
  | .prim a, .prim b => JsVal.strictEq a b
  | .obj r₁, .obj r₂ => r₁ == r₂
  | .prim _, .obj _ => false
  | .obj _, .prim _ => false

/-- Apply a prefix operator to an evaluated operand. -/
def applyUnary : UnaryOp → Value → Value
  | .neg, v => .prim (.num (-(toNumberPrim v)))
  | .plus, v => .prim (.num (toNumberPrim v))
  | .not, v => .prim (.bool (!toBooleanPrim v))

/-- Apply an infix operator to its two evaluated operands, left first.
`+` is numeric addition, which is all it can be here: no operand this
slice can build is a string. `%` is the library's `tsRem` — C `fmod`,
not the IEEE remainder — and the relations are the library's binary64
order, so a NaN operand answers `false` on all four. -/
def applyBinary : BinaryOp → Value → Value → Value
  | .add, l, r => .prim (.num (toNumberPrim l + toNumberPrim r))
  | .sub, l, r => .prim (.num (toNumberPrim l - toNumberPrim r))
  | .mul, l, r => .prim (.num (toNumberPrim l * toNumberPrim r))
  | .div, l, r => .prim (.num (toNumberPrim l / toNumberPrim r))
  | .rem, l, r => .prim (.num (Number.FloatOps.tsRem (toNumberPrim l) (toNumberPrim r)))
  | .lt, l, r => .prim (.bool (Float.lt (toNumberPrim l) (toNumberPrim r)))
  | .le, l, r => .prim (.bool (Float.le (toNumberPrim l) (toNumberPrim r)))
  | .gt, l, r => .prim (.bool (Float.lt (toNumberPrim r) (toNumberPrim l)))
  | .ge, l, r => .prim (.bool (Float.le (toNumberPrim r) (toNumberPrim l)))
  | .strictEq, l, r => .prim (.bool (strictEqValue l r))
  | .strictNe, l, r => .prim (.bool (!strictEqValue l r))

/-- UpdateEmpty: a statement that completes empty leaves the running
completion value alone. -/
def updateEmpty (acc : Option Value) : Option Value → Option Value
  | some v => some v
  | none => acc

/-- `undefined`, the value `if` and `while` complete with when their body
produced none. Both statements start from it rather than from empty —
`eval("1; if (true) {}")` is `undefined`, not `1` — while a block that
runs nothing completes empty and leaves the previous value standing. -/
def undefValue : Value := .prim .undef

mutual

/-- Evaluate an expression. -/
def evalExpr (env : Env) : Expr → EvalM Value
  | .numLit x => pure (.prim (.num x))
  | .boolLit b => pure (.prim (.bool b))
  | .undefLit => pure (.prim .undef)
  | .nullLit => pure (.prim .null)
  | .ident name =>
    match Env.lookup env name with
    | some r => do
      let cell ← readCell r
      pure cell.value
    | none => throwJsError "ReferenceError"
  | .unary op operand => do
    let v ← evalExpr env operand
    pure (applyUnary op v)
  | .binary op left right => do
    let l ← evalExpr env left
    let r ← evalExpr env right
    pure (applyBinary op l r)
  | .cond test consequent alternate => do
    let t ← evalExpr env test
    if toBooleanPrim t then evalExpr env consequent else evalExpr env alternate
  | .assign target value => do
    let v ← evalExpr env value
    match Env.lookup env target with
    | some r => do
      let cell ← readCell r
      if cell.mutable then do
        writeCell r v
        pure v
      else
        throwJsError "TypeError"
    | none => throwJsError "ReferenceError"
  partial_fixpoint

/-- Evaluate a statement, answering the environment it leaves behind and
its completion value. Only a declaration grows the environment; a block
and a loop body run in one of their own, which does not escape. -/
def evalStmt (env : Env) : Stmt → EvalM (Env × Option Value)
  | .exprStmt value => do
    let v ← evalExpr env value
    pure (env, some v)
  | .varDecl kind declarators => do
    let env' ← evalDeclarators env kind declarators
    pure (env', none)
  | .ifStmt test consequent alternate => do
    let t ← evalExpr env test
    if toBooleanPrim t then do
      let (_, v) ← evalStmt env consequent
      pure (env, updateEmpty (some undefValue) v)
    else
      match alternate with
      | some s => do
        let (_, v) ← evalStmt env s
        pure (env, updateEmpty (some undefValue) v)
      | none => pure (env, some undefValue)
  | .whileStmt test body => do
    -- The loop's running value starts at `undefined`, not at empty, so a
    -- loop whose body never runs still completes with a value.
    let v ← evalWhile env test body (some undefValue)
    pure (env, v)
  | .block body => do
    let (_, v) ← evalStmts env body none
    pure (env, v)
  partial_fixpoint

/-- Bind a declaration's declarators left to right, each initializer
seeing the ones before it. A `let` without an initializer binds
`undefined`. -/
def evalDeclarators (env : Env) (kind : DeclKind) : List Declarator → EvalM Env
  | [] => pure env
  | d :: rest => do
    let v ← match d.init with
      | some e => evalExpr env e
      | none => pure (.prim .undef)
    let r ← allocCell { mutable := kind.isMutable, value := v }
    evalDeclarators ((d.name, r) :: env) kind rest
  partial_fixpoint

/-- Run a statement list, threading the environment and the running
completion value. -/
def evalStmts (env : Env) : List Stmt → Option Value → EvalM (Env × Option Value)
  | [], acc => pure (env, acc)
  | s :: rest, acc => do
    let (env', v) ← evalStmt env s
    evalStmts env' rest (updateEmpty acc v)
  partial_fixpoint

/-- Run a `while`. The loop is the one definition whose unfolding is a
proof step: `rw [evalWhile]` exposes exactly one iteration, and a
postcondition is proved by doing that until the test fails. -/
def evalWhile (env : Env) (test : Expr) (body : Stmt) (acc : Option Value) :
    EvalM (Option Value) := do
  let t ← evalExpr env test
  if toBooleanPrim t then do
    let (_, v) ← evalStmt env body
    evalWhile env test body (updateEmpty acc v)
  else
    pure acc
  partial_fixpoint

end

/-- Run a whole script from the empty environment and the empty heap. -/
def evalProgram (p : Program) : EvalM (Option Value) := do
  let (_, v) ← evalStmts [] p none
  pure v

/-- A script's observable outcome: `none` is divergence, `.error` an
uncaught abrupt completion, `.ok` the script's completion value (`none`
when no statement produced one). The heap is dropped: nothing outside
the evaluator can name a cell. -/
def runProgram (p : Program) : Option (Except Completion (Option Value)) :=
  match ((evalProgram p).run Heap.empty).run with
  | none => none
  | some (.error c) => some (.error c)
  | some (.ok (v, _)) => some (.ok v)

end Tarski
