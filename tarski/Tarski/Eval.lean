import Js
import Tarski.Ast
import Tarski.Monad
import Tarski.Format

/-! The evaluator: a definitional interpreter over `EvalM`.

Every primitive operation delegates to the `Js` library — the same
definitions `lakatos prove` proves against — and the evaluator adds only
dispatch. Nothing here is `partial` in Lean's sense: the recursion is
defined by `partial_fixpoint`, so the equations are theorems and a
non-terminating program is `none`, not an axiom.

The non-recursive helpers live outside the `mutual` block on purpose:
their equations are ordinary and `simp` may use them freely. Two of the
recursive ones are never added to a simp set and are unfolded one step at
a time with `rw`: `evalWhile` and `getProp`. The rule is not "recursive"
but "recursive on something other than syntax" — `evalExpr` and its
neighbours recurse on a concrete AST, which runs out, while a loop
recurses until a heap value says stop and a prototype walk until a heap
link does, and `simp` unfolds both under a binder it has not resolved,
forever. What decides membership in the block is
whether a definition can reach user code: `getProp` and `toPrimitive` can
(a prototype chain is unbounded, and ToPrimitive calls `valueOf`), so
they are inside; `instantiateBlock` and `makeFunction` only touch the
heap, so they are outside.

A block's declarations are instantiated before its first statement runs.
That is one mechanism answering three needs: the temporal dead zone (a
cell exists but holds nothing until its declarator runs), a function
declaration callable above its own text, and two declarations that call
each other.

## The messages the evaluator raises

Every runtime error the evaluator itself throws is here, verbatim,
V8-shaped where that was free. test262 never inspects a message; the
table exists so the tests can pin what the binary prints, and so that a
new refusal is written against a list rather than invented.

| Situation                                         | Class            | Message                                                     |
| ------------------------------------------------- | ---------------- | ----------------------------------------------------------- |
| a name that resolves nowhere                       | `ReferenceError` | `{name} is not defined`                                      |
| a read or write in the temporal dead zone          | `ReferenceError` | `Cannot access '{name}' before initialization`               |
| assignment to a `const`                            | `TypeError`      | `Assignment to constant variable.`                           |
| calling a non-function                             | `TypeError`      | `not a function`                                             |
| `new` on anything without `[[Construct]]`          | `TypeError`      | `not a constructor`                                          |
| a property read on `undefined` or `null`           | `TypeError`      | `Cannot read properties of {undefined|null} (reading '{key}')` |
| a property write on a primitive                    | `TypeError`      | `Cannot set properties of {base} (setting '{key}')`          |
| ToPrimitive with no primitive to give              | `TypeError`      | `Cannot convert object to primitive value`                   |
| `instanceof` a non-callable                        | `TypeError`      | `Right-hand side of 'instanceof' is not callable`            |
| `instanceof` a function with a non-object prototype | `TypeError`     | `Function has non-object prototype in instanceof check`      |
| `Error.prototype.toString` on a primitive          | `TypeError`      | `Error.prototype.toString called on non-object`              |

`Tarski/Monad.lean` holds two more, for the two arms a reference the
evaluator handed out cannot reach. -/

namespace Tarski

open Js

/-- Whether a declaration form produces writable bindings. -/
def DeclKind.isMutable : DeclKind → Bool
  | .«let» => true
  | .«const» => false

/-- ToNumber on primitives. Not `JsVal.toNumber`, whose wrong-tag throw
is the prover refusing a coercion rather than JS performing one: here the
coercion is the semantics. An object never reaches this — ToPrimitive
runs first — and the `str` arm is a placeholder until #380 gives strings
their real conversion. -/
def toNumberPrim : JsVal → Float
  | .num x => x
  | .bool b => if b then 1.0 else 0.0
  | .undef => floatNaN
  | .null => 0.0
  | .str _ => floatNaN
  | .bigint _ => floatNaN

/-- ToBoolean, which is total and never calls user code, so it takes a
whole `Value`: every object is truthy. NaN is the one binary64 value
unequal to itself, which is how the number arm rejects it — the library
models `Number` by Lean's own `Float`, and neither it nor Lean names an
`isNaN` the arithmetic boundary would allow here. -/
def toBooleanPrim : Value → Bool
  | .prim (.num x) => !(x == 0.0) && x == x
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

/-- The eight spellings `typeof` answers with. The library's
`TypeofResult` is a closed enum with no string in it, because a proof
compares tags; a script compares strings. -/
def typeofName : TypeofResult → String
  | .number => "number"
  | .string => "string"
  | .bigint => "bigint"
  | .boolean => "boolean"
  | .undefined => "undefined"
  | .object => "object"
  | .function => "function"
  | .symbol => "symbol"

/-- Apply a prefix operator to an operand ToPrimitive has already run
on. `not` and `typeof` never coerce, so `evalExpr` answers them before
reaching here; the arms are still written out, because a total function
of the operator is easier to reason about than a partial one. -/
def applyUnary : UnaryOp → JsVal → Value
  | .neg, v => .prim (.num (-(toNumberPrim v)))
  | .plus, v => .prim (.num (toNumberPrim v))
  | .not, v => .prim (.bool (!toBooleanPrim (.prim v)))
  | .typeof, v => .prim (.str (typeofName v.typeof))

/-- Apply a coercing infix operator to its two operands, both of which
ToPrimitive has already run on, left first. `+` is numeric addition,
which is all it can be until #380 gives strings concatenation. `%` is the
library's `tsRem` — C `fmod`, not the IEEE remainder — and the relations
are Lean's binary64 order, which is the library's model of it, so a NaN
operand answers `false` on all four. -/
def applyBinary : BinaryOp → JsVal → JsVal → Value
  | .add, l, r => .prim (.num (toNumberPrim l + toNumberPrim r))
  | .sub, l, r => .prim (.num (toNumberPrim l - toNumberPrim r))
  | .mul, l, r => .prim (.num (toNumberPrim l * toNumberPrim r))
  | .div, l, r => .prim (.num (toNumberPrim l / toNumberPrim r))
  | .rem, l, r => .prim (.num (Number.FloatOps.tsRem (toNumberPrim l) (toNumberPrim r)))
  | .lt, l, r => .prim (.bool (decide (toNumberPrim l < toNumberPrim r)))
  | .le, l, r => .prim (.bool (decide (toNumberPrim l ≤ toNumberPrim r)))
  | .gt, l, r => .prim (.bool (decide (toNumberPrim r < toNumberPrim l)))
  | .ge, l, r => .prim (.bool (decide (toNumberPrim r ≤ toNumberPrim l)))
  | .strictEq, l, r => .prim (.bool (strictEqValue (.prim l) (.prim r)))
  | .strictNe, l, r => .prim (.bool (!strictEqValue (.prim l) (.prim r)))

/-- The two strict-equality operators, which answer on whole values:
neither coerces, so an object operand is compared by identity and is
never handed to ToPrimitive. -/
def applyStrict : BinaryOp → Value → Value → Value
  | .strictNe, l, r => .prim (.bool (!strictEqValue l r))
  | _, l, r => .prim (.bool (strictEqValue l r))

/-- Whether a `continue` is this loop's. An unlabelled one always is —
the innermost loop catches it — and a labelled one is exactly when the
label is among those the loop was reached through. -/
def loopContinues (labels : List String) : Option String → Bool
  | none => true
  | some l => labels.contains l

/-- Put a reified completion back into the monad: the answer `attempt`
gave, resumed. -/
def liftCompletion : Except Completion (Option Value) → EvalM (Option Value)
  | .ok v => pure v
  | .error c => throwCompletion c

/-- `undefined`, the value `if` and `while` complete with when their body
produced none, a missing argument binds to, and a `return` without an
argument carries. Both statements start from it rather than from empty —
`eval("1; if (true) {}")` is `undefined`, not `1` — while a block that
runs nothing completes empty and leaves the previous value standing. -/
def undefValue : Value := .prim .undef

/-- The name an ordinary call's receiver is bound under. `this` is a
keyword, so no identifier can collide with it, and a binding in the scope
chain is exactly what the spec means by an environment record's
`[[ThisBindingStatus]]`. An arrow pushes no such binding, so `this`
inside one resolves outward like any other name. -/
def thisName : String := "this"

/-- Whether a value is a function: an object with a `[[Call]]`. -/
def isCallable (v : Value) : EvalM Bool := do
  match v with
  | .prim _ => pure false
  | .obj r => pure (← readObj r).callable.isSome

/-- `typeof`'s answer. The object case is the only one needing the heap,
which is why this is not `applyUnary`'s job. -/
def typeofValue (v : Value) : EvalM String := do
  match v with
  | .prim p => pure (typeofName p.typeof)
  | .obj r => pure (if (← readObj r).callable.isSome then "function" else "object")

/-- Allocate a function object. An ordinary function also gets a fresh
`prototype` object whose `constructor` points back at it, which is what
`new` links an instance to; an arrow gets neither, because it cannot be
constructed. The function object's own `[[Prototype]]` stays null until
`Function.prototype` exists (#389). -/
def makeFunction (c : Closure) : EvalM Value := do
  let f ← allocObj { callable := some (.closure c) }
  match c.kind with
  | .arrow => pure (.obj f)
  | .ordinary => do
    let proto ← allocObj { properties := [("constructor", .obj f)] }
    modifyObj f (fun o => o.setOwn "prototype" (.obj proto))
    pure (.obj f)

/-- Bind a call's arguments to its parameters, positionally: a missing
argument is `undefined` and an extra one is dropped. Parameters are
plain identifiers here, so nothing evaluates — defaults are #393's and
patterns #394's. Every parameter is mutable. -/
def bindParams (env : Env) : List String → List Value → EvalM Env
  | [], _ => pure env
  | p :: ps, args => do
    let (v, rest) := match args with
      | [] => (undefValue, ([] : List Value))
      | a :: as => (a, as)
    let r ← allocCell { mutable := true, value := some v }
    bindParams ((p, r) :: env) ps rest

/-- Pass one of block instantiation: a cell per declared name, holding
nothing. A `let` or `const` cell stays uninitialized until its declarator
runs, which is the temporal dead zone; a function declaration's is filled
in by pass two. -/
def hoistDeclarators (env : Env) (mutable : Bool) : List Declarator → EvalM Env
  | [] => pure env
  | d :: rest => do
    let r ← allocCell { mutable }
    hoistDeclarators ((d.name, r) :: env) mutable rest

/-- Pass one over a statement list's direct statements. Nested blocks are
not descended into: each has its own scope and instantiates itself. -/
def hoistNames (env : Env) : List Stmt → EvalM Env
  | [] => pure env
  | s :: rest => do
    let env' ← match s with
      | .varDecl kind declarators => hoistDeclarators env kind.isMutable declarators
      | .funcDecl name _ _ => do
        let r ← allocCell { mutable := true }
        pure ((name, r) :: env)
      | _ => pure env
    hoistNames env' rest

/-- Pass two: every function declaration's object, built in the finished
environment and stored in the cell pass one allocated. Building them all
against the same environment is what lets two declarations call each
other, and what lets one be called above its own text. -/
def initFunctions (env : Env) : List Stmt → EvalM Unit
  | [] => pure ()
  | s :: rest => do
    match s with
    | .funcDecl name params body => do
      let f ← makeFunction { params, body, env, kind := .ordinary }
      match Env.lookup env name with
      | some r => initCell r f
      | none => pure ()
    | _ => pure ()
    initFunctions env rest

/-- BlockDeclarationInstantiation over what this slice declares. Run
before a statement list's first statement, and the only thing that grows
an environment — which is why `evalStmt` does not answer one. -/
def instantiateBlock (env : Env) (body : List Stmt) : EvalM Env := do
  let env' ← hoistNames env body
  initFunctions env' body
  pure env'

/-- Set a property. Strict mode throughout, so a primitive base is a
`TypeError` rather than a silent no-op. Outside the fixpoint block
because nothing it does can reach user code: there are no writability
checks and no prototype-chain setters, and descriptors and accessors are
#389's, which is when this joins `getProp` inside. -/
def setProp (base : Value) (key : String) (v : Value) : EvalM Unit :=
  match base with
  | .obj r => modifyObj r (fun o => o.setOwn key v)
  | .prim _ =>
    throwJsError .typeError
      s!"Cannot set properties of {formatValue base} (setting '{key}')"

mutual

/-- Evaluate an expression. -/
def evalExpr (env : Env) : Expr → EvalM Value
  | .numLit x => pure (.prim (.num x))
  | .strLit s => pure (.prim (.str s))
  | .boolLit b => pure (.prim (.bool b))
  | .undefLit => pure (.prim .undef)
  | .nullLit => pure (.prim .null)
  | .ident name =>
    match Env.lookup env name with
    | some r => readCell name r
    | none => throwJsError .referenceError s!"{name} is not defined"
  | .this =>
    -- No global object yet, so an unbound `this` is `undefined` rather
    -- than a `ReferenceError`: #381 gives the top level a receiver.
    match Env.lookup env thisName with
    | some r => readCell thisName r
    | none => pure undefValue
  | .unary op operand =>
    match op with
    | .not => do
      let v ← evalExpr env operand
      pure (.prim (.bool (!toBooleanPrim v)))
    | .typeof => do
      let v ← evalExpr env operand
      pure (.prim (.str (← typeofValue v)))
    | _ => do
      let v ← evalExpr env operand
      pure (applyUnary op (← toPrimitive v))
  | .binary op left right => do
    let l ← evalExpr env left
    let r ← evalExpr env right
    if op.coerces then do
      let lp ← toPrimitive l
      let rp ← toPrimitive r
      pure (applyBinary op lp rp)
    else
      pure (applyStrict op l r)
  | .logical op left right => do
    -- Short-circuiting: the answer is one of the operands, never a
    -- boolean of its own, and the right one may not run at all.
    let l ← evalExpr env left
    match op with
    | .and => if toBooleanPrim l then evalExpr env right else pure l
    | .or => if toBooleanPrim l then pure l else evalExpr env right
  | .cond test consequent alternate => do
    let t ← evalExpr env test
    if toBooleanPrim t then evalExpr env consequent else evalExpr env alternate
  | .member object name => do
    let o ← evalExpr env object
    getProp o name
  | .index object key => do
    let o ← evalExpr env object
    let k ← evalExpr env key
    getProp o (← toPropertyKey k)
  | .call callee args =>
    -- A property call passes its base as the receiver, and evaluates
    -- that base once: `o.f()` and `o[k]()` are the only shapes with a
    -- `this`, because nothing here has a `with` or a global object.
    match callee with
    | .member object name => do
      let base ← evalExpr env object
      let f ← getProp base name
      callFunction f base (← evalExprs env args)
    | .index object key => do
      let base ← evalExpr env object
      let k ← evalExpr env key
      let f ← getProp base (← toPropertyKey k)
      callFunction f base (← evalExprs env args)
    | _ => do
      let f ← evalExpr env callee
      callFunction f undefValue (← evalExprs env args)
  | .new callee args => do
    let f ← evalExpr env callee
    construct f (← evalExprs env args)
  | .objectLit props => do
    let r ← allocObj {}
    evalProps env props r
    pure (.obj r)
  | .funcExpr name params body =>
    match name with
    | none => makeFunction { params, body, env, kind := .ordinary }
    | some n => do
      -- A named function expression binds its own name, immutably, in a
      -- scope holding nothing else, so the body can recurse through it
      -- and no outer binding is shadowed for anyone else.
      let r ← allocCell { mutable := false }
      let inner := (n, r) :: env
      let f ← makeFunction { params, body, env := inner, kind := .ordinary }
      initCell r f
      pure f
  | .arrow params body =>
    -- A concise body is a `return` of its expression: the two forms
    -- differ in syntax only, so `Closure` carries one shape.
    match body with
    | .block b => makeFunction { params, body := b, env, kind := .arrow }
    | .expr e => makeFunction { params, body := [.returnStmt (some e)], env, kind := .arrow }
  | .assign target value =>
    match target with
    | .ident name => do
      let v ← evalExpr env value
      match Env.lookup env name with
      | some r => do
        let cell ← getCell r
        match cell.value with
        | none =>
          throwJsError .referenceError s!"Cannot access '{name}' before initialization"
        | some _ =>
          if cell.mutable then do
            writeCell r v
            pure v
          else
            throwJsError .typeError "Assignment to constant variable."
      | none => throwJsError .referenceError s!"{name} is not defined"
    | .member object name => do
      let base ← evalExpr env object
      let v ← evalExpr env value
      setProp base name v
      pure v
    | .index object key => do
      let base ← evalExpr env object
      let k ← evalExpr env key
      let v ← evalExpr env value
      setProp base (← toPropertyKey k) v
      pure v
  partial_fixpoint

/-- Evaluate an argument list, left to right. -/
def evalExprs (env : Env) : List Expr → EvalM (List Value)
  | [] => pure []
  | e :: rest => do
    let v ← evalExpr env e
    let vs ← evalExprs env rest
    pure (v :: vs)
  partial_fixpoint

/-- Evaluate an object literal's properties into an already-allocated
object, left to right, so a repeated key keeps the last value. -/
def evalProps (env : Env) : List (String × Expr) → Ref → EvalM Unit
  | [], _ => pure ()
  | (k, e) :: rest, r => do
    let v ← evalExpr env e
    modifyObj r (fun o => o.setOwn k v)
    evalProps env rest r
  partial_fixpoint

/-- Get a property, walking the prototype chain. There is no fuel bound:
a cyclic chain is a program that does not terminate, which is `none`, and
that is the same answer the epic gives every other divergence. A
primitive base other than `undefined` or `null` answers `undefined`
because it has no wrapper prototype yet — `"x".length` waits for #380.
This is inside the fixpoint block for the walk today, and for #389's
accessors, which will call user code from here. -/
def getProp (base : Value) (key : String) : EvalM Value :=
  match base with
  | .prim .undef =>
    throwJsError .typeError s!"Cannot read properties of undefined (reading '{key}')"
  | .prim .null =>
    throwJsError .typeError s!"Cannot read properties of null (reading '{key}')"
  | .prim _ => pure undefValue
  | .obj r => do
    let o ← readObj r
    match o.getOwn key with
    | some v => pure v
    | none =>
      match o.proto with
      | some p => getProp (.obj p) key
      | none => pure undefValue
  partial_fixpoint

/-- ToPrimitive with hint number: `valueOf`, then `toString`, the first
callable one whose result is a primitive wins, and a `TypeError` if
neither gives one. Until #389 puts the intrinsics on
`Object.prototype`, a plain object has neither method, so `{} + 1`
throws here where an engine answers `"[object Object]1"`; a user-defined
`valueOf` already works. -/
def toPrimitive (v : Value) : EvalM JsVal :=
  match v with
  | .prim p => pure p
  | .obj _ => do
    match ← primitiveFrom v "valueOf" with
    | some p => pure p
    | none =>
      match ← primitiveFrom v "toString" with
      | some p => pure p
      | none => throwJsError .typeError "Cannot convert object to primitive value"
  partial_fixpoint

/-- One step of OrdinaryToPrimitive: call the named method on the object
if it has a callable one, and answer its result when that is a
primitive. -/
def primitiveFrom (o : Value) (name : String) : EvalM (Option JsVal) := do
  let m ← getProp o name
  if ← isCallable m then
    match ← callFunction m o [] with
    | .prim p => pure (some p)
    | .obj _ => pure none
  else
    pure none
  partial_fixpoint

/-- ToPropertyKey. Every key in this slice is a string: symbols are
#392's, so an object key is its ToPrimitive and then this again. -/
def toPropertyKey (v : Value) : EvalM String :=
  match v with
  | .prim (.str s) => pure s
  | .prim (.num x) => pure (formatNumber x)
  | .prim (.bool b) => pure (if b then "true" else "false")
  | .prim .undef => pure "undefined"
  | .prim .null => pure "null"
  | .prim (.bigint i) => pure (toString i ++ "n")
  | .obj _ => do
    let p ← toPrimitive v
    toPropertyKey (.prim p)
  partial_fixpoint

/-- Call a function. The callee's environment is its closure's, plus a
`this` binding for an ordinary function (an arrow pushes none, so `this`
stays lexical), plus the parameters, and then the body's own
declarations. A `return` is an abrupt completion `catchReturn` turns back
into a value; a body that falls off the end answers `undefined`. -/
def callFunction (f : Value) (thisArg : Value) (args : List Value) : EvalM Value :=
  match f with
  | .prim _ => throwJsError .typeError "not a function"
  | .obj r => do
    let o ← readObj r
    match o.callable with
    | none => throwJsError .typeError "not a function"
    | some (.native (.errorCtor _)) =>
      -- `Error("x")` is `new Error("x")`: an Error constructor called as
      -- a function constructs (20.5.1.1), because with no `new.target` it
      -- falls back to itself.
      construct f args
    | some (.native n) => callNative n thisArg args
    | some (.closure c) => do
      let withThis ←
        match c.kind with
        | .arrow => pure c.env
        | .ordinary => do
          let tr ← allocCell { mutable := false, value := some thisArg }
          pure ((thisName, tr) :: c.env)
      let bound ← bindParams withThis c.params args
      let inner ← instantiateBlock bound c.body
      catchReturn do
        let _ ← evalStmts inner c.body none
        pure undefValue
  partial_fixpoint

/-- Run a built-in.

`.errorCtor` is the shared body of the seven `Error` constructors: it
sets `message` on the object it was handed, when an argument other than
`undefined` was given, and answers that object. It never allocates, so
`new E(m)` and `E(m)` differ only in who allocates — which is what lets
`construct` hand it a fresh object and `callFunction` route to
`construct`. The `options` argument, and so `cause`, is ignored; there is
no `stack`.

`.errorToString` is `Error.prototype.toString`: `name` and `message` off
the receiver, each defaulting when absent, joined by `": "` unless one of
them is empty. The uncaught-error report runs this same algorithm, which
is the reason it is exposed at all. -/
def callNative (f : NativeFn) (thisArg : Value) (args : List Value) : EvalM Value :=
  match f with
  | .errorCtor _ => do
    match args with
    | [] => pure thisArg
    | .prim .undef :: _ => pure thisArg
    | m :: _ => do
      -- ToString, which `toPropertyKey` already is for every primitive
      -- and which runs ToPrimitive on an object; #380 gives it its own
      -- name.
      setProp thisArg "message" (.prim (.str (← toPropertyKey m)))
      pure thisArg
  | .errorToString =>
    match thisArg with
    | .prim _ => throwJsError .typeError "Error.prototype.toString called on non-object"
    | .obj _ => do
      let name ← match ← getProp thisArg "name" with
        | .prim .undef => pure "Error"
        | v => toPropertyKey v
      let msg ← match ← getProp thisArg "message" with
        | .prim .undef => pure ""
        | v => toPropertyKey v
      if name.isEmpty then pure (.prim (.str msg))
      else if msg.isEmpty then pure (.prim (.str name))
      else pure (.prim (.str (name ++ ": " ++ msg)))
  partial_fixpoint

/-- OrdinaryCreateFromConstructor: the instance `new` builds, linked to
the constructor's `prototype` property when that is an object and to null
otherwise. Shared by the two `construct` arms, which differ only in what
runs afterwards. -/
def allocFromConstructor (f : Value) : EvalM Ref := do
  let protoVal ← getProp f "prototype"
  let proto := match protoVal with
    | .obj p => some p
    | .prim _ => none
  allocObj { proto }
  partial_fixpoint

/-- Whether `p` is on `o`'s prototype chain, `o` itself not counted —
`[[HasInstance]]`'s walk. No fuel, as `getProp` has none: a cycle is a
program that does not terminate, and nothing can build one until
`Object.setPrototypeOf` (#389). -/
def protoChainHas (o p : Ref) : EvalM Bool := do
  match (← readObj o).proto with
  | none => pure false
  | some q => if q == p then pure true else protoChainHas q p
  partial_fixpoint

/-- `new`. The instance's prototype is the function's `prototype`
property when that is an object, and null otherwise; a constructor that
returns an object returns that object, and one that returns anything else
returns the instance. An arrow has no `[[Construct]]`. -/
def construct (f : Value) (args : List Value) : EvalM Value :=
  match f with
  | .prim _ => throwJsError .typeError "not a constructor"
  | .obj r => do
    let o ← readObj r
    match o.callable with
    | none => throwJsError .typeError "not a constructor"
    | some (.native (.errorCtor k)) => do
      -- The native answers the object it was handed, so the
      -- return-object rule below holds trivially and is not written out.
      let fresh ← allocFromConstructor f
      callNative (.errorCtor k) (.obj fresh) args
    | some (.native _) => throwJsError .typeError "not a constructor"
    | some (.closure c) =>
      match c.kind with
      | .arrow => throwJsError .typeError "not a constructor"
      | .ordinary => do
        let fresh ← allocFromConstructor f
        match ← callFunction f (.obj fresh) args with
        | .obj result => pure (.obj result)
        | .prim _ => pure (.obj fresh)
  partial_fixpoint

/-- Evaluate a statement against the running completion value, and
answer the updated one. The environment is not answered:
`instantiateBlock` fixed it before the list started running.

Threading is UpdateEmpty, done once instead of at every statement list.
The spec fills an abrupt completion's empty `[[Value]]` from each list it
crosses on the way out; starting a nested list at the *enclosing* running
value computes exactly the same first-non-empty value, without catching
the completion at every list to patch it. So a statement that completes
empty answers `acc` unchanged, and a `break` throws the value it can see.
`if`, `while`, `try`, and `catch` bodies start from `undefined` rather
than from the enclosing value — `eval("1; if (true) {}")` is `undefined`
— while a bare block, a function body, and the script itself do not. -/
def evalStmt (env : Env) : Stmt → Option Value → EvalM (Option Value)
  | .exprStmt value, _ => do
    let v ← evalExpr env value
    pure (some v)
  | .varDecl _ declarators, acc => do
    evalDeclarators env declarators
    pure acc
  | .funcDecl _ _ _, acc =>
    -- Instantiation already built and bound it; the statement itself
    -- completes empty, so `1; function f() {}` still answers 1.
    pure acc
  | .returnStmt argument, _ => do
    let v ← match argument with
      | some e => evalExpr env e
      | none => pure undefValue
    throwCompletion (.«return» v)
  | .ifStmt test consequent alternate, _ => do
    let t ← evalExpr env test
    if toBooleanPrim t then
      evalStmt env consequent (some undefValue)
    else
      match alternate with
      | some s => evalStmt env s (some undefValue)
      | none => pure (some undefValue)
  | .whileStmt test body, _ =>
    -- An unlabelled loop reached directly: no label names it, so only an
    -- unlabelled `continue` is its own.
    evalLoop env [] test body
  | .block body, acc => evalBlock env body acc
  | .labeled l body, acc =>
    -- A label reached from a statement list starts a fresh label set:
    -- only `a: b: while (…)` puts two in one set, and `evalLabeled` is
    -- what collects them.
    evalLabeled env [] (.labeled l body) acc
  | .breakStmt label, acc => throwCompletion (.«break» label acc)
  | .continueStmt label, acc => throwCompletion (.«continue» label acc)
  partial_fixpoint

/-- A statement list with its own scope: instantiated, then run from the
running value it was reached with. -/
def evalBlock (env : Env) (body : List Stmt) (acc : Option Value) :
    EvalM (Option Value) := do
  let inner ← instantiateBlock env body
  evalStmts inner body acc
  partial_fixpoint

/-- LabelledEvaluation: a statement reached through a set of labels. A
`labeled` adds its own and recurses, so `a: b: while (…)` hands the loop
both; a loop consumes the set, because a labelled `continue` targeting it
must be *its* continue rather than an escape; anything else ignores it
and is an ordinary statement. A labelled `break` is caught by the label
it names and by nothing else, which is why this is the only catch of one
and why an unnamed label set is not a scope. -/
def evalLabeled (env : Env) (labels : List String) :
    Stmt → Option Value → EvalM (Option Value)
  | .labeled l body, acc => do
    match ← attempt (evalLabeled env (l :: labels) body acc) with
    | .ok v => pure v
    | .error (.«break» (some l') v) =>
      if l' == l then pure v else throwCompletion (.«break» (some l') v)
    | .error c => throwCompletion c
  | .whileStmt test body, _ => evalLoop env labels test body
  | s, acc => evalStmt env s acc
  partial_fixpoint

/-- A loop as a BreakableStatement: an unlabelled `break` is its own and
ends it with the running value, a labelled one is somebody else's. The
loop's running value starts at `undefined`, not at empty, so a loop whose
body never runs still completes with a value. -/
def evalLoop (env : Env) (labels : List String) (test : Expr) (body : Stmt) :
    EvalM (Option Value) := do
  match ← attempt (evalWhile env labels test body (some undefValue)) with
  | .ok v => pure v
  | .error (.«break» none v) => pure v
  | .error c => throwCompletion c
  partial_fixpoint

/-- Initialize a declaration's cells left to right, each initializer
seeing the ones before it. The cells already exist — instantiation
allocated them — so this ends their temporal dead zone rather than
binding anything new. A declarator without an initializer binds
`undefined`, which is what makes `let x;` different from a name in its
dead zone. -/
def evalDeclarators (env : Env) : List Declarator → EvalM Unit
  | [] => pure ()
  | d :: rest => do
    let v ← match d.init with
      | some e => evalExpr env e
      | none => pure undefValue
    match Env.lookup env d.name with
    | some r => initCell r v
    | none => pure ()
    evalDeclarators env rest
  partial_fixpoint

/-- Run a statement list, threading the running completion value. -/
def evalStmts (env : Env) : List Stmt → Option Value → EvalM (Option Value)
  | [], acc => pure acc
  | s :: rest, acc => do
    let v ← evalStmt env s acc
    evalStmts env rest v
  partial_fixpoint

/-- Run a `while`'s iterations. The loop is the one definition whose
unfolding is a proof step: `rw [evalWhile]` exposes exactly one
iteration, and a postcondition is proved by doing that until the test
fails. A `continue` this loop answers for resumes with the value the body
had reached; any other completion, `break` included, leaves — `evalLoop`
is where an unlabelled `break` stops. -/
def evalWhile (env : Env) (labels : List String) (test : Expr) (body : Stmt)
    (acc : Option Value) : EvalM (Option Value) := do
  let t ← evalExpr env test
  if toBooleanPrim t then
    match ← attempt (evalStmt env body acc) with
    | .ok v => evalWhile env labels test body v
    | .error (.«continue» l v) =>
      if loopContinues labels l then evalWhile env labels test body v
      else throwCompletion (.«continue» l v)
    | .error c => throwCompletion c
  else
    pure acc
  partial_fixpoint

end

/-- Run a whole script from the realm's global environment. The script
body is a block like any other, so it is instantiated first — on top of
`globalEnv`, which is where `Error` and its subclasses are bound. -/
def evalProgram (p : Program) : EvalM (Option Value) := do
  let env ← instantiateBlock globalEnv p
  evalStmts env p none

/-- A script's run, heap and all: `none` is divergence, `.error` an
uncaught abrupt completion, `.ok` the completion value (`none` when no
statement produced one). The binary reads this, because reporting an
uncaught error means following the reference it threw. -/
def runScript (p : Program) : Option (Except Completion (Option Value) × Heap) :=
  ((evalProgram p).run).run Heap.initial

/-- A script's outcome with the heap dropped, which is what a proof
states: a theorem about a program should say what it answers, not what
realm it answered in. -/
def runProgram (p : Program) : Option (Except Completion (Option Value)) :=
  (runScript p).map (·.1)

/-- An Error object's `toString`, for the report. "Error object" here
means the prototype chain reaches `Error.prototype` — which is what an
`[[ErrorData]]` slot would say about everything this slice can build,
there being no other way to get that prototype. -/
def errorSummary (v : Value) : EvalM (Option String) := do
  match v with
  | .prim _ => pure none
  | .obj r =>
    if ← protoChainHas r ErrorKind.error.protoRef then
      match ← callNative .errorToString v [] with
      | .prim (.str s) => pure (some s)
      | _ => pure none
    else pure none

/-- How the binary names a thrown value: `<name>: <message>` for an Error
object, and its printed form for anything else — a script may `throw 1`.
The summary is computed in the heap the throw came out with, since that
is where the object is. A `toString` that itself ends abruptly falls back
to the printed form rather than replacing one uncaught throw with
another. -/
def describeThrown (h : Heap) (v : Value) : String :=
  match ((errorSummary v).run).run h with
  | some (.ok (some s), _) => s
  | _ => formatValue v

end Tarski
