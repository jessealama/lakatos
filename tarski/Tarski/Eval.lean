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
their equations are ordinary and `simp` may use them freely. Four of the
recursive ones are never added to a simp set and are unfolded one step at
a time with `rw`: `evalWhile`, `evalFor`, `getProp`, and `joinElements`.
The rule is not "recursive" but "recursive on something other than
syntax" — `evalExpr` and its neighbours recurse on a concrete AST, which
runs out, while a loop recurses until a heap value says stop, a prototype
walk until a heap link does, and a join until an array's length does, and
`simp` unfolds all three under a binder it has not resolved, forever.
What decides membership in the block is whether a definition can reach
user code: `getProp`, `toPrimitive`, and `setProp` can (a prototype chain
is unbounded, ToPrimitive calls `valueOf`, and ArraySetLength coerces its
value with ToNumber, which is ToPrimitive on an object), so they are
inside; `instantiateBlock` and `makeFunction` only touch the heap, so
they are outside.

A block's declarations are instantiated before its first statement runs.
That is one mechanism answering three needs: the temporal dead zone (a
cell exists but holds nothing until its declarator runs), a function
declaration callable above its own text, and two declarations that call
each other.

A `var` is instantiated somewhere else and at another time. `varNames`
collects VarDeclaredNames over a whole function body or script — through
blocks, loops, `switch` clauses, and `try` parts, but never into a
nested function — and `hoistVars` gives each of them a cell holding
`undefined` before the body runs. That is why a `var` has no dead zone,
why a block's `var` outlives the block, and why a `var` naming a
parameter or an existing global keeps the binding already there rather
than erasing it.

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
| `xs.length = v` with a `v` that is not a uint32    | `RangeError`     | `Invalid array length`                                       |
| `Object.keys` of `undefined` or `null`             | `TypeError`      | `Cannot convert undefined or null to object`                 |
| `Object(v)` or `hasOwnProperty` on a string primitive | `TypeError`  | `Cannot convert a primitive to an object`                     |
| `push` on a non-array                              | `TypeError`      | `Array.prototype.push called on non-array`                   |
| `join` on a non-array                              | `TypeError`      | `Array.prototype.join called on non-array`                   |
| `Number.prototype.{toString,valueOf,toFixed,toExponential,toPrecision,toLocaleString}` off a Number | `TypeError` | `Number.prototype.<name> requires that 'this' be a Number` |
| `Boolean.prototype.toString` off a Boolean         | `TypeError`      | `Boolean.prototype.toString requires that 'this' be a Boolean` |
| `Boolean.prototype.valueOf` off a Boolean          | `TypeError`      | `Boolean.prototype.valueOf requires that 'this' be a Boolean`  |
| `(1).toString(r)` with an `r` outside 2–36         | `RangeError`     | `toString() radix must be between 2 and 36`                   |
| `(1).toFixed(f)` with an `f` outside 0–100         | `RangeError`     | `toFixed() digits argument must be between 0 and 100`         |
| `(1).toExponential(f)` with an `f` outside 0–100   | `RangeError`     | `toExponential() argument must be between 0 and 100`          |
| `(1).toPrecision(p)` with a `p` outside 1–100      | `RangeError`     | `toPrecision() argument must be between 1 and 100`            |

`Tarski/Monad.lean` holds two more, for the two arms a reference the
evaluator handed out cannot reach. -/

namespace Tarski

open Js

/-- Whether a declaration form produces writable bindings. -/
def DeclKind.isMutable : DeclKind → Bool
  | .«let» => true
  | .«const» => false
  | .«var» => true

/-- One step of an update operator, applied to the number ToNumeric
gave. `++` and `--` are the two, and neither saturates: the arithmetic is
the library's binary64, so `Infinity++` is `Infinity`. -/
def UpdateOp.step : UpdateOp → Float → Float
  | .inc, x => x + 1.0
  | .dec, x => x - 1.0

/-- ToNumber on primitives. Not `JsVal.toNumber`, whose wrong-tag throw
is the prover refusing a coercion rather than JS performing one: here the
coercion is the semantics. An object never reaches this — ToPrimitive
runs first — and the `str` arm is the library's StringToNumber, so
`Number("0.1")` and the literal `0.1` are the same term. -/
def toNumberPrim : JsVal → Float
  | .num x => x
  | .bool b => if b then 1.0 else 0.0
  | .undef => floatNaN
  | .null => 0.0
  | .str s => Number.stringToNumber s
  | .bigint _ => floatNaN

/-- ToString on primitives. An object never reaches this — ToPrimitive
runs first — and the number arm is the library's `Number::toString`.
`toPropertyKey` is this, and so is the string arm of `+`. -/
def toStringPrim : JsVal → String
  | .str s => s
  | .num x => Number.toDecimalString x
  | .bool b => if b then "true" else "false"
  | .undef => "undefined"
  | .null => "null"
  | .bigint i => toString i ++ "n"

/-- Whether a primitive is a string, which is what makes `+`
concatenation rather than addition. Not `JsVal.isStr`: the library owns
that namespace, and the evaluator may not grow it. -/
def isStrPrim : JsVal → Bool
  | .str _ => true
  | _ => false

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

/-- `Object.is` on values: the library's `sameValue` on primitives —
which is what makes `Object.is(NaN, NaN)` true and `Object.is(0, -0)`
false — reference identity on objects, and `false` across the two. -/
def sameValueValue : Value → Value → Bool
  | .prim a, .prim b => JsVal.sameValue a b
  | .obj r₁, .obj r₂ => r₁ == r₂
  | .prim _, .obj _ => false
  | .obj _, .prim _ => false

/-- Which hint ToPrimitive was called with. `number` is the default and
what `+`, the relations, and the unary operators use; `string` is what
`String(v)`, `join`, and ToPropertyKey use. The difference is only the
order the two methods are tried in. -/
inductive PrimHint where
  | number
  | string
deriving Repr, DecidableEq, Inhabited

/-- The two method names OrdinaryToPrimitive tries, in the hint's
order. -/
def hintOrder : PrimHint → String × String
  | .number => ("valueOf", "toString")
  | .string => ("toString", "valueOf")

/-- A string's `length`, in code points. `JsVal.str` is a Lean `String`,
which cannot hold a lone surrogate, so this is UTF-16 code-unit length
for every string this slice can build; #391 owns the difference, along
with `String.prototype` and the wrapper object. -/
def stringLength (s : String) : Nat := s.length

/-- The one-character string at an index, or `none` past the end — the
String exotic object's own index properties, in code points for the
reason `stringLength` gives. -/
def stringIndex? (s : String) (i : Nat) : Option String :=
  s.toList[i]?.map String.singleton

/-- ToUint32 restricted to the values that are already one: an array
`length` and an `Array(n)` argument are integers in `[0, 2^32)` or a
`RangeError`, so nothing here wraps. The conversion is the library's
ToIntegerOrInfinity — every `Float`-to-`Nat` spelling is behind the
arithmetic boundary, and this is the sanctioned route — with integrality
and the range demanded here, so a fractional value and an infinity are
both `none`. Both zeros are `0`. -/
def uint32Of? (x : Float) : Option Nat :=
  match Number.FloatOps.integerOrInfinity? x with
  | some i =>
    if 0 ≤ i && i < 4294967296 && Number.FloatOps.tsIsInteger x then some i.toNat else none
  | none => none

/-- The index keys of something `length` long, as string values —
`Object.keys` of a string, whose own properties are its indices. -/
def indexKeys (n : Nat) : List Value :=
  (List.range n).map (fun i => .prim (.str (Nat.repr i)))

/-- Whether a built-in has a `[[Construct]]`. `String` does not: the
wrapper object is #391's, so `new String("x")` refuses. `Math` is not a
function at all, so it is not here either. -/
def NativeFn.constructs : NativeFn → Bool
  | .errorCtor _ => true
  | .objectCtor => true
  | .arrayCtor => true
  | .numberCtor => true
  | .booleanCtor => true
  | _ => false

/-- `Number.prototype.toString`'s radix: ToIntegerOrInfinity of the
argument, accepted only in `[2, 36]`. NaN, an infinity, a negative, and 37
all answer `none`, which the caller reports as the `RangeError` —
ToIntegerOrInfinity's own zero and infinity are outside the range either
way, so neither needs a case of its own. -/
def radix? (x : Float) : Option Nat :=
  match Number.FloatOps.integerOrInfinity? x with
  | some i => if 2 ≤ i && i ≤ 36 then some i.toNat else none
  | none => none

/-- thisNumberValue: the `[[NumberData]]` of the receiver, which may be
the primitive itself or a wrapper around one. `who` names the method, so
the message says which one was called off a Number. -/
def thisNumberValue (who : String) (v : Value) : EvalM Float := do
  match v with
  | .prim (.num x) => pure x
  | .obj r =>
    match (← readObj r).kind with
    | .number x => pure x
    | _ => throwJsError .typeError s!"Number.prototype.{who} requires that 'this' be a Number"
  | _ => throwJsError .typeError s!"Number.prototype.{who} requires that 'this' be a Number"

/-- thisBooleanValue, the mirror of `thisNumberValue`. -/
def thisBooleanValue (who : String) (v : Value) : EvalM Bool := do
  match v with
  | .prim (.bool b) => pure b
  | .obj r =>
    match (← readObj r).kind with
    | .boolean b => pure b
    | _ => throwJsError .typeError s!"Boolean.prototype.{who} requires that 'this' be a Boolean"
  | _ => throwJsError .typeError s!"Boolean.prototype.{who} requires that 'this' be a Boolean"

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
on. `not`, `typeof`, and `void` never coerce, so `evalExpr` answers them
before reaching here; the arms are still written out, because a total
function of the operator is easier to reason about than a partial one. -/
def applyUnary : UnaryOp → JsVal → Value
  | .neg, v => .prim (.num (-(toNumberPrim v)))
  | .plus, v => .prim (.num (toNumberPrim v))
  | .not, v => .prim (.bool (!toBooleanPrim (.prim v)))
  | .typeof, v => .prim (.str (typeofName v.typeof))
  | .void, _ => .prim .undef

/-- Apply a coercing infix operator to its two operands, both of which
ToPrimitive has already run on, left first. Two operators look at the
operands' types. `+` is concatenation when either side is a string and
addition otherwise. Each of the four relations is code-point string
order when *both* sides are strings and numeric otherwise, which is
IsLessThan's own split: `"10" < "9"` is true and `"a" < 1` is false,
the latter because ToNumber of a string is still the placeholder (#388).
Lean's `String` order is `List Char` order on the code points, so it is
UTF-16 code-unit order for every string this slice can build — a lone
surrogate cannot live in a Lean `String`, and #391 owns the difference.
`%` is the library's `tsRem` — C `fmod`, not the IEEE remainder — `**` is
its `tsPow`, which is `Math.pow`'s definition too, and the
numeric relations are Lean's binary64 order, which is the library's model
of it, so a NaN operand answers `false` on all four. -/
def applyBinary : BinaryOp → JsVal → JsVal → Value
  | .add, l, r =>
    if isStrPrim l || isStrPrim r then .prim (.str (toStringPrim l ++ toStringPrim r))
    else .prim (.num (toNumberPrim l + toNumberPrim r))
  | .sub, l, r => .prim (.num (toNumberPrim l - toNumberPrim r))
  | .mul, l, r => .prim (.num (toNumberPrim l * toNumberPrim r))
  | .div, l, r => .prim (.num (toNumberPrim l / toNumberPrim r))
  | .rem, l, r => .prim (.num (Number.FloatOps.tsRem (toNumberPrim l) (toNumberPrim r)))
  -- `**` and `Math.pow` are one library definition.
  | .exponent, l, r =>
    .prim (.num (Number.FloatOps.tsPow (toNumberPrim l) (toNumberPrim r)))
  | .lt, l, r =>
    if isStrPrim l && isStrPrim r then .prim (.bool (decide (toStringPrim l < toStringPrim r)))
    else .prim (.bool (decide (toNumberPrim l < toNumberPrim r)))
  | .le, l, r =>
    if isStrPrim l && isStrPrim r then .prim (.bool (decide (toStringPrim l ≤ toStringPrim r)))
    else .prim (.bool (decide (toNumberPrim l ≤ toNumberPrim r)))
  | .gt, l, r =>
    if isStrPrim l && isStrPrim r then .prim (.bool (decide (toStringPrim r < toStringPrim l)))
    else .prim (.bool (decide (toNumberPrim r < toNumberPrim l)))
  | .ge, l, r =>
    if isStrPrim l && isStrPrim r then .prim (.bool (decide (toStringPrim r ≤ toStringPrim l)))
    else .prim (.bool (decide (toNumberPrim r ≤ toNumberPrim l)))
  | .strictEq, l, r => .prim (.bool (strictEqValue (.prim l) (.prim r)))
  | .strictNe, l, r => .prim (.bool (!strictEqValue (.prim l) (.prim r)))
  -- `evalExpr` answers `instanceof` before reaching here, as it answers
  -- `!` and `typeof` before `applyUnary`. Unlike those, this arm cannot
  -- state the operator's meaning — it walks a prototype chain, which is
  -- the heap's business — so it states what is true of the primitives it
  -- would have been handed: neither is an instance of anything.
  | .instanceof, _, _ => .prim (.bool false)

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

/-- The `default` clause and everything after it, or nothing when there
is no `default`. Pure, and a search over syntax, so it is outside the
fixpoint block. -/
def dropUntilDefault : List SwitchCase → List SwitchCase
  | [] => []
  | c :: rest => if c.test.isNone then c :: rest else dropUntilDefault rest

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
constructed. That `prototype` is an ordinary object, so it is created
against `Object.prototype` like any other; the function object's own
`[[Prototype]]` stays null until `Function.prototype` exists (#389). -/
def makeFunction (c : Closure) : EvalM Value := do
  let f ← allocObj { callable := some (.closure c) }
  match c.kind with
  | .arrow => pure (.obj f)
  | .ordinary => do
    let proto ← newObject
    modifyObj proto (fun o => o.setOwn "constructor" (.obj f))
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

mutual

/-- VarDeclaredNames (8.2.5) over what this AST has: every name a `var`
declares anywhere inside a function body or script, in source order. It
descends through blocks, both loops, a `switch`'s clauses, and a `try`'s
three parts, because none of those is a variable scope; it stops at a
function declaration and at every expression, because a nested function's
`var`s are its own. Pure and structural, so `evalProgram` and
`callFunction` still reduce under `simp`. -/
def varNames : List Stmt → List String
  | [] => []
  | s :: rest => varNamesStmt s ++ varNames rest

/-- One statement's VarDeclaredNames; see `varNames`. -/
def varNamesStmt : Stmt → List String
  | .varDecl .«var» declarators => declarators.map (·.name)
  | .block body => varNames body
  | .ifStmt _ consequent none => varNamesStmt consequent
  | .ifStmt _ consequent (some alternate) => varNamesStmt consequent ++ varNamesStmt alternate
  | .whileStmt _ body => varNamesStmt body
  | .forStmt (some (.decl .«var» declarators)) _ _ body =>
    declarators.map (·.name) ++ varNamesStmt body
  | .forStmt _ _ _ body => varNamesStmt body
  | .switchStmt _ cases => varNamesCases cases
  | .tryStmt block none none => varNames block
  | .tryStmt block (some ⟨_, handler⟩) none => varNames block ++ varNames handler
  | .tryStmt block none (some finalizer) => varNames block ++ varNames finalizer
  | .tryStmt block (some ⟨_, handler⟩) (some finalizer) =>
    varNames block ++ varNames handler ++ varNames finalizer
  | .labeled _ body => varNamesStmt body
  | _ => []

/-- A `switch`'s clauses' VarDeclaredNames, in source order. -/
def varNamesCases : List SwitchCase → List String
  | [] => []
  | ⟨_, body⟩ :: rest => varNames body ++ varNamesCases rest

end

/-- VarDeclaredNames instantiated: a cell per name, holding `undefined`
rather than nothing, which is the whole of why a `var` has no dead zone.
`skip` is what is already bound and must stay bound — a function's
parameters (10.2.11 step 27) and the global environment's own names
(16.1.7 step 17) — so `function f(a) { var a; }` keeps the argument and
`var Error;` at top level leaves `Error` where it was. A name already
handled by this pass joins `skip`, so `var x = 1; var x = 2;` allocates
one cell. -/
def hoistVars (env : Env) (skip : List String) : List String → EvalM Env
  | [] => pure env
  | n :: rest =>
    if skip.contains n then hoistVars env skip rest
    else do
      let r ← allocCell { mutable := true, value := some undefValue }
      hoistVars ((n, r) :: env) (n :: skip) rest

/-- Point a name at another cell, innermost binding first. Replacing
rather than pushing is what keeps a scope chain the same length across a
loop's iterations, so a thousand-iteration loop does not leave a
thousand shadowed copies for `Env.lookup` to walk. -/
def Env.rebind : Env → String → CellRef → Env
  | [], _, _ => []
  | (n, r) :: rest, name, fresh =>
    if n == name then (name, fresh) :: rest else (n, r) :: Env.rebind rest name fresh

/-- CreatePerIterationEnvironment (14.7.4.4): a fresh cell per name,
holding what the current one holds, with every other binding left alone.
A `for`'s `let` head is copied this way before the first test and again
after each body, so a closure the body made keeps that iteration's cell
while the update writes the next iteration's. A name still in its dead
zone copies as one — the cell is fresh and holds nothing. -/
def copyBindings (env : Env) : List String → EvalM Env
  | [] => pure env
  | n :: rest => do
    let c ← match Env.lookup env n with
      | some r => getCell r
      | none => pure { mutable := true, value := none }
    let fresh ← allocCell c
    copyBindings (Env.rebind env n fresh) rest

/-- Pass one over a statement list's direct statements. Nested blocks are
not descended into: each has its own scope and instantiates itself. A
`var` is not a block's — `hoistVars` gave it a cell in the enclosing
function or script — so it is skipped here. -/
def hoistNames (env : Env) : List Stmt → EvalM Env
  | [] => pure env
  | s :: rest => do
    let env' ← match s with
      | .varDecl .«var» _ => pure env
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

/-- PutValue to an identifier reference: the dead-zone read, the `const`
refusal, and the write. One definition rather than three copies, because
plain assignment, compound assignment, and `++` all write the same way
and differ only in what they wrote. It needs no user code, so it lives
outside the fixpoint block. -/
def putIdent (env : Env) (name : String) (v : Value) : EvalM Unit :=
  match Env.lookup env name with
  | some r => do
    let cell ← getCell r
    match cell.value with
    | none =>
      throwJsError .referenceError s!"Cannot access '{name}' before initialization"
    | some _ =>
      if cell.mutable then writeCell r v
      else throwJsError .typeError "Assignment to constant variable."
  | none => throwJsError .referenceError s!"{name} is not defined"

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
    -- than a `ReferenceError`: #389 gives the top level a receiver.
    match Env.lookup env thisName with
    | some r => readCell thisName r
    | none => pure undefValue
  | .unary op operand =>
    match op with
    | .not => do
      let v ← evalExpr env operand
      pure (.prim (.bool (!toBooleanPrim v)))
    | .typeof => do
      -- `typeof` evaluates a *reference*, and an unresolvable one
      -- answers `"undefined"` instead of throwing. That is the whole of
      -- the exception, so only a bare identifier with no binding takes
      -- this arm; every other operand is evaluated as usual.
      match operand with
      | .ident name =>
        match Env.lookup env name with
        | none => pure (.prim (.str "undefined"))
        | some _ => do
          let v ← evalExpr env operand
          pure (.prim (.str (← typeofValue v)))
      | _ => do
        let v ← evalExpr env operand
        pure (.prim (.str (← typeofValue v)))
    | .void => do
      -- `void e` evaluates its operand for the effects and answers
      -- `undefined`; the value is discarded uncoerced, so `void {}` does
      -- not reach ToPrimitive.
      let _ ← evalExpr env operand
      pure undefValue
    | _ => do
      let v ← evalExpr env operand
      pure (applyUnary op (← toPrimitive .number v))
  | .binary op left right => do
    let l ← evalExpr env left
    let r ← evalExpr env right
    match op with
    | .instanceof => pure (.prim (.bool (← instanceOf l r)))
    | _ =>
      if op.coerces then applyCoercing op l r
      else pure (applyStrict op l r)
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
    let r ← newObject
    evalProps env props r
    pure (.obj r)
  | .arrayLit elements => do newArray (← evalExprs env elements)
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
      putIdent env name v
      pure v
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
  | .compoundAssign op target value =>
    -- 13.15.2 in its own order: the target's *reference* is evaluated
    -- once and read, then the right operand, then the operator, then the
    -- write. So `let x = 1; x += (x = 2)` is 3 — the left read happened
    -- before the right side moved it — and `o[k()].p += 1` calls `k`
    -- once.
    match target with
    | .ident name => do
      let l ← evalExpr env (.ident name)
      let r ← evalExpr env value
      let result ← applyCoercing op l r
      putIdent env name result
      pure result
    | .member object name => do
      let base ← evalExpr env object
      let l ← getProp base name
      let r ← evalExpr env value
      let result ← applyCoercing op l r
      setProp base name result
      pure result
    | .index object key => do
      let base ← evalExpr env object
      let k ← toPropertyKey (← evalExpr env key)
      let l ← getProp base k
      let r ← evalExpr env value
      let result ← applyCoercing op l r
      setProp base k result
      pure result
  | .update op isPrefix target =>
    -- 13.4.2–13.4.5: read the reference, ToNumeric it, step it, write it
    -- back, and answer the new number for the prefix form and the old one
    -- for the postfix form. BigInt is outside the slice, so ToNumeric is
    -- ToNumber and the arithmetic is the library's binary64.
    match target with
    | .ident name => do
      let old := toNumberPrim (← toPrimitive .number (← evalExpr env (.ident name)))
      let stepped := op.step old
      putIdent env name (.prim (.num stepped))
      pure (.prim (.num (if isPrefix then stepped else old)))
    | .member object name => do
      let base ← evalExpr env object
      let old := toNumberPrim (← toPrimitive .number (← getProp base name))
      let stepped := op.step old
      setProp base name (.prim (.num stepped))
      pure (.prim (.num (if isPrefix then stepped else old)))
    | .index object key => do
      let base ← evalExpr env object
      let k ← toPropertyKey (← evalExpr env key)
      let old := toNumberPrim (← toPrimitive .number (← getProp base k))
      let stepped := op.step old
      setProp base k (.prim (.num stepped))
      pure (.prim (.num (if isPrefix then stepped else old)))
  partial_fixpoint

/-- ApplyStringOrNumericBinaryOperator: ToPrimitive on each operand with
the number hint, left first, and then the operator. `a op b` and
`a op= b` are the same computation once each side has a value, which is
what this names. -/
def applyCoercing (op : BinaryOp) (l r : Value) : EvalM Value := do
  let lp ← toPrimitive .number l
  let rp ← toPrimitive .number r
  pure (applyBinary op lp rp)
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
that is the same answer the epic gives every other divergence.

Two own properties do not live in a property list. A string answers its
own `length` and its own index properties — the String exotic object's
`[[GetOwnProperty]]` — and every other key on it is `undefined` until
`String.prototype` exists (#391). An array answers its own `length` out
of its kind, which is where the live length lives.

A Number or a Boolean base reads through its wrapper prototype **without
allocating a wrapper**: the wrapper would have no own properties, so the
answer is the same, and the receiver a method call then gets is still the
primitive, which is why `thisNumberValue` accepts both. A bigint base
still answers `undefined`, that being #392's.

This is inside the fixpoint block for the walk today, and for #389's
accessors, which will call user code from here. -/
def getProp (base : Value) (key : String) : EvalM Value :=
  match base with
  | .prim .undef =>
    throwJsError .typeError s!"Cannot read properties of undefined (reading '{key}')"
  | .prim .null =>
    throwJsError .typeError s!"Cannot read properties of null (reading '{key}')"
  | .prim (.str s) =>
    if key == "length" then pure (Value.ofNat (stringLength s))
    else
      match arrayIndex? key with
      | some i => pure (((stringIndex? s i).map (fun c => Value.prim (.str c))).getD undefValue)
      | none => pure undefValue
  | .prim (.num _) => getProp (.obj numberProtoRef) key
  | .prim (.bool _) => getProp (.obj booleanProtoRef) key
  | .prim _ => pure undefValue
  | .obj r => do
    let o ← readObj r
    match o.kind, key == "length" with
    | .array len, true => pure (Value.ofNat len)
    | _, _ =>
      match o.getOwn key with
      | some v => pure v
      | none =>
        match o.proto with
        | some p => getProp (.obj p) key
        | none => pure undefValue
  partial_fixpoint

/-- Set a property. Strict mode throughout, so a primitive base is a
`TypeError` rather than a silent no-op. An array's own `length` is the
one key whose write is not a property write: assigning to it truncates
or grows, and assigning to an index at or past the end grows the length
to hold it, which is the whole of the Array exotic object's
`[[DefineOwnProperty]]` at this slice's fidelity. Inside the fixpoint
block because that coercion can reach user code; writability checks and
prototype-chain setters arrive with descriptors (#389). -/
def setProp (base : Value) (key : String) (v : Value) : EvalM Unit :=
  match base with
  | .obj r => do
    let o ← readObj r
    match o.kind with
    | .array len =>
      if key == "length" then setArrayLength r o v
      else
        match arrayIndex? key with
        | some i => writeObj r { o.setOwn key v with kind := .array (max len (i + 1)) }
        | none => writeObj r (o.setOwn key v)
    -- A wrapper object takes an ordinary write like any other object: its
    -- `[[NumberData]]` is a field, not a property, so nothing can reach it.
    | _ => writeObj r (o.setOwn key v)
  | .prim _ =>
    throwJsError .typeError
      s!"Cannot set properties of {formatValue base} (setting '{key}')"
  partial_fixpoint

/-- ArraySetLength without descriptors: the new length is ToUint32 of
ToNumber of the value, and anything else — a negative, a fraction, a
string the placeholder ToNumber cannot read — is a `RangeError`.
Shortening drops the elements it passes; there is no non-writable check
and no partial truncation, both of which need descriptors (#389). -/
def setArrayLength (r : Ref) (o : Obj) (v : Value) : EvalM Unit := do
  match uint32Of? (toNumberPrim (← toPrimitive .number v)) with
  | none => throwJsError .rangeError "Invalid array length"
  | some n => writeObj r (o.truncate n)
  partial_fixpoint

/-- `Array.prototype.push`'s writes, left to right, each through
`setProp` so that the array's `length` grows with them. -/
def pushElements (arr : Value) (i : Nat) : List Value → EvalM Unit
  | [] => pure ()
  | v :: rest => do
    setProp arr (Nat.repr i) v
    pushElements arr (i + 1) rest
  partial_fixpoint

/-- `Array.prototype.join`'s fold: each element ToString'd, `undefined`
and `null` contributing the empty string, joined by the separator. It
recurses on the length rather than on syntax, so its equation is `rw`'s
and never a simp set's. -/
def joinElements (arr : Value) (i len : Nat) (sep : String) : EvalM String := do
  if i < len then
    let s ← match ← getProp arr (Nat.repr i) with
      | .prim .undef => pure ""
      | .prim .null => pure ""
      | v => toStringValue v
    let rest ← joinElements arr (i + 1) len sep
    pure (if i + 1 < len then s ++ sep ++ rest else s ++ rest)
  else pure ""
  partial_fixpoint

/-- ToPrimitive. `valueOf` then `toString` under the number hint,
`toString` then `valueOf` under the string one; the first callable
method whose result is a primitive wins, and a `TypeError` if neither
gives one. Until #389 puts the intrinsics on `Object.prototype`, a plain
object has neither method, so `{} + 1` throws here where an engine
answers `"[object Object]1"`; a user-defined `valueOf` or `toString`
already works. -/
def toPrimitive (hint : PrimHint) (v : Value) : EvalM JsVal :=
  match v with
  | .prim p => pure p
  | .obj _ => do
    match ← primitiveFrom v (hintOrder hint).1 with
    | some p => pure p
    | none =>
      match ← primitiveFrom v (hintOrder hint).2 with
      | some p => pure p
      | none => throwJsError .typeError "Cannot convert object to primitive value"
  partial_fixpoint

/-- ToString on values: ToPrimitive with hint string, then ToString on
the primitive. `String(v)`, `join`, and the `Error` constructor's
`message` all spell it this way. -/
def toStringValue (v : Value) : EvalM String := do
  pure (toStringPrim (← toPrimitive .string v))
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
  | .prim p => pure (toStringPrim p)
  | .obj _ => do
    let p ← toPrimitive .string v
    pure (toStringPrim p)
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
      -- FunctionDeclarationInstantiation 10.2.11 steps 27–28: the `var`s
      -- first, skipping the parameters, so `function f(a) { var a; }`
      -- keeps the argument; then the block's own declarations, whose
      -- cells are pushed later and so shadow a `var` of the same name,
      -- which is what makes `var f; function f() {}` end as the function.
      let hoisted ← hoistVars bound c.params (varNames c.body)
      let inner ← instantiateBlock hoisted c.body
      catchReturn do
        let _ ← evalStmts inner c.body none
        pure undefValue
  partial_fixpoint

/-- ToNumber on values: ToPrimitive with the number hint, then ToNumber
on the primitive. The twin of `toStringValue`, and what every coercing
built-in argument goes through. -/
def toNumberValue (v : Value) : EvalM Float := do
  pure (toNumberPrim (← toPrimitive .number v))
  partial_fixpoint

/-- ToIntegerOrInfinity on values, 7.1.5: ToNumber first — so a user
`valueOf` runs, and runs *before* any range check the caller makes — then
the library's own truncation. `none` is either infinity, which every
caller here reports as its own `RangeError`. -/
def toIntegerOrInfinityValue (v : Value) : EvalM (Option Int) := do
  pure (Number.FloatOps.integerOrInfinity? (← toNumberValue v))
  partial_fixpoint

/-- A whole argument list coerced to Numbers, left to right. `Math.max`
and `Math.min` need this rather than a fold that coerces lazily: the
specification coerces *every* argument before comparing any, so a user
`valueOf` after one that answered NaN still runs. -/
def toNumberValues : List Value → EvalM (List Float)
  | [] => pure []
  | v :: rest => do
    let x ← toNumberValue v
    let xs ← toNumberValues rest
    pure (x :: xs)
  partial_fixpoint

/-- The shared body of the eight unary `Math` members: ToNumber of the
first argument through one of the library's operations. A missing
argument is `undefined`, hence NaN, which is what makes `Math.abs()`
NaN. -/
def mathUnary (f : Float → Float) (args : List Value) : EvalM Value := do
  pure (.prim (.num (f (← toNumberValue (args.headD undefValue)))))
  partial_fixpoint

/-- `Number`'s argument. A *missing* `value` is `+0`, while a `value` that
is present and `undefined` is NaN, so the two cannot share one default. -/
def numberArg : List Value → EvalM Float
  | [] => pure 0.0
  | v :: _ => toNumberValue v
  partial_fixpoint

/-- What `new` does to a native that differs from calling it. Only the two
wrappers do: `Number(v)` answers the Number and `new Number(v)` a wrapper
object around it, off one conversion. `Object`, `Array`, and the `Error`
constructors behave the same either way, so they fall through to
`callNative`. NewTarget's `prototype` is ignored here as it is there
(#384). -/
def constructNative (n : NativeFn) (args : List Value) : EvalM Value :=
  match n with
  | .numberCtor => do
    let x ← numberArg args
    pure (.obj (← allocObj { proto := some numberProtoRef, kind := .number x }))
  | .booleanCtor => do
    let b := toBooleanPrim (args.headD undefValue)
    pure (.obj (← allocObj { proto := some booleanProtoRef, kind := .boolean b }))
  | _ => callNative n undefValue args
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
is the reason it is exposed at all.

The rest are #380's floor. `String(v)` is ToString and nothing else —
`new String(v)` refuses, the wrapper being #391's. `Object(v)` is an
ordinary object for a nullish argument, the argument itself for an
object, a wrapper for a Number or a Boolean, and a `TypeError` for a
string until that wrapper exists (#391). `Object.keys` is OrdinaryOwnPropertyKeys of an
object, the index keys of a string, and empty for any other non-nullish
primitive. `push` and `join` require an Array exotic receiver: the
generic array-like forms, and the rest of `Array.prototype`, are
#390's. A missing argument is `undefined` throughout.

`Number` and `Boolean` called as functions are their conversions;
`constructNative` is what `new` does instead. The four `Number`
predicates do **not** coerce — `Number.isNaN("NaN")` is `false` — while
every `Math` member does, through `toNumberValue`. `Math.max` and
`Math.min` coerce every argument first and then fold the library's binary
`tsMax`/`tsMin` from the identities its header names, `-∞` and `+∞`, so
the empty call answers an infinity and a NaN anywhere propagates.
`Math.pow` is `tsPow`, the same definition `**` is, and carries the same
limit on a non-integral exponent (#434).

`Number.prototype.toString` is the library's `toRadixString`, and the
`toFixed` family is the library's three formatters. Each arm keeps the
**specification's step order** where test262 observes it: a poisoned
argument is coerced, and so throws, before any range check; a non-finite
`this` short-circuits `toExponential` and `toPrecision` before their range
check but not `toFixed`, so `Infinity.toExponential(200)` is `Infinity`
while `NaN.toFixed(Infinity)` throws. `toLocaleString` is `toString()`:
there is no locale here, ECMA-402 being outside the epic. -/
def callNative (f : NativeFn) (thisArg : Value) (args : List Value) : EvalM Value :=
  match f with
  | .errorCtor _ => do
    match args with
    | [] => pure thisArg
    | .prim .undef :: _ => pure thisArg
    | m :: _ => do
      setProp thisArg "message" (.prim (.str (← toStringValue m)))
      pure thisArg
  | .errorToString =>
    match thisArg with
    | .prim _ => throwJsError .typeError "Error.prototype.toString called on non-object"
    | .obj _ => do
      let name ← match ← getProp thisArg "name" with
        | .prim .undef => pure "Error"
        | v => toStringValue v
      let msg ← match ← getProp thisArg "message" with
        | .prim .undef => pure ""
        | v => toStringValue v
      if name.isEmpty then pure (.prim (.str msg))
      else if msg.isEmpty then pure (.prim (.str name))
      else pure (.prim (.str (name ++ ": " ++ msg)))
  | .stringCtor =>
    match args with
    | [] => pure (.prim (.str ""))
    | v :: _ => do pure (.prim (.str (← toStringValue v)))
  | .objectCtor =>
    match args with
    | [] => do pure (.obj (← newObject))
    | .prim .undef :: _ => do pure (.obj (← newObject))
    | .prim .null :: _ => do pure (.obj (← newObject))
    | .obj r :: _ => pure (.obj r)
    | .prim (.num x) :: _ => do
      pure (.obj (← allocObj { proto := some numberProtoRef, kind := .number x }))
    | .prim (.bool b) :: _ => do
      pure (.obj (← allocObj { proto := some booleanProtoRef, kind := .boolean b }))
    | .prim _ :: _ => throwJsError .typeError "Cannot convert a primitive to an object"
  | .objectIs =>
    pure (.prim (.bool (sameValueValue (args[0]?.getD undefValue) (args[1]?.getD undefValue))))
  | .objectKeys =>
    match args[0]?.getD undefValue with
    | .prim .undef => throwJsError .typeError "Cannot convert undefined or null to object"
    | .prim .null => throwJsError .typeError "Cannot convert undefined or null to object"
    | .obj r => do newArray ((← readObj r).ownKeys.map (fun k => .prim (.str k)))
    | .prim (.str s) => newArray (indexKeys (stringLength s))
    | .prim _ => newArray []
  | .objectHasOwnProperty =>
    match thisArg with
    -- ToObject of a Number or a Boolean has no own properties, so the
    -- answer is `false` — but the key is converted first, as the spec
    -- orders it, so a `toString` on it still runs.
    | .prim (.num _) | .prim (.bool _) => do
      let _ ← toPropertyKey (args[0]?.getD undefValue)
      pure (.prim (.bool false))
    | .prim _ => throwJsError .typeError "Cannot convert a primitive to an object"
    | .obj r => do
      let key ← toPropertyKey (args[0]?.getD undefValue)
      pure (.prim (.bool ((← readObj r).hasOwn key)))
  | .arrayCtor =>
    -- `Array(n)` with one Number argument is a length, not an element;
    -- every other argument list is the elements themselves.
    match args with
    | [.prim (.num x)] =>
      match uint32Of? x with
      | none => throwJsError .rangeError "Invalid array length"
      | some n => newArrayOfLength n
    | vs => newArray vs
  | .arrayIsArray =>
    match args[0]?.getD undefValue with
    | .obj r => do pure (.prim (.bool (← readObj r).isArray))
    | .prim _ => pure (.prim (.bool false))
  | .arrayPush =>
    match thisArg with
    | .prim _ => throwJsError .typeError "Array.prototype.push called on non-array"
    | .obj r => do
      match (← readObj r).kind with
      | .array len => do
        pushElements thisArg len args
        pure (Value.ofNat (len + args.length))
      | _ => throwJsError .typeError "Array.prototype.push called on non-array"
  | .arrayJoin =>
    match thisArg with
    | .prim _ => throwJsError .typeError "Array.prototype.join called on non-array"
    | .obj r => do
      match (← readObj r).kind with
      | .array len => do
        let sep ← match args with
          | [] => pure ","
          | .prim .undef :: _ => pure ","
          | v :: _ => toStringValue v
        pure (.prim (.str (← joinElements thisArg 0 len sep)))
      | _ => throwJsError .typeError "Array.prototype.join called on non-array"
  | .numberCtor => do pure (.prim (.num (← numberArg args)))
  | .numberIsFinite =>
    match args[0]?.getD undefValue with
    | .prim (.num x) => pure (.prim (.bool (Number.FloatOps.tsIsFinite x)))
    | _ => pure (.prim (.bool false))
  | .numberIsInteger =>
    match args[0]?.getD undefValue with
    | .prim (.num x) => pure (.prim (.bool (Number.FloatOps.tsIsInteger x)))
    | _ => pure (.prim (.bool false))
  | .numberIsNaN =>
    match args[0]?.getD undefValue with
    | .prim (.num x) => pure (.prim (.bool (Number.FloatOps.tsIsNaN x)))
    | _ => pure (.prim (.bool false))
  | .numberIsSafeInteger =>
    match args[0]?.getD undefValue with
    | .prim (.num x) => pure (.prim (.bool (Number.FloatOps.tsIsSafeInteger x)))
    | _ => pure (.prim (.bool false))
  | .numberToString => do
    let x ← thisNumberValue "toString" thisArg
    match args with
    | [] => pure (.prim (.str (Number.toDecimalString x)))
    | .prim .undef :: _ => pure (.prim (.str (Number.toDecimalString x)))
    | r :: _ =>
      match radix? (← toNumberValue r) with
      | none => throwJsError .rangeError "toString() radix must be between 2 and 36"
      | some n => pure (.prim (.str (Number.toRadixString x n)))
  | .numberValueOf => do pure (.prim (.num (← thisNumberValue "valueOf" thisArg)))
  | .numberToFixed => do
    let x ← thisNumberValue "toFixed" thisArg
    match ← toIntegerOrInfinityValue (args.headD undefValue) with
    | none => throwJsError .rangeError "toFixed() digits argument must be between 0 and 100"
    | some f =>
      if f < 0 || 100 < f then
        throwJsError .rangeError "toFixed() digits argument must be between 0 and 100"
      else if !Number.FloatOps.tsIsFinite x then
        pure (.prim (.str (Number.toDecimalString x)))
      else pure (.prim (.str (Number.toFixedString x f.toNat)))
  | .numberToExponential => do
    let x ← thisNumberValue "toExponential" thisArg
    let f? ←
      match args.headD undefValue with
      | .prim .undef => pure none
      | v => do pure (some (← toIntegerOrInfinityValue v))
    if !Number.FloatOps.tsIsFinite x then pure (.prim (.str (Number.toDecimalString x)))
    else
      match f? with
      | some none => throwJsError .rangeError "toExponential() argument must be between 0 and 100"
      | some (some f) =>
        if f < 0 || 100 < f then
          throwJsError .rangeError "toExponential() argument must be between 0 and 100"
        else pure (.prim (.str (Number.toExponentialString x (some f.toNat))))
      | none => pure (.prim (.str (Number.toExponentialString x none)))
  | .numberToPrecision => do
    let x ← thisNumberValue "toPrecision" thisArg
    match args.headD undefValue with
    | .prim .undef => pure (.prim (.str (Number.toDecimalString x)))
    | v => do
      let p? ← toIntegerOrInfinityValue v
      if !Number.FloatOps.tsIsFinite x then pure (.prim (.str (Number.toDecimalString x)))
      else
        match p? with
        | none => throwJsError .rangeError "toPrecision() argument must be between 1 and 100"
        | some p =>
          if p < 1 || 100 < p then
            throwJsError .rangeError "toPrecision() argument must be between 1 and 100"
          else pure (.prim (.str (Number.toPrecisionString x p.toNat)))
  | .numberToLocaleString => do
    let x ← thisNumberValue "toLocaleString" thisArg
    pure (.prim (.str (Number.toDecimalString x)))
  | .parseFloat => do
    let s ← toStringValue (args.headD undefValue)
    pure (.prim (.num (Number.parseFloat s)))
  | .parseInt => do
    let s ← toStringValue (args.headD undefValue)
    let r ← toNumberValue (args[1]?.getD undefValue)
    pure (.prim (.num (Number.parseInt s (Number.FloatOps.tsToInt32 r))))
  | .booleanCtor => pure (.prim (.bool (toBooleanPrim (args.headD undefValue))))
  | .booleanToString => do
    let b ← thisBooleanValue "toString" thisArg
    pure (.prim (.str (if b then "true" else "false")))
  | .booleanValueOf => do pure (.prim (.bool (← thisBooleanValue "valueOf" thisArg)))
  | .mathAbs => mathUnary Number.FloatOps.tsAbs args
  | .mathCeil => mathUnary Number.FloatOps.tsCeil args
  | .mathFloor => mathUnary Number.FloatOps.tsFloor args
  | .mathFround => mathUnary Number.FloatOps.tsFround args
  | .mathRound => mathUnary Number.FloatOps.tsRound args
  | .mathSign => mathUnary Number.FloatOps.tsSign args
  | .mathSqrt => mathUnary Number.FloatOps.tsSqrt args
  | .mathTrunc => mathUnary Number.FloatOps.tsTrunc args
  | .mathMax => do
    let xs ← toNumberValues args
    pure (.prim (.num (xs.foldl Number.FloatOps.tsMax Number.NEGATIVE_INFINITY)))
  | .mathMin => do
    let xs ← toNumberValues args
    pure (.prim (.num (xs.foldl Number.FloatOps.tsMin Number.POSITIVE_INFINITY)))
  | .mathPow => do
    let base ← toNumberValue (args.headD undefValue)
    let exponent ← toNumberValue (args[1]?.getD undefValue)
    pure (.prim (.num (Number.FloatOps.tsPow base exponent)))
  | .print => do
    -- The host's output binding. There is no IO in `EvalM`, so the line
    -- is appended to `%PrintLog%` and the binary writes the log out once
    -- the run is over; a run that diverges has no log, which is right —
    -- the runner reads a timeout, not a partial transcript.
    let s ← toStringValue (args.headD undefValue)
    let _ ← callNative .arrayPush (.obj printLogRef) [.prim (.str s)]
    pure undefValue
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
    | some (.native n) =>
      -- `Object`, `Array`, and the two wrappers allocate their own
      -- instance against the intrinsic prototype, so `new` hands them no
      -- receiver at all and NewTarget's `prototype` is ignored;
      -- subclassing is #384's.
      if n.constructs then constructNative n args
      else throwJsError .typeError "not a constructor"
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
  | .varDecl kind declarators, acc => do
    evalDeclarators env kind declarators
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
  | .forStmt init test update body, _ => evalForLoop env [] init test update body
  | .switchStmt discriminant cases, _ => evalSwitch env discriminant cases
  | .empty, acc =>
    -- The empty statement completes empty, so the running value stands:
    -- `1; ;` is 1, where `1; undefined;` would be undefined.
    pure acc
  | .block body, acc => evalBlock env body acc
  | .throwStmt argument, _ => do
    let v ← evalExpr env argument
    throwCompletion (.throw v)
  | .tryStmt block handler finalizer, _ => do
    -- The three parts of TryStatement's semantics, in order. The block's
    -- completion is reified rather than propagated, so the finalizer runs
    -- whatever it was; a `catch` replaces it only for a *throw*, which is
    -- why a `return` crossing a `try` is not caught here; and the
    -- finalizer's own abrupt completion escapes this `do` block, which is
    -- exactly the override the spec gives it — `try { return 1; }
    -- finally { return 2; }` is 2.
    let tried ← attempt (evalBlock env block (some undefValue))
    let caught ← match tried, handler with
      | .error (.throw e), some h => attempt (evalCatch env h e)
      | r, _ => pure r
    match finalizer with
    | none => pure ()
    | some fin => do
      let _ ← evalBlock env fin none
      pure ()
    liftCompletion caught
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

/-- CatchClauseEvaluation: the handler's block, run with the thrown value
bound. The binding is mutable — `catch (e) { e = 2; }` is legal — and
lives in a scope holding nothing but itself, so a same-named binding
outside is shadowed for the clause and untouched after it. A clause
without a parameter binds nothing. -/
def evalCatch (env : Env) (h : CatchClause) (e : Value) : EvalM (Option Value) := do
  let inner ← match h.param with
    | none => pure env
    | some name => do
      let r ← allocCell { mutable := true, value := some e }
      pure ((name, r) :: env)
  evalBlock inner h.body (some undefValue)
  partial_fixpoint

/-- InstanceofOperator. `Symbol.hasInstance` is #392's, so this is always
OrdinaryHasInstance: the right operand must be a function, its
`prototype` property must be an object, and the question is whether that
object is on the left operand's prototype chain. A primitive left operand
is not an instance of anything, and says so rather than throwing. -/
def instanceOf (v target : Value) : EvalM Bool := do
  if ← isCallable target then
    match v with
    | .prim _ => pure false
    | .obj o =>
      match ← getProp target "prototype" with
      | .obj p => protoChainHas o p
      | .prim _ =>
        throwJsError .typeError "Function has non-object prototype in instanceof check"
  else
    throwJsError .typeError "Right-hand side of 'instanceof' is not callable"
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
  | .forStmt init test update body, _ => evalForLoop env labels init test update body
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
binding anything new. A `let` or `const` declarator without an
initializer binds `undefined`, which is what makes `let x;` different
from a name in its dead zone; a `var` without one does nothing at all,
because `hoistVars` already put `undefined` in the cell and 14.3.2.1
says `var x;` performs no operation. -/
def evalDeclarators (env : Env) (kind : DeclKind) : List Declarator → EvalM Unit
  | [] => pure ()
  | d :: rest => do
    match kind, d.init with
    | .«var», none => pure ()
    | _, init =>
      let v ← match init with
        | some e => evalExpr env e
        | none => pure undefValue
      match Env.lookup env d.name with
      | some r => initCell r v
      | none => pure ()
    evalDeclarators env kind rest
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

/-- ForLoopEvaluation (14.7.4.2) and its two declaration forms. The head
runs first: a `let` or `const` head gets a scope of its own, so its
bindings are the loop's and not the enclosing block's and a self-
referring initializer sees its own dead zone; a `var` head writes cells
`hoistVars` already made; an expression head is evaluated for effect.
Only a `let` head is copied per iteration (14.7.4.3 step 2 is the first
copy, before the first test), because `const` cannot be updated and a
`var` is not the loop's binding at all. The whole thing is a
BreakableStatement, so an unlabelled `break` ends it with the running
value. -/
def evalForLoop (env : Env) (labels : List String) (init : Option ForInit)
    (test update : Option Expr) (body : Stmt) : EvalM (Option Value) := do
  let (loopEnv, perIter) ← match init with
    | none => pure (env, ([] : List String))
    | some (.expr e) => do
      let _ ← evalExpr env e
      pure (env, [])
    | some (.decl .«var» declarators) => do
      evalDeclarators env .«var» declarators
      pure (env, [])
    | some (.decl kind declarators) => do
      let inner ← hoistDeclarators env kind.isMutable declarators
      evalDeclarators inner kind declarators
      pure (inner, if kind == .«let» then declarators.map (·.name) else [])
  let firstEnv ← copyBindings loopEnv perIter
  match ← attempt (evalFor firstEnv labels test update body perIter (some undefValue)) with
  | .ok v => pure v
  | .error (.«break» none v) => pure v
  | .error c => throwCompletion c
  partial_fixpoint

/-- ForBodyEvaluation (14.7.4.3) — `evalWhile`'s twin, and the second
definition whose equation is `rw`'s and never a simp set's. An absent
test is one that is always true, which is what makes `for (;;)` a loop
with no exit but a `break`.

The order of steps 3.b–3.f is the whole point: the body runs, *then* the
per-iteration bindings are copied, *then* the update runs in the copies.
So a closure the body made keeps this iteration's cell at the value the
body left, and the update writes the next iteration's cell. A `continue`
this loop answers for reaches the copy and the update like a normal
completion; any other completion, `break` included, leaves. -/
def evalFor (env : Env) (labels : List String) (test update : Option Expr)
    (body : Stmt) (perIter : List String) (acc : Option Value) : EvalM (Option Value) := do
  let running ← match test with
    | none => pure true
    | some t => pure (toBooleanPrim (← evalExpr env t))
  if running then
    let v ← match ← attempt (evalStmt env body acc) with
      | .ok v => pure v
      | .error (.«continue» l v) =>
        if loopContinues labels l then pure v else throwCompletion (.«continue» l v)
      | .error c => throwCompletion c
    let env' ← copyBindings env perIter
    match update with
      | none => pure ()
      | some u => do
        let _ ← evalExpr env' u
        pure ()
    evalFor env' labels test update body perIter v
  else
    pure acc
  partial_fixpoint

/-- CaseBlockEvaluation's frame (14.12.4). The discriminant is evaluated
first, then the whole case block is instantiated as *one* scope — before
any clause's test runs, which is why a `let` in a later clause is in its
dead zone for an earlier one. A `switch` is a BreakableStatement, so an
unlabelled `break` ends it with the running value while a `continue`
passes through to the loop around it. -/
def evalSwitch (env : Env) (discriminant : Expr) (cases : List SwitchCase) :
    EvalM (Option Value) := do
  let v ← evalExpr env discriminant
  let inner ← instantiateBlock env (cases.flatMap (·.body))
  match ← attempt (evalCases inner v cases) with
  | .ok r => pure r
  | .error (.«break» none r) => pure r
  | .error c => throwCompletion c
  partial_fixpoint

/-- CaseBlockEvaluation (14.12.2): the clause the discriminant selects
and every clause after it, or — when nothing matched — `default` and
every clause after *it*. The running value starts at `undefined`, so a
`switch` that selects nothing still completes with one. -/
def evalCases (env : Env) (v : Value) (cases : List SwitchCase) : EvalM (Option Value) := do
  match ← selectCase env v cases with
  | some selected => runCases env selected (some undefValue)
  | none => runCases env (dropUntilDefault cases) (some undefValue)
  partial_fixpoint

/-- The clauses from the first one whose test is strictly equal to the
discriminant, or `none` when none is. The tests run in source order and
`default` is skipped, which is exactly 14.12.2's A-clauses-then-B-clauses
order, since every A clause precedes every B clause in the source. A test
that throws ends the `switch`, and the tests after it never run. -/
def selectCase (env : Env) (v : Value) : List SwitchCase → EvalM (Option (List SwitchCase))
  | [] => pure none
  | c :: rest =>
    match c.test with
    | none => selectCase env v rest
    | some t => do
      let tv ← evalExpr env t
      if strictEqValue v tv then pure (some (c :: rest)) else selectCase env v rest
  partial_fixpoint

/-- Run a run of clauses in order, threading the running completion
value. Fall-through is the list running out rather than a jump: a `break`
in one of the bodies is what stops it, and `evalSwitch` catches that. -/
def runCases (env : Env) : List SwitchCase → Option Value → EvalM (Option Value)
  | [], acc => pure acc
  | c :: rest, acc => do
    let v ← evalStmts env c.body acc
    runCases env rest v
  partial_fixpoint

end


/-- Run a whole script from the realm's global environment. The script
body is a block like any other, so it is instantiated first — on top of
`globalEnv`, which is where `Error` and its subclasses are bound.

GlobalDeclarationInstantiation (16.1.7) puts the `var`s in ahead of that,
skipping every name the global environment already has: `var Error;` at
top level leaves `Error` where it was, and `var print = 1;` writes the
existing binding rather than shadowing it with `undefined`. -/
def evalProgram (p : Program) : EvalM (Option Value) := do
  let hoisted ← hoistVars globalEnv (globalEnv.map (·.1)) (varNames p)
  let env ← instantiateBlock hoisted p
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

/-- A thrown object's own ToString, for the report. This is
`Error.prototype.toString` for an `Error`, and the harness's own
`Test262Error.prototype.toString` for a `Test262Error` — which is not an
`Error` subclass at all, so reading the chain would miss it. test262
identifies the class of an uncaught error by name, and the name is what
this line carries. A primitive has no `toString` to run, and an object
with none of its own — every plain object until `Object.prototype`
grows one (#389) — ends abruptly here; both answer `none` and fall back
to the printed form. -/
def thrownSummary (v : Value) : EvalM (Option String) := do
  match v with
  | .prim _ => pure none
  | .obj _ =>
    match ← attempt (toStringValue v) with
    | .ok s => pure (some s)
    | .error _ => pure none

/-- How the binary names a thrown value: the object's own ToString —
`<name>: <message>` for an Error — and its printed form for anything
else, since a script may `throw 1`. The summary is computed in the heap
the throw came out with, since that is where the object is. A `toString`
that itself ends abruptly falls back to the printed form rather than
replacing one uncaught throw with another. -/
def describeThrown (h : Heap) (v : Value) : String :=
  match ((thrownSummary v).run).run h with
  | some (.ok (some s), _) => s
  | _ => formatValue v

/-- What `print` wrote, in order: `%PrintLog%`'s index properties `0 …
length - 1`, the strings among them. The binary reads this after the run
and writes one line per entry. -/
def Heap.printedLines (h : Heap) : List String :=
  match h.objects[printLogRef]? with
  | none => []
  | some o =>
    match o.kind with
    | .array len =>
      (List.range len).filterMap fun i =>
        match o.getOwn (toString i) with
        | some (.prim (.str s)) => some s
        | _ => none
    | _ => []

end Tarski
