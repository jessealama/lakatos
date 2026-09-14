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
their equations are ordinary and `simp` may use them freely. The rule for
the recursive ones is not "recursive" but "recursive on something other
than syntax" — `evalExpr` and its neighbours recurse on a concrete AST,
which runs out, while a loop recurses until a heap value says stop, a
prototype walk until a heap link does, and a join until an array's length
does, and `simp` unfolds all three under a binder it has not resolved,
forever. So the loop arms — `evalWhile`, `evalDoWhile`, `evalFor` — and `joinElements`
never join a simp set at all and are unfolded one step at a time with
`rw`; `getFromUp`, `findAccessorUp`, `protoChainHas`, and `construct`
join `tarski_eval` only as *guarded simprocs* (`Tarski/Simp.lean`), which
fire when the reference they are handed is a literal — which is what a
concrete heap has already resolved, and what the manual `rw` used to wait
for. `getProp` and `getFrom` are plain members: the first is the dispatch
onto the second, and the second answers an own property without
recursing — the two prototype *steps* are what recurse, and they are the
two guarded definitions above. What decides membership in the block is
whether a definition can reach user code: `getProp`, `toPrimitive`, and
`setProp` can (a getter or a setter is user code, ToPrimitive calls
`valueOf`, and ArraySetLength coerces its value with ToNumber, which is
ToPrimitive on an object), so they are inside; `instantiateBlock` and
`makeFunction` only touch the heap, so they are outside.

A block's declarations are instantiated before its first statement runs.
That is one mechanism answering three needs: the temporal dead zone (a
cell exists but holds nothing until its declarator runs), a function
declaration callable above its own text, and two declarations that call
each other.

Four bindings in the scope chain are the evaluator's own rather than any
source name's: `thisName`, `homeName`, `newTargetName`, and
`activeFunctionName`. `this` is a keyword and the other three are
spelled with a `%` or a `.`, so no identifier collides with one; putting
them in the chain rather than in a frame is what lets an arrow see all
four lexically, and what makes a derived constructor's "before
`super()`" the ordinary temporal dead zone with a message of its own.

A class declaration is hoisted like a `let` and is in that same dead zone
until its declaration runs. `evalClass` is ClassDefinitionEvaluation,
`constructClass` a class constructor's `[[Construct]]`, and a field is a
*definition* — never a write — evaluated per instance after `super()`
has returned.

FunctionDeclarationInstantiation (10.2.11) is `instantiateFunction`, the
one place a call's scope is built. Parameters are cells in a dead zone of
their own, initialized left to right, so a default may read a parameter
to its left and not one to its right. With an initializer present the
`var`s get a scope of their own whose cells start from the parameters'
values (step 28); without one they share the parameters' cells (step
27). `arguments` is a source name bound to an immutable cell when — and
only when — the function's own code spells it, which `mentionsArguments`
decides once per function object; without `eval` and the `Function`
constructor, both outside this epic, an unspelled `arguments` cannot be
observed. A function's `length` is ExpectedArgumentCount, an own data
property `makeFunction` and `evalClass` define.

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
| a write through an accessor with no setter         | `TypeError`      | `Cannot set property {key} of #<Object> which has only a getter` |
| a class constructor called without `new`           | `TypeError`      | `Class constructor cannot be invoked without 'new'`           |
| `extends` something that is neither a constructor nor `null` | `TypeError` | `Class extends value {v} is not a constructor or null`   |
| a parent whose `prototype` is neither an object nor `null` | `TypeError` | `Class extends value does not have valid prototype property {p}` |
| `this` read, or a derived constructor finishing, before `super()` | `ReferenceError` | `Must call super constructor in derived class before accessing 'this' or returning from derived constructor` |
| `super()` a second time                            | `ReferenceError` | `Super constructor may only be called once`                   |
| a derived constructor returning a non-`undefined` primitive | `TypeError` | `Derived constructors may only return object or undefined`   |
| `super` where no method is active                  | `SyntaxError`    | `'super' keyword unexpected here`                             |
| the parent of a derived class not a constructor    | `TypeError`      | `Super constructor null of anonymous class is not a constructor` |
| a private name not in scope                        | `SyntaxError`    | `Private field '#{name}' must be declared in an enclosing class` |
| a private read on an object without the element    | `TypeError`      | `Cannot read private member #{name} from an object whose class did not declare it` |
| a private write on an object without the element   | `TypeError`      | `Cannot write private member #{name} to an object whose class did not declare it` |
| a private field initialized twice                  | `TypeError`      | `Cannot initialize #{name} twice on the same object`          |
| `arguments.callee` read or written                 | `TypeError`      | `'caller', 'callee', and 'arguments' properties may not be accessed on strict mode functions or the arguments objects for calls to them` |

The two `SyntaxError`s stand in for early errors the epic does not
check: they are raised where the construct is *used* rather than where
the script is parsed.

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
the latter because ToNumber of `"a"` is NaN and every relation on a NaN
is false.
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
inside one resolves outward like any other name.

It is one of **four reserved bindings**, the other three below. `%` and
`.` are not identifier characters and `this` is a keyword, so no source
name collides with any of them; an arrow sees all four lexically for
free, which is the whole of why an arrow in a constructor may call
`super()`. -/
def thisName : String := "this"

/-- `[[HomeObject]]`'s binding: the object `super.x` reads through,
pushed by a call to a function that has one. -/
def homeName : String := "%home"

/-- NewTarget's binding, spelled as the meta-property itself so that
#486's `MetaProperty` node reads the cell as it stands. -/
def newTargetName : String := "new.target"

/-- The running class constructor's own function object, which is what
`super()` reads the parent constructor off. -/
def activeFunctionName : String := "%function"

/-- The name an `arguments` object is bound under. Unlike the four
above it *is* a source name — `arguments` is an ordinary identifier that
a strict-mode function may not declare or assign, which is an early
error rather than anything checked here — so the binding is pushed only
when the function's own code spells it. -/
def argumentsName : String := "arguments"

/-- Whether a value is a function: an object with a `[[Call]]`. -/
def isCallable (v : Value) : EvalM Bool := do
  match v with
  | .prim _ => pure false
  | .obj r => pure (← readObj r).callable.isSome

/-- IsConstructor: whether `new` may be applied to a value. An ordinary
function and a class constructor may; an arrow and a method may not, and
neither may a built-in without a `[[Construct]]` of its own. `extends`
asks this of its heritage. -/
def isConstructor (v : Value) : EvalM Bool := do
  match v with
  | .prim _ => pure false
  | .obj r =>
    match (← readObj r).callable with
    | none => pure false
    | some (.native n) => pure n.constructs
    | some (.closure c) =>
      match c.kind with
      | .ordinary => pure true
      | .classCtor _ _ => pure true
      | .arrow | .method => pure false

/-- `typeof`'s answer. The object case is the only one needing the heap,
which is why this is not `applyUnary`'s job. -/
def typeofValue (v : Value) : EvalM String := do
  match v with
  | .prim p => pure (typeofName p.typeof)
  | .obj r => pure (if (← readObj r).callable.isSome then "function" else "object")

mutual

/-- ContainsArguments (10.2.11 step 18 reads it through
CreateUnmappedArgumentsObject's guard) over this AST: whether a
function's own code spells the name `arguments` anywhere in its
parameters' initializers or its body.

It descends into an arrow — an arrow has no `arguments` of its own, so
one inside a function body is the function's — and into a class's
`extends` expression, which is evaluated where the class is written. It
stops at a `funcExpr`, a `funcDecl`, and every element of a class body,
each of which has an `arguments` of its own; an `arguments` in a field
initializer is an early error, which this epic does not check.

Pure and structural, so a call still reduces under `simp`. -/
def mentionsArgumentsExpr : Expr → Bool
  | .ident name => name == "arguments"
  | .numLit _ | .strLit _ | .boolLit _ | .undefLit | .nullLit | .this => false
  | .unary _ operand => mentionsArgumentsExpr operand
  | .binary _ l r => mentionsArgumentsExpr l || mentionsArgumentsExpr r
  | .logical _ l r => mentionsArgumentsExpr l || mentionsArgumentsExpr r
  | .cond t c a =>
    mentionsArgumentsExpr t || mentionsArgumentsExpr c || mentionsArgumentsExpr a
  | .member object _ => mentionsArgumentsExpr object
  | .index object key => mentionsArgumentsExpr object || mentionsArgumentsExpr key
  | .privateMember object _ => mentionsArgumentsExpr object
  | .superMember _ => false
  | .superIndex key => mentionsArgumentsExpr key
  | .superCall args => mentionsArgumentsExprs args
  | .call callee args => mentionsArgumentsExpr callee || mentionsArgumentsExprs args
  | .new callee args => mentionsArgumentsExpr callee || mentionsArgumentsExprs args
  | .arrayLit elements => mentionsArgumentsExprs elements
  | .objectLit props => mentionsArgumentsProps props
  -- A function of its own: its `arguments` is its own.
  | .funcExpr _ _ _ => false
  | .arrow params body => mentionsArgumentsParams params || mentionsArgumentsArrow body
  | .assign target value => mentionsArgumentsTarget target || mentionsArgumentsExpr value
  | .compoundAssign _ target value =>
    mentionsArgumentsTarget target || mentionsArgumentsExpr value
  | .update _ _ target => mentionsArgumentsTarget target
  | .classExpr cls => mentionsArgumentsClass cls

/-- A list of expressions; see `mentionsArgumentsExpr`. -/
def mentionsArgumentsExprs : List Expr → Bool
  | [] => false
  | e :: rest => mentionsArgumentsExpr e || mentionsArgumentsExprs rest

/-- An object literal's members; see `mentionsArgumentsExpr`. -/
def mentionsArgumentsProps : List (String × Expr) → Bool
  | [] => false
  | (_, e) :: rest => mentionsArgumentsExpr e || mentionsArgumentsProps rest

/-- An assignment target; see `mentionsArgumentsExpr`. A bare
`arguments = 1` is an early error in strict mode, so the target's own
name is not what this is looking for — but its object expression is. -/
def mentionsArgumentsTarget : Target → Bool
  | .ident name => name == "arguments"
  | .member object _ => mentionsArgumentsExpr object
  | .index object key => mentionsArgumentsExpr object || mentionsArgumentsExpr key
  | .privateMember object _ => mentionsArgumentsExpr object

/-- An arrow's body; see `mentionsArgumentsExpr`. -/
def mentionsArgumentsArrow : ArrowBody → Bool
  | .expr value => mentionsArgumentsExpr value
  | .block body => mentionsArgumentsStmts body

/-- A parameter list's initializers; see `mentionsArgumentsExpr`. -/
def mentionsArgumentsParams : List Param → Bool
  | [] => false
  | ⟨_, none⟩ :: rest => mentionsArgumentsParams rest
  | ⟨_, some d⟩ :: rest => mentionsArgumentsExpr d || mentionsArgumentsParams rest

/-- A class's heritage; see `mentionsArgumentsExpr`. The elements are
not descended into: each has an `arguments` of its own. -/
def mentionsArgumentsClass : ClassDef → Bool
  | ⟨_, none, _⟩ => false
  | ⟨_, some e, _⟩ => mentionsArgumentsExpr e

/-- A statement list; see `mentionsArgumentsExpr`. -/
def mentionsArgumentsStmts : List Stmt → Bool
  | [] => false
  | s :: rest => mentionsArgumentsStmt s || mentionsArgumentsStmts rest

/-- One statement; see `mentionsArgumentsExpr`. -/
def mentionsArgumentsStmt : Stmt → Bool
  | .exprStmt value => mentionsArgumentsExpr value
  | .varDecl _ declarators => mentionsArgumentsDecls declarators
  -- A nested function declaration has an `arguments` of its own.
  | .funcDecl _ _ _ => false
  | .returnStmt none => false
  | .returnStmt (some e) => mentionsArgumentsExpr e
  | .ifStmt test consequent none => mentionsArgumentsExpr test || mentionsArgumentsStmt consequent
  | .ifStmt test consequent (some alternate) =>
    mentionsArgumentsExpr test || mentionsArgumentsStmt consequent ||
      mentionsArgumentsStmt alternate
  | .whileStmt test body => mentionsArgumentsExpr test || mentionsArgumentsStmt body
  | .doWhileStmt body test => mentionsArgumentsStmt body || mentionsArgumentsExpr test
  | .forStmt init none none body => mentionsArgumentsForInit init || mentionsArgumentsStmt body
  | .forStmt init (some t) none body =>
    mentionsArgumentsForInit init || mentionsArgumentsExpr t || mentionsArgumentsStmt body
  | .forStmt init none (some u) body =>
    mentionsArgumentsForInit init || mentionsArgumentsExpr u || mentionsArgumentsStmt body
  | .forStmt init (some t) (some u) body =>
    mentionsArgumentsForInit init || mentionsArgumentsExpr t || mentionsArgumentsExpr u ||
      mentionsArgumentsStmt body
  | .switchStmt discriminant cases =>
    mentionsArgumentsExpr discriminant || mentionsArgumentsCases cases
  | .empty => false
  | .block body => mentionsArgumentsStmts body
  | .throwStmt argument => mentionsArgumentsExpr argument
  | .tryStmt block none none => mentionsArgumentsStmts block
  | .tryStmt block (some ⟨_, handler⟩) none =>
    mentionsArgumentsStmts block || mentionsArgumentsStmts handler
  | .tryStmt block none (some finalizer) =>
    mentionsArgumentsStmts block || mentionsArgumentsStmts finalizer
  | .tryStmt block (some ⟨_, handler⟩) (some finalizer) =>
    mentionsArgumentsStmts block || mentionsArgumentsStmts handler ||
      mentionsArgumentsStmts finalizer
  | .labeled _ body => mentionsArgumentsStmt body
  | .breakStmt _ | .continueStmt _ => false
  | .classDecl _ cls => mentionsArgumentsClass cls

/-- A `for` head; see `mentionsArgumentsExpr`. -/
def mentionsArgumentsForInit : Option ForInit → Bool
  | none => false
  | some (.decl _ declarators) => mentionsArgumentsDecls declarators
  | some (.expr value) => mentionsArgumentsExpr value

/-- A declaration's initializers; see `mentionsArgumentsExpr`. -/
def mentionsArgumentsDecls : List Declarator → Bool
  | [] => false
  | ⟨_, none⟩ :: rest => mentionsArgumentsDecls rest
  | ⟨_, some e⟩ :: rest => mentionsArgumentsExpr e || mentionsArgumentsDecls rest

/-- A `switch`'s clauses; see `mentionsArgumentsExpr`. -/
def mentionsArgumentsCases : List SwitchCase → Bool
  | [] => false
  | ⟨none, body⟩ :: rest => mentionsArgumentsStmts body || mentionsArgumentsCases rest
  | ⟨some e, body⟩ :: rest =>
    mentionsArgumentsExpr e || mentionsArgumentsStmts body || mentionsArgumentsCases rest

end

/-- ContainsArguments over a whole function: its parameters'
initializers and its body. `makeFunction` and `evalClass` compute it once
into `Closure.needsArguments`. -/
def mentionsArguments (params : List Param) (body : List Stmt) : Bool :=
  mentionsArgumentsParams params || mentionsArgumentsStmts body

/-- CreateUnmappedArgumentsObject (10.4.4.7), which is the only kind this
epic has: the epic is strict-mode only, and a strict function's
`arguments` does not alias its parameters, so writing `arguments[0]` does
not move `a` and writing `a` does not move `arguments[0]`.

`length` is the *argument* count, not the parameter count. `callee` is
an accessor whose getter and setter are both `%ThrowTypeError%`, the one
object the realm holds for it. `@@iterator` is #392's and enumerability
#389's, so `Object.keys` of one still lists `length` and `callee`. -/
def makeArguments (args : List Value) : EvalM Value := do
  let r ← allocObj
    { proto := some objectProtoRef,
      kind := .arguments,
      properties := ("length", Value.ofNat args.length) :: indexProps 0 args,
      accessors :=
        [("callee",
          { getter := some (.obj throwTypeErrorRef),
            setter := some (.obj throwTypeErrorRef) })] }
  pure (.obj r)

/-- Allocate a function object. An ordinary function also gets a fresh
`prototype` object whose `constructor` points back at it, which is what
`new` links an instance to; an arrow gets neither, because it cannot be
constructed. That `prototype` is an ordinary object, so it is created
against `Object.prototype` like any other; the function object's own
`[[Prototype]]` stays null until `Function.prototype` exists (#389).

Every function gets an own `length` — ExpectedArgumentCount, so the
parameters before the first default — and every function but an arrow
gets `needsArguments` computed from its own text here, once, rather than
at each call. Writability and enumerability are #389's, as they are for
`prototype`; `name` is #389's too. -/
def makeFunction (c : Closure) : EvalM Value := do
  let needsArguments :=
    match c.kind with
    | .arrow => false
    | _ => mentionsArguments c.params c.body
  let f ← allocObj
    { callable := some (.closure { c with needsArguments }),
      properties := [("length", Value.ofNat (expectedArgumentCount c.params))] }
  match c.kind with
  -- A method has no `prototype` because it cannot be constructed, and a
  -- class constructor's is built by `evalClass`, which needs the object
  -- before the closure that names it exists.
  | .arrow | .method | .classCtor _ _ => pure (.obj f)
  | .ordinary => do
    let proto ← newObject
    modifyObj proto (fun o => o.setOwn "constructor" (.obj f))
    modifyObj f (fun o => o.setOwn "prototype" (.obj proto))
    pure (.obj f)

/-- FunctionDeclarationInstantiation step 21: a mutable, *uninitialized*
cell per parameter name, pushed in order. The cells exist before any
initializer runs, which is what puts a parameter in its own temporal
dead zone — `function f(a = b, b = 1) {}` called with no arguments reads
`b` before initialization — and what lets a default read a parameter to
its left. `initParams` is the step that fills them; the two are separate
because filling one may run user code and allocating cannot. Duplicate
parameter names are a strict-mode early error, so nothing deduplicates
here. -/
def allocParams (env : Env) : List Param → EvalM Env
  | [] => pure env
  | p :: ps => do
    let r ← allocCell { mutable := true }
    allocParams ((p.name, r) :: env) ps

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
  | .doWhileStmt body _ => varNamesStmt body
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

/-- FunctionDeclarationInstantiation step 28, the branch a parameter
list *with* an initializer takes: the `var`s get a scope of their own,
on top of the parameters', and a name that is also a parameter starts
from that parameter's current value rather than from `undefined`. The
copy is what makes the separate scope observable without `eval` — in
`function f(g = () => a, a = 1) { var a = 2; return g(); }` the closure
the default made keeps the parameter's cell, so `f()` is 1 while the
body's `a` ends at 2. `params` is the parameter names, `seen` the names
this pass has already given a cell, so `var x; var x;` allocates one. -/
def hoistVarsFrom (env : Env) (params : List String) (seen : List String) :
    List String → EvalM Env
  | [] => pure env
  | n :: rest =>
    if seen.contains n then hoistVarsFrom env params seen rest
    else do
      let v ←
        if params.contains n then
          match Env.lookup env n with
          | some r => pure ((← getCell r).value.getD undefValue)
          | none => pure undefValue
        else pure undefValue
      let r ← allocCell { mutable := true, value := some v }
      hoistVarsFrom ((n, r) :: env) params (n :: seen) rest

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
      -- A class declaration hoists like a `let`: the cell exists from
      -- here and holds nothing until the declaration runs.
      | .classDecl name _ => do
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

/-- Resolve a private name's spelling to the cell that *is* the name.
The cell is bound under `"#" ++ name` in the class's scope, so an
unbound spelling is a use outside every class that declares it — an
early error in the specification, reported here as a `SyntaxError` at
the point of use, early errors being outside this epic. -/
def privateName (env : Env) (name : String) : EvalM PrivateName :=
  match Env.lookup env ("#" ++ name) with
  | some r => pure r
  | none =>
    throwJsError .syntaxError
      s!"Private field '#{name}' must be declared in an enclosing class"

/-- PrivateGet, restricted to fields: the element on the object itself.
There is no prototype walk — a private element is not a property — so a
base whose class did not declare the name is a `TypeError`, and so is a
primitive base. -/
def readPrivate (env : Env) (base : Value) (name : String) : EvalM Value := do
  let k ← privateName env name
  match base with
  | .obj r =>
    match (← readObj r).getPrivate k with
    | some v => pure v
    | none =>
      throwJsError .typeError
        s!"Cannot read private member #{name} from an object whose class did not declare it"
  | .prim _ =>
    throwJsError .typeError
      s!"Cannot read private member #{name} from an object whose class did not declare it"

/-- PrivateSet, restricted to fields. A write never creates an element:
only field initialization does, which is why a write to an object the
class did not build is a `TypeError` rather than a new field. -/
def writePrivate (env : Env) (base : Value) (name : String) (v : Value) : EvalM Unit := do
  let k ← privateName env name
  match base with
  | .obj r =>
    match (← readObj r).getPrivate k with
    | some _ => modifyObj r (fun o => o.setPrivate k v)
    | none =>
      throwJsError .typeError
        s!"Cannot write private member #{name} to an object whose class did not declare it"
  | .prim _ =>
    throwJsError .typeError
      s!"Cannot write private member #{name} to an object whose class did not declare it"

/-- PrivateFieldAdd. The element must not already be there: it can be,
through the return-override trick, and the specification makes that a
`TypeError` rather than a second element of one name. -/
def addPrivate (target : Ref) (name : String) (k : PrivateName) (v : Value) : EvalM Unit := do
  match (← readObj target).getPrivate k with
  | some _ => throwJsError .typeError s!"Cannot initialize #{name} twice on the same object"
  | none => modifyObj target (fun o => o.addPrivate k v)

/-- One immutable cell per `#name` the class declares, pushed under the
spelling `"#name"`. The cell's *reference* is the Private Name; its
contents are never read, so it holds `undefined`. -/
def bindPrivateNames (env : Env) : List String → EvalM Env
  | [] => pure env
  | n :: rest => do
    let r ← allocCell { mutable := false, value := some undefValue }
    bindPrivateNames (("#" ++ n, r) :: env) rest

/-- MethodDefinitionEvaluation over a class body: every method, getter,
and setter on its home object — the prototype for an instance element,
the constructor for a `static` one. A getter and a setter of one name
merge into one accessor property, which is `Obj.defineAccessor`'s
business. Constructors and fields are not here: the first is the
closure `evalClass` built, the second runs per instance.

Outside the fixpoint block, like `instantiateBlock` and `initFunctions`
and for the same reason: a method's body is closed over here, never run,
so nothing this does can reach user code. -/
def defineMethods (env : Env) (F proto : Ref) : List ClassElement → EvalM Unit
  | [] => pure ()
  | .method kind isStatic name params body :: rest => do
    let target := if isStatic then F else proto
    let f ← makeFunction { params, body, env, kind := .method, homeObject := some target }
    modifyObj target (fun o =>
      match kind with
      | .method => o.defineData name f
      | .getter => o.defineAccessor name (some f) none
      | .setter => o.defineAccessor name none (some f))
    defineMethods env F proto rest
  | _ :: rest => defineMethods env F proto rest

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
    -- than a `ReferenceError`: #389 gives the top level a receiver. A
    -- *bound but uninitialized* one is a derived constructor before its
    -- `super()`, and that has a message of its own rather than the
    -- dead zone's.
    match Env.lookup env thisName with
    | some r => do
      match (← getCell r).value with
      | some v => pure v
      | none =>
        throwJsError .referenceError
          ("Must call super constructor in derived class before accessing 'this' " ++
            "or returning from derived constructor")
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
  | .privateMember object name => do
    let o ← evalExpr env object
    readPrivate env o name
  | .superMember name => do
    let (parent, receiver) ← superBase env
    superRead parent receiver name
  | .superIndex key => do
    let (parent, receiver) ← superBase env
    let k ← evalExpr env key
    superRead parent receiver (← toPropertyKey k)
  | .superCall args => evalSuperCall env args
  | .classExpr cls => evalClass env cls
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
    | .privateMember object name => do
      let base ← evalExpr env object
      let f ← readPrivate env base name
      callFunction f base (← evalExprs env args)
    -- `super.m()` is a method call on the *current* receiver: the
    -- function comes off the parent, the `this` it is handed does not.
    | .superMember name => do
      let (parent, receiver) ← superBase env
      let f ← superRead parent receiver name
      callFunction f receiver (← evalExprs env args)
    | .superIndex key => do
      let (parent, receiver) ← superBase env
      let k ← evalExpr env key
      let f ← superRead parent receiver (← toPropertyKey k)
      callFunction f receiver (← evalExprs env args)
    | _ => do
      let f ← evalExpr env callee
      callFunction f undefValue (← evalExprs env args)
  | .new callee args => do
    let f ← evalExpr env callee
    construct f f (← evalExprs env args)
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
    | .privateMember object name => do
      let base ← evalExpr env object
      let v ← evalExpr env value
      writePrivate env base name v
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
    | .privateMember object name => do
      let base ← evalExpr env object
      let l ← readPrivate env base name
      let r ← evalExpr env value
      let result ← applyCoercing op l r
      writePrivate env base name result
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
    | .privateMember object name => do
      let base ← evalExpr env object
      let old := toNumberPrim (← toPrimitive .number (← readPrivate env base name))
      let stepped := op.step old
      writePrivate env base name (.prim (.num stepped))
      pure (.prim (.num (if isPrefix then stepped else old)))
  partial_fixpoint

/-- SuperCall (13.3.7.1). The parent is the *active function object's*
prototype rather than anything lexical, which is what makes
`Object.setPrototypeOf` on a class change what `super()` reaches; the
NewTarget passed on is the one this constructor was entered with, so a
grandchild's `super()` chain still allocates against the grandchild.

Binding the answer to `this` is BindThisValue: the cell is immutable and
uninitialized, so a second `super()` finds it full and refuses. The
fields run only after the parent has returned, which is why a parent
constructor cannot see a child's field. -/
def evalSuperCall (env : Env) (args : List Expr) : EvalM Value := do
  match Env.lookup env activeFunctionName with
  | none => throwJsError .syntaxError "'super' keyword unexpected here"
  | some fr => do
    match ← readCell activeFunctionName fr with
    | .prim _ => throwJsError .syntaxError "'super' keyword unexpected here"
    | .obj r =>
      match (← readObj r).proto with
      | none =>
        throwJsError .typeError
          "Super constructor null of anonymous class is not a constructor"
      | some parent => do
        let newTarget ←
          match Env.lookup env newTargetName with
          | some ntr => readCell newTargetName ntr
          | none => pure undefValue
        let argv ← evalExprs env args
        let result ← construct (.obj parent) newTarget argv
        match Env.lookup env thisName with
        | none => throwJsError .syntaxError "'super' keyword unexpected here"
        | some tr =>
          match (← getCell tr).value with
          | some _ => throwJsError .referenceError "Super constructor may only be called once"
          | none => initCell tr result
        initializeInstance r result
        pure result
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

This is inside the fixpoint block because a getter is user code called
from here. It is no longer the walk itself, though: `getFrom` is, and
this is the dispatch onto it, so this one may join a simp set while
`getFrom` is unfolded a step at a time like every other heap
recursion. -/
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
  | .prim (.num _) => getFrom numberProtoRef key base
  | .prim (.bool _) => getFrom booleanProtoRef key base
  | .prim _ => pure undefValue
  | .obj r => getFrom r key base
  partial_fixpoint

/-- OrdinaryGet (10.1.8.1): the prototype walk itself, carrying the
*receiver* the read started from. An own accessor property's getter is
called on that receiver rather than on the object the property was found
on, which is what makes an inherited getter see the instance; a getter-
less accessor reads `undefined`. A Number or a Boolean base starts the
walk at its wrapper prototype with the primitive as the receiver, which
is why `thisNumberValue` accepts one.

The walk is `getFromUp`'s, not this one's: what recurses on the heap
rather than on syntax may never join a simp set, so the step is a
definition of its own and `getFrom` is free to be in one. -/
def getFrom (r : Ref) (key : String) (receiver : Value) : EvalM Value := do
  let o ← readObj r
  match o.kind, key == "length" with
  | .array len, true => pure (Value.ofNat len)
  | _, _ =>
    match o.getOwnAccessor key with
    | some a =>
      match a.getter with
      | some g => callFunction g receiver []
      | none => pure undefValue
    | none =>
      match o.getOwn key with
      | some v => pure v
      | none =>
        match o.proto with
        | some p => getFromUp p key receiver
        | none => pure undefValue
  partial_fixpoint

/-- OrdinaryGet's last step, taken on the parent an object named. It is
the *only* recursive part of the read, which is why it is split out:
`getFrom` answers an own property without calling itself, so it may join
a simp set, and a read then costs one `rw [getFromUp]` per prototype link
it has to climb and nothing at all when it finds what it wants where it
started. -/
def getFromUp (parent : Ref) (key : String) (receiver : Value) : EvalM Value :=
  getFrom parent key receiver
  partial_fixpoint

/-- OrdinarySet's search (10.1.9.2) for the accessor a write goes
through: the first own accessor property on the chain, `none` as soon as
an own *data* property — or an array's own `length` — shadows everything
above it, and `none` at the top. Writability is not here, having no
descriptors to read (#389); what is here is the one thing a write cannot
do without, which is finding an inherited setter.

The step up is `findAccessorUp`'s, for the reason `getFrom` gives. -/
def findAccessor (r : Ref) (key : String) : EvalM (Option Accessor) := do
  let o ← readObj r
  match o.getOwnAccessor key with
  | some a => pure (some a)
  | none =>
    if (o.getOwn key).isSome || (o.isArray && key == "length") then pure none
    else
      match o.proto with
      | some p => findAccessorUp p key
      | none => pure none
  partial_fixpoint

/-- `findAccessor`'s prototype step, split out for the reason
`getFromUp` is. -/
def findAccessorUp (parent : Ref) (key : String) : EvalM (Option Accessor) :=
  findAccessor parent key
  partial_fixpoint

/-- Set a property. Strict mode throughout, so a primitive base is a
`TypeError` rather than a silent no-op. An array's own `length` is the
one key whose write is not a property write: assigning to it truncates
or grows, and assigning to an index at or past the end grows the length
to hold it, which is the whole of the Array exotic object's
`[[DefineOwnProperty]]` at this slice's fidelity. Inside the fixpoint
block because that coercion can reach user code, and because a setter
anywhere on the chain is user code too; writability checks arrive with
descriptors (#389). -/
def setProp (base : Value) (key : String) (v : Value) : EvalM Unit :=
  match base with
  | .obj r => do
    -- OrdinarySet: an accessor anywhere on the chain answers the write,
    -- and only a chain with none of them reaches the own-property write
    -- below. A setter-less accessor is a strict-mode `TypeError`.
    match ← findAccessor r key with
    | some a =>
      match a.setter with
      | some s => do
        let _ ← callFunction s base [v]
        pure ()
      | none =>
        throwJsError .typeError
          s!"Cannot set property {key} of #<Object> which has only a getter"
    | none => do
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

/-- IteratorBindingInitialization for a list of single-name bindings
(8.6.2, through FunctionDeclarationInstantiation step 24): the
positional argument, `undefined` past the end of the list, and the
parameter's initializer in place of an argument that *is* `undefined` —
which is why `f(1, undefined)` runs the default and `f(1, null)` does
not. Each initializer is evaluated in the whole parameter scope, so it
sees every parameter to its left initialized and every one to its right
in its dead zone. -/
def initParams (env : Env) : List Param → List Value → EvalM Unit
  | [], _ => pure ()
  | p :: ps, args => do
    let (a, rest) := match args with
      | [] => (undefValue, ([] : List Value))
      | a :: as => (a, as)
    let v ← match p.default, a with
      | some d, .prim .undef => evalExpr env d
      | _, _ => pure a
    match Env.lookup env p.name with
    | some r => initCell r v
    | none => pure ()
    initParams env ps rest
  partial_fixpoint

/-- FunctionDeclarationInstantiation (10.2.11) over what this AST has,
and the one place a call's scope is built: the `arguments` object when
the function's own code spells the name, then the parameters' cells,
then their initializers, then the `var`s, then the body's own
declarations.

The `var`s take one of two branches. With no parameter initializer the
parameters' cells *are* the `var`s' (step 27), so `function f(a) { var
a; }` keeps the argument — that is `hoistVars`, skipping the parameter
names. With one present the `var`s get a scope of their own whose cells
start from the parameters' values (step 28) — that is `hoistVarsFrom`.

`arguments` is an immutable binding, as 10.2.11 step 19 makes it in
strict mode, so `arguments = 1` inside a function is the same refusal an
assignment to a `const` is. -/
def instantiateFunction (env : Env) (c : Closure) (args : List Value) : EvalM Env := do
  let withArgs ←
    if c.needsArguments then do
      let a ← makeArguments args
      let r ← allocCell { mutable := false, value := some a }
      pure ((argumentsName, r) :: env)
    else pure env
  let paramEnv ← allocParams withArgs c.params
  initParams paramEnv c.params args
  let names := Param.names c.params
  let hoisted ←
    if hasDefaults c.params then hoistVarsFrom paramEnv names [] (varNames c.body)
    else hoistVars paramEnv names (varNames c.body)
  instantiateBlock hoisted c.body
  partial_fixpoint

/-- Call a function. The callee's environment is its closure's, plus a
`this` binding for an ordinary function or a method (an arrow pushes
none, so `this` stays lexical), plus its home object when it has one,
plus the parameters, and then the body's own declarations. A class
constructor refuses to be called at all: `new` is its only entry. A `return` is an abrupt completion `catchReturn` turns back
into a value; a body that falls off the end answers `undefined`. -/
def callFunction (f : Value) (thisArg : Value) (args : List Value) : EvalM Value :=
  match f with
  | .prim _ => throwJsError .typeError "not a function"
  | .obj r => do
    let o ← readObj r
    match o.callable with
    | none => throwJsError .typeError "not a function"
    | some (.native (.errorCtor k)) => do
      -- `Error("x")` is `new Error("x")`: an Error constructor called as
      -- a function constructs (20.5.1.1), because with no `new.target` it
      -- falls back to itself. Written out rather than delegated to
      -- `construct` — this is exactly what `construct`'s own errorCtor
      -- arm does after re-reading the same object — so that
      -- `callFunction` does not mention `construct`, or the two unfold
      -- through each other under `simp` and neither guard can stop it.
      let fresh ← allocFromConstructor f k.protoRef
      callNative (.errorCtor k) (.obj fresh) args
    | some (.native n) => callNative n thisArg args
    | some (.closure c) => do
      let withThis ←
        match c.kind with
        | .arrow => pure c.env
        | .ordinary | .method => do
          let tr ← allocCell { mutable := false, value := some thisArg }
          pure ((thisName, tr) :: c.env)
        | .classCtor _ _ =>
          throwJsError .typeError "Class constructor cannot be invoked without 'new'"
      -- A class element carries its home object, which is what `super.x`
      -- reads through; nothing else has one.
      let withHome ←
        match c.homeObject with
        | none => pure withThis
        | some h => do
          let hr ← allocCell { mutable := false, value := some (.obj h) }
          pure ((homeName, hr) :: withThis)
      -- FunctionDeclarationInstantiation: the `arguments` object, the
      -- parameters, the `var`s, and then the block's own declarations,
      -- whose cells are pushed last and so shadow a `var` of the same
      -- name, which is what makes `var f; function f() {}` end as the
      -- function.
      let inner ← instantiateFunction withHome c args
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
object around it, off one conversion. The `Error` constructors are
answered by `construct` itself, which allocates the receiver they fill
in; `Object` and `Array` allocate here.

**Each allocation honours NewTarget**, so `class A extends Array {}`
gives its instances `A.prototype` and `class N extends Number {}` gives
them `N.prototype`; the intrinsic prototype is only the fallback. -/
def constructNative (n : NativeFn) (newTarget : Value) (args : List Value) : EvalM Value :=
  match n with
  | .numberCtor => do
    let x ← numberArg args
    let proto ← allocFromConstructor newTarget numberProtoRef
    modifyObj proto (fun o => { o with kind := .number x })
    pure (.obj proto)
  | .booleanCtor => do
    let b := toBooleanPrim (args.headD undefValue)
    let proto ← allocFromConstructor newTarget booleanProtoRef
    modifyObj proto (fun o => { o with kind := .boolean b })
    pure (.obj proto)
  | .objectCtor =>
    -- `new Object(v)` with a non-nullish `v` answers `v` itself, exactly
    -- as `Object(v)` does, and NewTarget does not enter.
    match args with
    | [] => do pure (.obj (← allocFromConstructor newTarget objectProtoRef))
    | .prim .undef :: _ => do pure (.obj (← allocFromConstructor newTarget objectProtoRef))
    | .prim .null :: _ => do pure (.obj (← allocFromConstructor newTarget objectProtoRef))
    | _ => callNative .objectCtor undefValue args
  | .arrayCtor => do
    -- ArrayCreate is the native's; only the prototype link is NewTarget's,
    -- so the array is re-pointed rather than copied into a second one.
    let arr ← callNative .arrayCtor undefValue args
    match arr with
    | .obj a => do
      match ← getProp newTarget "prototype" with
      | .obj p => do
        modifyObj a (fun o => { o with proto := some p })
        pure arr
      | .prim _ => pure arr
    | v => pure v
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
  | .throwTypeError =>
    -- %ThrowTypeError% (10.2.4.1). Both halves of a strict `arguments`
    -- object's `callee` are this one object, so a read and a write of it
    -- raise the same error.
    throwJsError .typeError
      ("'caller', 'callee', and 'arguments' properties may not be accessed on " ++
        "strict mode functions or the arguments objects for calls to them")
  partial_fixpoint

/-- GetPrototypeFromConstructor (10.1.13) and OrdinaryObjectCreate on
its answer: the instance is linked to **NewTarget's** `prototype`
property when that is an object, and to the intrinsic `fallback`
otherwise. Reading NewTarget rather than the function being run is what
makes `class B extends A {}` produce a `B` — `A`'s body allocates, but
`B` is the NewTarget the allocation sees.

The fallback is the specification's: the intrinsic prototype of the
constructor doing the work, so `Error.prototype` for an `Error` and
`Object.prototype` for an ordinary function. That is a change from the
null this used to link to, and it is observable exactly once, as
`Test/Tarski/ObjectsTest.lean` pins it: after `F.prototype = 1`, a
`new F()` is still an `Object`. -/
def allocFromConstructor (newTarget : Value) (fallback : Ref) : EvalM Ref := do
  let protoVal ← getProp newTarget "prototype"
  let proto := match protoVal with
    | .obj p => some p
    | .prim _ => some fallback
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

/-- `[[Construct]]`. `newTarget` is the spec's NewTarget: the same
function for a plain `new f()`, and the *derived* class for a `super()`
call, which is what gives a subclass's instances the subclass's
prototype. A constructor that returns an object returns that object, and
one that returns anything else returns the instance. An arrow has no
`[[Construct]]`. -/
def construct (f : Value) (newTarget : Value) (args : List Value) : EvalM Value :=
  match f with
  | .prim _ => throwJsError .typeError "not a constructor"
  | .obj r => do
    let o ← readObj r
    match o.callable with
    | none => throwJsError .typeError "not a constructor"
    | some (.native (.errorCtor k)) => do
      -- The native answers the object it was handed, so the
      -- return-object rule below holds trivially and is not written out.
      let fresh ← allocFromConstructor newTarget k.protoRef
      callNative (.errorCtor k) (.obj fresh) args
    | some (.native n) =>
      if n.constructs then constructNative n newTarget args
      else throwJsError .typeError "not a constructor"
    | some (.closure c) =>
      match c.kind with
      | .arrow | .method => throwJsError .typeError "not a constructor"
      | .classCtor derived implicit => constructClass r c derived implicit newTarget args
      | .ordinary => do
        let fresh ← allocFromConstructor newTarget objectProtoRef
        match ← callFunction f (.obj fresh) args with
        | .obj result => pure (.obj result)
        | .prim _ => pure (.obj fresh)
  partial_fixpoint

/-- A class constructor's `[[Construct]]` (15.7.15). The three shapes
are the specification's three: a **base** class allocates the instance
against NewTarget, initializes its fields, and runs the body with `this`
already bound; a **derived** class with a constructor of its own runs the
body with `this` *unbound* and lets `super()` bind it, which is what
makes reading `this` before `super()` the dead zone rather than a special
check; a **derived implicit** constructor — the one a class without a
constructor gets — forwards its arguments to the parent and initializes
the fields on whatever came back.

A base constructor may return anything: an object replaces the instance
and a primitive is ignored. A derived one may not — `undefined` answers
the bound `this` and any other primitive is a `TypeError` — because the
instance it would be discarding is the parent's. -/
def constructClass (r : Ref) (c : Closure) (derived implicit : Bool)
    (newTarget : Value) (args : List Value) : EvalM Value := do
  if derived then
    if implicit then
      match (← readObj r).proto with
      | none =>
        throwJsError .typeError
          "Super constructor null of anonymous class is not a constructor"
      | some parent => do
        let result ← construct (.obj parent) newTarget args
        initializeInstance r result
        pure result
    else do
      let (returned, bound) ← runConstructor r c none newTarget args
      match returned with
      | .obj _ => pure returned
      | .prim .undef =>
        match bound with
        | some t => pure t
        | none =>
          throwJsError .referenceError
            ("Must call super constructor in derived class before accessing 'this' " ++
              "or returning from derived constructor")
      | .prim _ =>
        throwJsError .typeError "Derived constructors may only return object or undefined"
  else do
    let fresh ← allocFromConstructor newTarget objectProtoRef
    initializeInstance r (.obj fresh)
    if implicit then pure (.obj fresh)
    else
      match ← runConstructor r c (some (.obj fresh)) newTarget args with
      | (.obj result, _) => pure (.obj result)
      | (.prim _, _) => pure (.obj fresh)
  partial_fixpoint

/-- A class constructor's body, run in a scope carrying the four
reserved bindings. The `this` cell is **immutable and possibly
uninitialized**: a base constructor gets it filled in, a derived one
gets it empty and `super()` initializes it, so the dead zone the
evaluator already has is the mechanism.

Both the body's answer and the `this` cell's final contents come out,
because a derived constructor's answer depends on the second: the cell
is read once, after the body, since `super()` may have run anywhere
inside it. -/
def runConstructor (r : Ref) (c : Closure) (thisValue : Option Value)
    (newTarget : Value) (args : List Value) : EvalM (Value × Option Value) := do
  let tr ← allocCell { mutable := false, value := thisValue }
  let withThis := (thisName, tr) :: c.env
  let withHome ←
    match c.homeObject with
    | none => pure withThis
    | some h => do
      let hr ← allocCell { mutable := false, value := some (.obj h) }
      pure ((homeName, hr) :: withThis)
  let ntr ← allocCell { mutable := false, value := some newTarget }
  let afr ← allocCell { mutable := false, value := some (.obj r) }
  let env := (activeFunctionName, afr) :: (newTargetName, ntr) :: withHome
  let inner ← instantiateFunction env c args
  let returned ←
    match ← attempt (evalStmts inner c.body none) with
    | .ok _ => pure undefValue
    | .error (.«return» v) => pure v
    | .error e => throwCompletion e
  pure (returned, (← getCell tr).value)
  partial_fixpoint

/-- InitializeInstanceElements: the fields the constructor object
carries, put on the target. The class's own scope and home object come
off the closure, so a field initializer sees the class's private names
and may say `super.x`. -/
def initializeInstance (r : Ref) (target : Value) : EvalM Unit := do
  match (← readObj r).callable with
  | some (.closure c) => initFields c.env c.homeObject target c.fields
  | _ => pure ()
  partial_fixpoint

/-- DefineField over a list, in source order, with `this` and the home
object bound once for the whole run. A field is a **definition**: a
public one goes through `Obj.defineData`, so an inherited setter of the
same name is not called, and a private one is added to the object's
private elements, where a second initialization of one name is a
`TypeError`. -/
def initFields (env : Env) (home : Option Ref) (target : Value)
    (fields : List ClassField) : EvalM Unit := do
  match fields with
  | [] => pure ()
  | _ => do
    let tr ← allocCell { mutable := false, value := some target }
    let withThis := (thisName, tr) :: env
    let inner ←
      match home with
      | none => pure withThis
      | some h => do
        let hr ← allocCell { mutable := false, value := some (.obj h) }
        pure ((homeName, hr) :: withThis)
    initFieldList inner target fields
  partial_fixpoint

/-- `initFields`'s loop, once its scope is built. -/
def initFieldList (env : Env) (target : Value) : List ClassField → EvalM Unit
  | [] => pure ()
  | f :: rest => do
    let v ←
      match f.value with
      | some e => evalExpr env e
      | none => pure undefValue
    match target, f.key with
    | .obj t, .«public» name => modifyObj t (fun o => o.defineData name v)
    | .obj t, .«private» name => do
      let k ← privateName env name
      addPrivate t name k v
    -- The target is always the object being built, so this arm is
    -- unreachable; `Value` is not a subtype.
    | .prim _, _ => pure ()
    initFieldList env target rest
  partial_fixpoint

/-- ClassDefinitionEvaluation (15.7.14), in the specification's order.

The class's own name is an immutable binding in a scope of its own, so
the body can name the class and no outer binding is shadowed for anyone
else; the private names are cells in that same scope. The heritage is
evaluated there, which is why `class A extends A {}` sees its own dead
zone.

`extends` gives two different parents: the *prototype* parent, read off
the superclass's `prototype` property, and the *constructor* parent, the
superclass itself — which is what makes a static method inherited. A
class with no heritage gets `Object.prototype` and no constructor
parent; `extends null` gets neither, so `new` on it can only succeed
through the return-override trick. -/
def evalClass (env : Env) (d : ClassDef) : EvalM Value := do
  let classEnv ←
    match d.name with
    | none => pure env
    | some n => do
      let r ← allocCell { mutable := false }
      pure ((n, r) :: env)
  let inner ← bindPrivateNames classEnv d.privateNames
  let heritage : Option Ref × Option Ref × Bool ←
    match d.superClass with
    | none => pure (some objectProtoRef, none, false)
    | some e => do
      let v ← evalExpr inner e
      match v with
      | .prim .null => pure (none, none, true)
      | _ =>
        if ← isConstructor v then
          let ctorParent := match v with
            | .obj r => some r
            | .prim _ => none
          match ← getProp v "prototype" with
          | .obj p => pure (some p, ctorParent, true)
          | .prim .null => pure (none, ctorParent, true)
          | pv =>
            throwJsError .typeError
              s!"Class extends value does not have valid prototype property {formatValue pv}"
        else
          throwJsError .typeError
            s!"Class extends value {formatValue v} is not a constructor or null"
  let (protoParent, ctorParent, derived) := heritage
  let proto ← allocObj { proto := protoParent }
  let (params, body, implicit) :=
    match d.constructor? with
    | some (ps, b) => (ps, b, false)
    | none => (([] : List Param), ([] : List Stmt), true)
  let ctor : Closure :=
    { params, body, env := inner, kind := .classCtor derived implicit,
      homeObject := some proto, fields := d.instanceFields,
      needsArguments := mentionsArguments params body }
  -- A class constructor's `length` is its parameter list's
  -- ExpectedArgumentCount like any other function's; an implicit
  -- constructor has none, which is the 0 the spec's `constructor(...args)`
  -- also has.
  let F ← allocObj
    { proto := ctorParent, callable := some (.closure ctor),
      properties :=
        [("length", Value.ofNat (expectedArgumentCount params)),
         ("prototype", .obj proto)] }
  modifyObj proto (fun o => o.defineData "constructor" (.obj F))
  defineMethods inner F proto d.elements
  match d.name with
  | none => pure ()
  | some n =>
    match Env.lookup inner n with
    | some r => initCell r (.obj F)
    | none => pure ()
  initFields inner (some F) (.obj F) d.staticFields
  pure (.obj F)
  partial_fixpoint

/-- MakeSuperPropertyReference's first two steps (13.3.7.2): the object
the read will go through — the home object's *prototype* — and the
current `this`, which is the receiver a getter found there will see.

**Both are taken before the property expression runs.** The
specification reads the `this` binding at step 2 and evaluates the key
at step 3, so `super[super()]` inside a derived constructor is the dead
zone's `ReferenceError` and not a read through whatever that `super()`
would have bound. `super` where no home object is bound is a
`SyntaxError` — an early error in the specification, which tsc leaves to
its checker and this epic reports at the point of use. -/
def superBase (env : Env) : EvalM (Option Ref × Value) := do
  match Env.lookup env homeName with
  | none => throwJsError .syntaxError "'super' keyword unexpected here"
  | some hr => do
    let home ← readCell homeName hr
    let receiver ← evalExpr env .this
    match home with
    | .obj h => pure ((← readObj h).proto, receiver)
    | .prim _ => pure (none, receiver)
  partial_fixpoint

/-- The read itself, once `superBase` has the two halves of the
reference. A home object with no prototype reads through null, which is
`getProp`'s own `TypeError` rather than a message of its own. -/
def superRead (parent : Option Ref) (receiver : Value) (key : String) : EvalM Value :=
  match parent with
  | some p => getFrom p key receiver
  | none => getProp (.prim .null) key
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
  | .doWhileStmt body test, _ => evalDoLoop env [] body test
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
  | .classDecl name cls, acc => do
    -- The cell instantiation allocated ends its dead zone here; the
    -- statement itself completes empty, as a function declaration does.
    let v ← evalClass env cls
    match Env.lookup env name with
    | some r => initCell r v
    | none => pure ()
    pure acc
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
  | .doWhileStmt body test, _ => evalDoLoop env labels body test
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

/-- A `do`/`while` as a BreakableStatement — `evalLoop`'s twin. It is a
pair of definitions of its own rather than a flag on the `while` pair
because a body-first iteration is a different equation, and a proof that
unfolds one iteration should do it with one `rw`. -/
def evalDoLoop (env : Env) (labels : List String) (body : Stmt) (test : Expr) :
    EvalM (Option Value) := do
  match ← attempt (evalDoWhile env labels body test (some undefValue)) with
  | .ok v => pure v
  | .error (.«break» none v) => pure v
  | .error c => throwCompletion c
  partial_fixpoint

/-- Run a `do`/`while`'s iterations (14.7.2.2) — `evalWhile`'s twin, with
the body ahead of the test, which is the whole of the difference: the
body runs once whatever the test says. A `continue` this loop answers for
reaches the *test* with the value the body had, rather than leaving; any
other completion, `break` included, leaves, and `evalDoLoop` is where an
unlabelled `break` stops. Never in a simp set: like `evalWhile` it
recurses until a heap value says stop, so it is unfolded one step at a
time with `rw`. -/
def evalDoWhile (env : Env) (labels : List String) (body : Stmt) (test : Expr)
    (acc : Option Value) : EvalM (Option Value) := do
  let v ← match ← attempt (evalStmt env body acc) with
    | .ok v => pure v
    | .error (.«continue» l v) =>
      if loopContinues labels l then pure v else throwCompletion (.«continue» l v)
    | .error c => throwCompletion c
  let t ← evalExpr env test
  if toBooleanPrim t then evalDoWhile env labels body test v else pure v
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
