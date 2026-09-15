import Js
import Tarski.Ast
import Tarski.Json
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
forever. So the loop arms — `evalWhile`, `evalDoWhile`, `evalFor`, and
`evalForOf` — and the list walks — `joinElements`, `listFromArrayLike`,
`forInNext`, the step from one object of a `for`-`in` to its prototype,
and the four walks that run until an iterator says stop (`iteratorToList`,
`fromEntriesInto`, `groupByInto`) — never join a simp set at all and are
unfolded one step at a time with `rw`, as are the three steps a bound
function's target is reached by — `callBound`, `constructBound`, and
`instanceOfBound`. `getFromUp`, `findPropertyUp`,
`protoChainHas`, and `construct` join `tarski_eval` only as *guarded
simprocs* (`Tarski/Simp.lean`), which fire when the reference they are
handed is a literal — which is what a concrete heap has already
resolved, and what the manual `rw` used to wait for. `getProp` and
`getFrom` are plain members: the first is the dispatch onto the second,
and the second answers an own property without recursing — the two
prototype *steps* are what recurse, and they are the two guarded
definitions above. What decides membership in the block is
whether a definition can reach user code: `getProp`, `toPrimitive`, and
`setProp` can (a getter or a setter is user code, ToPrimitive calls
`valueOf`, and ArraySetLength coerces its value with ToNumber, which is
ToPrimitive on an object), so they are inside; `instantiateBlock` and
`makeFunction` only touch the heap, so they are outside.

## The property protocol

Every own property carries the four attributes 6.1.7.1 gives it, and
`Tarski/Value.lean`'s `Obj.applyDescriptor` is 10.1.6.3 as a pure
function, so the table that decides whether a redefinition is legal is
`#guard`-testable without a heap. What is here is the part that throws.

OrdinaryGet is unchanged in shape. **OrdinarySet finds the first own
property on the chain** — `findProperty`, which replaced the old
accessor-only search — and refuses a non-writable data property or an
accessor with no setter; an own write that would *add* a key to a
non-extensible object refuses too. `[[Delete]]` refuses a
non-configurable key. Every one of those refusals is a strict-mode
`TypeError`, this epic having no sloppy mode to be silent in.

NamedEvaluation is one definition, `evalNamed`, called from the four
places the specification gives an anonymous function a name: a
declarator, an assignment to an identifier, an object literal's member,
and a class field. An anonymous function that reaches `evalExpr` any
other way is named `""`, which is what the specification gives it too.

## The iteration protocol

GetIterator, IteratorStepValue, and IteratorClose (7.4.3, 7.4.8, 7.4.11)
are `getIterator`, `iteratorStep`, and `iteratorClose`, three ordinary
members of the block. An Iterator Record here is a `{ iterator, next }`
pair with `next` read **once**, as the specification reads it, and no
`[[Done]]` field at all: *done* is which code path a throw took. A throw
from `next`, from the result's `done`, or from its `value` escapes an
`attempt`-free call and no `return` is called; a throw from anything
between two steps is caught with `attempt` and closes the iterator. That
is 7.4.8–7.4.11 read as control flow, and it is what keeps `iteratorStep`
a plain member and each walk one `attempt`.

Destructuring is one walk, `bindPattern`, for both pattern families:
ESTree gives them one node family and 14.3.3 and 13.15.5 are the same
order. `BindMode` says how a leaf is *written* — `.init` is
InitializeReferencedBinding on a cell instantiation allocated, `.var` and
`.assign` are PutValue — and `LeafRef` is a leaf's reference evaluated
**before** the value is stepped or read, which 13.15.5.4 and 13.15.5.5
require of an assignment pattern and a binding pattern never needs.

`evalForOf` is ForIn/OfBodyEvaluation for `iterate`: the per-iteration
binding is *inside* the `attempt`, because step 6.h closes the iterator
when the binding itself fails, and every exit but exhaustion and a throw
from the iterator closes — a `break`, a `continue` this loop does not
answer for, a `return`, a body throw. Spread and an array literal's
holes are `evalArgs` and `evalArrayElements`: ArgumentListEvaluation and
ArrayAccumulation, each iterating a `.spread` and counting a `.hole`
without defining anything.

`for`-`in` is EnumerateObjectProperties' informative algorithm, 14.7.5.9:
each object's own string keys are snapshotted when that object is
reached, a key is visited only if it is *still* own and enumerable when
its turn comes, and every key already seen shadows the prototypes'. The
keys of one level are data, so only the step to the next object
(`forInNext`) is `rw`'s: a proof unfolds object levels, not keys. The
head is a `ForInLeft` and `bindForIn` the per-iteration binder for a
`for`-`of` too: the two heads are the same production.

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
27). A pattern parameter's names are cells exactly as a plain
parameter's are, and a rest parameter takes every argument left over as a
fresh array. `arguments` is a source name bound to an immutable cell
when — and only when — the function's own code spells it, which
`mentionsArguments` decides once per function object; without `eval` and the `Function`
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
| a write to a non-writable data property            | `TypeError`      | `Cannot assign to read only property '{key}' of object '#<Object>'` |
| a write adding a key to a non-extensible object    | `TypeError`      | `Cannot add property {key}, object is not extensible`         |
| `delete` of a non-configurable key                 | `TypeError`      | `Cannot delete property '{key}' of #<Object>`                 |
| a refused `[[DefineOwnProperty]]`                  | `TypeError`      | `Cannot redefine property: {key}`                             |
| a definition adding a key to a non-extensible object | `TypeError`    | `Cannot define property {key}, object is not extensible`      |
| `Object.defineProperty` on a primitive             | `TypeError`      | `Object.defineProperty called on non-object`                  |
| `Object.defineProperties` on a primitive           | `TypeError`      | `Object.defineProperties called on non-object`                |
| a descriptor argument that is not an object        | `TypeError`      | `Property description must be an object: {v}`                 |
| a descriptor with both kinds of field              | `TypeError`      | `Invalid property descriptor. Cannot both specify accessors and a value or writable attribute` |
| a descriptor `get` that is neither callable nor `undefined` | `TypeError` | `Getter must be a function: {v}`                          |
| a descriptor `set` that is neither callable nor `undefined` | `TypeError` | `Setter must be a function: {v}`                          |
| a prototype that is neither an object nor `null`   | `TypeError`      | `Object prototype may only be an Object or null: {v}`         |
| `Object.setPrototypeOf` on `undefined` or `null`   | `TypeError`      | `Object.setPrototypeOf called on null or undefined`           |
| a prototype change on a non-extensible object      | `TypeError`      | `#<Object> is not extensible`                                 |
| a prototype change on `Object.prototype`           | `TypeError`      | `Immutable prototype object '#<Object>' cannot have their prototype set` |
| a prototype change that would make a cycle         | `TypeError`      | `Cyclic __proto__ value`                                      |
| `in` with a non-object right operand               | `TypeError`      | `Cannot use 'in' operator to search for '{key}' in {v}`       |
| `delete` of a bare identifier                      | `SyntaxError`    | `Delete of an unqualified identifier in strict mode.`         |
| `Function.prototype.toString` off a function       | `TypeError`      | `Function.prototype.toString requires that 'this' be a Function` |
| `Function.prototype.bind` off a function           | `TypeError`      | `Bind must be called on a function`                           |
| `Function.prototype.apply` off a function          | `TypeError`      | `Function.prototype.apply was called on {v}, which is not a function` |
| `apply`'s second argument a non-object             | `TypeError`      | `CreateListFromArrayLike called on non-object`                |
| `Function(...)` reached through an alias           | `TypeError`      | `Function constructor is out of scope`                        |
| GetIterator with no callable `@@iterator`          | `TypeError`      | `{v} is not iterable`                                         |
| an `@@iterator` that answers a primitive           | `TypeError`      | `Result of the Symbol.iterator method is not an object`       |
| a `next` or `return` that answers a primitive      | `TypeError`      | `Iterator result {v} is not an object`                        |
| an iterator's `next` off an iterator of its kind    | `TypeError`      | `next method called on incompatible receiver {v}`             |
| an object pattern destructuring `undefined` or `null` | `TypeError`   | `Cannot destructure '{v}' as it is {undefined\|null}.`        |
| `Object.fromEntries` over a non-object entry       | `TypeError`      | `Iterator value {v} is not an entry object`                   |
| a `.spread` reached outside a list                 | `SyntaxError`    | `Unexpected token '...'`                                      |
| a `.hole` reached outside an array literal         | `SyntaxError`    | `Unexpected token ','`                                        |

The last two `SyntaxError`s are unreachable through the decoder, which
never places a spread or a hole outside the lists that iterate them;
they are stated as the placeholder rows they are. The other three stand
in for early errors the epic does not
check: they are raised where the construct is *used* rather than where
the script is parsed. `Object.prototype.toString`'s tags are not
messages and are not here.

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
  | .str s => Number.stringToNumber s.toStringLossy
  | .bigint _ => floatNaN

/-- ToString on primitives. An object never reaches this — ToPrimitive
runs first — and the number arm is the library's `Number::toString`.
`toPropertyKey` is this and then `JsString.toKey`, and so is the string
arm of `+`. -/
def toStringPrim : JsVal → JsString
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

/-- The refusal a symbol operand of a coercing operator raises. `+` with
a string on the other side is ToString and every other route into the
operators is ToNumeric, and V8 spells the two differently. -/
def symbolOperandRefusal (op : BinaryOp) (other : Value) : String :=
  match op, other with
  | .add, .prim p =>
    if isStrPrim p then "Cannot convert a Symbol value to a string"
    else "Cannot convert a Symbol value to a number"
  | _, _ => "Cannot convert a Symbol value to a number"

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
  | .sym _ => true

/-- `===` on values: the library's test on primitives, reference identity
on objects, and `false` across the two. -/
def strictEqValue : Value → Value → Bool
  | .prim a, .prim b => JsVal.strictEq a b
  | .obj r₁, .obj r₂ => r₁ == r₂
  | .sym a, .sym b => a.id == b.id
  | .prim _, .obj _ => false
  | .prim _, .sym _ => false
  | .obj _, .prim _ => false
  | .obj _, .sym _ => false
  | .sym _, .prim _ => false
  | .sym _, .obj _ => false

/-- Which hint ToPrimitive was called with. `number` is what the
relations and the unary operators use; `string` is what `String(v)`,
`join`, and ToPropertyKey use; `default` is `+`'s, and OrdinaryToPrimitive
treats it exactly as `number` (7.1.1 step 2.d). The three differ only in
the order the two methods are tried in and in the string an
`@@toPrimitive` handler is handed. -/
inductive PrimHint where
  | number
  | string
  | «default»
deriving Repr, DecidableEq, Inhabited

/-- The two method names OrdinaryToPrimitive tries, in the hint's
order. `default` is `number`'s order, as 7.1.1 step 2.d has it. -/
def hintOrder : PrimHint → String × String
  | .number => ("valueOf", "toString")
  | .string => ("toString", "valueOf")
  | .«default» => ("valueOf", "toString")

/-- The hint as an `@@toPrimitive` handler is handed it. -/
def PrimHint.name : PrimHint → String
  | .number => "number"
  | .string => "string"
  | .«default» => "default"

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
`Object.keys` of an array-like whose own properties are its indices. -/
def indexKeys (n : Nat) : List Value :=
  (List.range n).map (fun i => .prim (.str (Nat.repr i)))

/-- CreateDataProperty (7.3.5) on a reference: the definition
`JSON.parse`'s reviver performs, whose `false` the specification does not
report. -/
def createDataProperty (r : Ref) (key : Key) (v : Value) : EvalM Unit := do
  let o ← readObj r
  match o.applyDescriptor key (Property.ordinary v).toDescriptor with
  | some o' => writeObj r o'
  | none => pure ()

/-- `[[Delete]]` with its answer dropped, which is what 25.5.1.1 does to
a member the reviver replaced with `undefined`: a non-configurable one
simply stays. -/
def removeIfConfigurable (r : Ref) (key : Key) : EvalM Unit := do
  let o ← readObj r
  match o.getOwnProperty key with
  | some p => if p.configurable then writeObj r (o.remove key) else pure ()
  | none => pure ()

/-- `Symbol.keyFor`'s scan of `%SymbolRegistry%` (20.4.2.3): the key
whose value is this symbol, or `undefined`. A linear scan, the registry
being a dozen entries at most in any program this evaluator runs. -/
def registryKeyFor : List (Key × Property) → Symbol → Value
  | [], _ => .prim .undef
  | (k, p) :: rest, sy =>
    match k.str?, p.value? with
    | some text, some (.sym s) =>
      if s.id == sy.id then .prim (.str text) else registryKeyFor rest sy
    | _, _ => registryKeyFor rest sy

/-- A run of spaces, `JSON.stringify`'s gap from a numeric `space`. -/
def spaces (n : Nat) : String := String.ofList (List.replicate n ' ')

/-- `JSON.stringify`'s state, built once from its three arguments
(25.5.2 steps 4–6) and carried down the walk: a callable replacer, an
array replacer's PropertyList, and the indent one level costs. -/
structure JsonState where
  /-- The replacer, when it is callable. -/
  replacer : Option Value := none
  /-- An array replacer's keys; `none` is every enumerable own key. -/
  propertyList : Option (List String) := none
  /-- What one level of indentation adds; empty for the compact form. -/
  gap : String := ""
deriving Inhabited

/-- Whether a built-in has a `[[Construct]]`. `Math` is not a function at
all, so it is not here; a `String.prototype` method is a function and not
a constructor, so it is not either. -/
def NativeFn.constructs : NativeFn → Bool
  | .errorCtor _ => true
  | .stringCtor => true
  | .objectCtor => true
  | .arrayCtor => true
  | .numberCtor => true
  | .booleanCtor => true
  -- `Function` is a constructor in the specification, and test262's
  -- `isConstructor.js` asks; what it *does* is the decoder's refusal.
  | .functionCtor => true
  -- 20.4.1: `Symbol` has a `[[Construct]]`, so `isConstructor(Symbol)`
  -- is true and `class X extends Symbol` is well-formed; what it *does*
  -- is `constructNative`'s `TypeError`.
  | .symbolCtor => true
  | .aggregateErrorCtor => true
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

/-- thisSymbolValue (20.4.3): the receiver's symbol, which is the symbol
itself or the `[[SymbolData]]` of a wrapper around one. -/
def thisSymbolValue (who : String) (v : Value) : EvalM Symbol := do
  match v with
  | .sym s => pure s
  | .obj r =>
    match (← readObj r).kind with
    | .symbol s => pure s
    | _ => throwJsError .typeError s!"Symbol.prototype.{who} requires that 'this' be a Symbol"
  | _ => throwJsError .typeError s!"Symbol.prototype.{who} requires that 'this' be a Symbol"

/-- thisStringValue (22.1.3.1): `[[StringData]]`, from the primitive or
from a wrapper around one — the twin of `thisNumberValue`, and the only
thing `toString` and `valueOf` accept. -/
def thisStringValue (who : String) (v : Value) : EvalM JsString := do
  match v with
  | .prim (.str s) => pure s
  | .obj r =>
    match (← readObj r).kind with
    | .string s => pure s
    | _ => throwJsError .typeError s!"String.prototype.{who} requires that 'this' be a String"
  | _ => throwJsError .typeError s!"String.prototype.{who} requires that 'this' be a String"

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
A string is a sequence of UTF-16 code units, so the four relations are
IsLessThan step 3 exactly — **code-unit** order, under which
`"\u{10000}" < "\uFFFF"` is true, where code-point order says the
opposite.
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
  -- `evalExpr` answers `instanceof` and `in` before reaching here, as it
  -- answers `!` and `typeof` before `applyUnary`. Unlike those, these two
  -- arms cannot state their operator's meaning — one walks a prototype
  -- chain and the other asks the heap for a key — so they state what is
  -- true of the primitives they would have been handed: neither is an
  -- instance of anything, and no primitive has a property.
  | .instanceof, _, _ => .prim (.bool false)
  | .«in», _, _ => .prim (.bool false)

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

/-- An argument by position, `undefined` past the end — the `args[i]` of
every built-in's specification text. -/
def argAt (args : List Value) (i : Nat) : Value := args[i]?.getD undefValue

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
  | .sym _ => pure false
  | .obj r => pure (← readObj r).callable.isSome

/-- IsConstructor: whether `new` may be applied to a value. An ordinary
function and a class constructor may; an arrow and a method may not, and
neither may a built-in without a `[[Construct]]` of its own. `extends`
asks this of its heritage. -/
def isConstructor (v : Value) : EvalM Bool := do
  match v with
  | .prim _ => pure false
  | .sym _ => pure false
  | .obj r =>
    match (← readObj r).callable with
    | none => pure false
    | some (.native n) => pure n.constructs
    -- BoundFunctionCreate decided this once, from a target whose
    -- constructibility cannot change, so no walk is needed.
    | some (.bound b) => pure b.constructs
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
  | .sym _ => pure "symbol"
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
  | .objectLit props => mentionsArgumentsPropDefs props
  | .assignPattern p value =>
    mentionsArgumentsPattern p || mentionsArgumentsExpr value
  | .spread argument => mentionsArgumentsExpr argument
  | .hole => false
  | .template _ exprs => mentionsArgumentsExprs exprs
  | .taggedTemplate tag _ _ exprs =>
    mentionsArgumentsExpr tag || mentionsArgumentsExprs exprs
  -- A function of its own: its `arguments` is its own.
  | .funcExpr _ _ _ => false
  | .arrow params body => mentionsArgumentsParams params || mentionsArgumentsArrow body
  | .assign target value => mentionsArgumentsTarget target || mentionsArgumentsExpr value
  | .compoundAssign _ target value =>
    mentionsArgumentsTarget target || mentionsArgumentsExpr value
  | .update _ _ target => mentionsArgumentsTarget target
  | .delete operand => mentionsArgumentsExpr operand
  | .classExpr cls => mentionsArgumentsClass cls

/-- A list of expressions; see `mentionsArgumentsExpr`. -/
def mentionsArgumentsExprs : List Expr → Bool
  | [] => false
  | e :: rest => mentionsArgumentsExpr e || mentionsArgumentsExprs rest

/-- An object literal's members; see `mentionsArgumentsExpr`. A method's
body and parameters are not descended into — a method has an `arguments`
of its own — but its *key* is, because a computed key is evaluated where
the literal is written. -/
def mentionsArgumentsPropDefs : List PropDef → Bool
  | [] => false
  | .init key value :: rest =>
    mentionsArgumentsPropKey key || mentionsArgumentsExpr value
      || mentionsArgumentsPropDefs rest
  | .method _ key _ _ :: rest =>
    mentionsArgumentsPropKey key || mentionsArgumentsPropDefs rest
  | .proto value :: rest =>
    mentionsArgumentsExpr value || mentionsArgumentsPropDefs rest
  | .spread value :: rest =>
    mentionsArgumentsExpr value || mentionsArgumentsPropDefs rest

/-- An object literal member's key; see `mentionsArgumentsExpr`. -/
def mentionsArgumentsPropKey : PropKey → Bool
  | .name _ => false
  | .computed e => mentionsArgumentsExpr e

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

/-- A parameter list's targets and initializers; see
`mentionsArgumentsExpr`. -/
def mentionsArgumentsParams : List Param → Bool
  | [] => false
  | ⟨t, none, _⟩ :: rest => mentionsArgumentsPattern t || mentionsArgumentsParams rest
  | ⟨t, some d, _⟩ :: rest =>
    mentionsArgumentsPattern t || mentionsArgumentsExpr d || mentionsArgumentsParams rest

/-- A pattern's defaults, computed keys, and member leaves; see
`mentionsArgumentsExpr`. -/
def mentionsArgumentsPattern : Pattern → Bool
  | .target t => mentionsArgumentsTarget t
  | .array elements rest =>
    mentionsArgumentsElems elements || mentionsArgumentsPatternOpt rest
  | .object props rest =>
    mentionsArgumentsProps props ||
      (match rest with | none => false | some t => mentionsArgumentsTarget t)

/-- An `ArrayPattern`'s elements; see `mentionsArgumentsExpr`. -/
def mentionsArgumentsElems : List (Option PatternElem) → Bool
  | [] => false
  | none :: rest => mentionsArgumentsElems rest
  | some ⟨t, none⟩ :: rest => mentionsArgumentsPattern t || mentionsArgumentsElems rest
  | some ⟨t, some d⟩ :: rest =>
    mentionsArgumentsPattern t || mentionsArgumentsExpr d || mentionsArgumentsElems rest

/-- An `ObjectPattern`'s properties; see `mentionsArgumentsExpr`. -/
def mentionsArgumentsProps : List PatternProp → Bool
  | [] => false
  | ⟨k, t, none⟩ :: rest =>
    mentionsArgumentsPropKey k || mentionsArgumentsPattern t || mentionsArgumentsProps rest
  | ⟨k, t, some d⟩ :: rest =>
    mentionsArgumentsPropKey k || mentionsArgumentsPattern t || mentionsArgumentsExpr d ||
      mentionsArgumentsProps rest

/-- An `ArrayPattern`'s rest; see `mentionsArgumentsExpr`. -/
def mentionsArgumentsPatternOpt : Option Pattern → Bool
  | none => false
  | some p => mentionsArgumentsPattern p

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
  | .forInStmt (.decl _ p) right body =>
    mentionsArgumentsPattern p || mentionsArgumentsExpr right || mentionsArgumentsStmt body
  | .forInStmt (.target t) right body =>
    mentionsArgumentsTarget t || mentionsArgumentsExpr right || mentionsArgumentsStmt body
  | .forInStmt (.pattern p) right body =>
    mentionsArgumentsPattern p || mentionsArgumentsExpr right || mentionsArgumentsStmt body
  | .forOfStmt (.decl _ p) right body =>
    mentionsArgumentsPattern p || mentionsArgumentsExpr right || mentionsArgumentsStmt body
  | .forOfStmt (.target t) right body =>
    mentionsArgumentsTarget t || mentionsArgumentsExpr right || mentionsArgumentsStmt body
  | .forOfStmt (.pattern p) right body =>
    mentionsArgumentsPattern p || mentionsArgumentsExpr right || mentionsArgumentsStmt body
  | .switchStmt discriminant cases =>
    mentionsArgumentsExpr discriminant || mentionsArgumentsCases cases
  | .empty => false
  | .block body => mentionsArgumentsStmts body
  | .throwStmt argument => mentionsArgumentsExpr argument
  | .tryStmt block none none => mentionsArgumentsStmts block
  | .tryStmt block (some ⟨p, handler⟩) none =>
    mentionsArgumentsStmts block || mentionsArgumentsPatternOpt p ||
      mentionsArgumentsStmts handler
  | .tryStmt block none (some finalizer) =>
    mentionsArgumentsStmts block || mentionsArgumentsStmts finalizer
  | .tryStmt block (some ⟨p, handler⟩) (some finalizer) =>
    mentionsArgumentsStmts block || mentionsArgumentsPatternOpt p ||
      mentionsArgumentsStmts handler || mentionsArgumentsStmts finalizer
  | .labeled _ body => mentionsArgumentsStmt body
  | .breakStmt _ | .continueStmt _ => false
  | .classDecl _ cls => mentionsArgumentsClass cls

/-- A `for` head; see `mentionsArgumentsExpr`. -/
def mentionsArgumentsForInit : Option ForInit → Bool
  | none => false
  | some (.decl _ declarators) => mentionsArgumentsDecls declarators
  | some (.expr value) => mentionsArgumentsExpr value

/-- A declaration's targets and initializers; see
`mentionsArgumentsExpr`. -/
def mentionsArgumentsDecls : List Declarator → Bool
  | [] => false
  | ⟨t, none⟩ :: rest => mentionsArgumentsPattern t || mentionsArgumentsDecls rest
  | ⟨t, some e⟩ :: rest =>
    mentionsArgumentsPattern t || mentionsArgumentsExpr e || mentionsArgumentsDecls rest

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

`length` is the *argument* count, not the parameter count, and it is
writable and configurable but not enumerable; the indices are ordinary
data properties, as CreateDataProperty makes them; `callee` is a
non-enumerable, non-configurable accessor whose getter and setter are
both `%ThrowTypeError%`, the one object the realm holds for it.
`@@iterator` is `%Array.prototype.values%` itself (10.4.4.6 step 8), an
ordinary method property, so `[...arguments]` iterates the indices. -/
def makeArguments (args : List Value) : EvalM Value := do
  let r ← allocObj
    { proto := some objectProtoRef,
      kind := .arguments,
      properties :=
        (Key.str "length", Property.method (Value.ofNat args.length)) :: indexProps 0 args ++
          [(WellKnownSymbol.iterator.key, Property.method (.obj arrayValuesRef)),
           (Key.str "callee",
            { slot := .accessor { getter := some (.obj throwTypeErrorRef),
                                  setter := some (.obj throwTypeErrorRef) },
              enumerable := false, configurable := false })] }
  pure (.obj r)

/-- An Iterator Record (7.4.1) without `[[Done]]`: the iterator object
and its `next`, which GetIterator reads **once**, so replacing `next`
after the loop has started changes nothing. *Done* is not a field here
but a code path — see this module's header. -/
structure IteratorRecord where
  /-- `[[Iterator]]`. -/
  iterator : Value
  /-- `[[NextMethod]]`. -/
  next : Value
deriving Repr, Inhabited

/-- How a destructuring leaf is written. `.init` is
InitializeReferencedBinding on a cell an instantiation already
allocated — a `let`, a `const`, a parameter, a `catch` parameter, a
`for`-`of` declaration head; `.var` and `.assign` are PutValue, which is
`putIdent`, `setProp`, or `writePrivate` by the leaf's shape. -/
inductive BindMode where
  /-- InitializeReferencedBinding into an allocated cell. -/
  | init
  /-- PutValue into a `var`'s binding. -/
  | «var»
  /-- PutValue into an assignment target. -/
  | assign
deriving Repr, DecidableEq, Inhabited

/-- A leaf target's *reference*, evaluated before the value that will be
written to it. 13.15.5.4 and 13.15.5.5 evaluate an assignment pattern's
non-pattern target's reference before the property is read or the
iterator is stepped, which is observable when the object expression has
an effect. -/
inductive LeafRef where
  /-- An `Identifier` leaf. -/
  | ident (name : String)
  /-- A `MemberExpression` leaf, its base and key already evaluated. -/
  | prop (base : Value) (key : Key)
  /-- A private-element leaf. -/
  | priv (base : Value) (name : String)
deriving Repr, Inhabited

/-- CreateIterResultObject (7.4.14): an ordinary object with `value` and
then `done`, in that order, both ordinary data properties. -/
def createIterResult (v : Value) (done : Bool) : EvalM Value := do
  let r ← newObject
  modifyObj r (fun o =>
    (o.define "value" (Property.ordinary v)).define "done"
      (Property.ordinary (.prim (.bool done))))
  pure (.obj r)

/-- The tag `Object.prototype.toString` answers with, 20.1.3.6 steps
4–14 in the specification's order: an Array first, then anything
callable, then the internal-slot classes this slice has. -/
def builtinTag (o : Obj) : String :=
  if o.isArray then "Array"
  else if o.callable.isSome then "Function"
  else
    match o.kind with
    | .arguments => "Arguments"
    | .error => "Error"
    | .boolean _ => "Boolean"
    | .number _ => "Number"
    | .string _ => "String"
    -- 20.1.3.6's table has no `Symbol` row: a Symbol wrapper's
    -- `[object Symbol]` comes from `Symbol.prototype`'s
    -- `@@toStringTag`, which the step after this one reads.
    | _ => "Object"

/-- The NativeFunction form 20.2.3.5 allows for a function whose
`[[SourceText]]` is unavailable. The bridge keeps no source text — the
evaluator is handed an AST, not a script — so this is what every
function's `toString` answers, native, closure, and bound alike. -/
def functionSourceText (name : String) : String :=
  "function " ++ name ++ "() { [native code] }"

/-- A function's `name` as `Function.prototype.toString` reads it: the
own data property, and the empty string for anything else. It is the
stand-in for `[[InitialName]]`, which 20.2.3.5 reads without calling
anything, so this reads the property list rather than going through
`getProp`. `bind`, whose step 12 *is* a `Get`, does not use it. -/
def nameOf (v : Value) : EvalM String := do
  match v with
  | .prim _ => pure ""
  | .sym _ => pure ""
  | .obj r =>
    match (← readObj r).getOwn "name" with
    | some (.prim (.str s)) => pure s.toStringLossy
    | _ => pure ""

/-- ToObject (7.1.18) on a value, shared by the `Object` natives and by
`Object.prototype`'s methods. A Number, a Boolean, or a String gets a
fresh wrapper; a bigint is still the refusal #392 removes.

Outside the fixpoint block: it allocates and it throws, but it cannot
reach user code. -/
def toObjectValue (v : Value) : EvalM Ref :=
  match v with
  | .prim .undef => throwJsError .typeError "Cannot convert undefined or null to object"
  | .prim .null => throwJsError .typeError "Cannot convert undefined or null to object"
  | .obj r => pure r
  | .prim (.num x) => allocObj { proto := some numberProtoRef, kind := .number x }
  | .prim (.bool b) => allocObj { proto := some booleanProtoRef, kind := .boolean b }
  | .sym s => allocObj { proto := some symbolProtoRef, kind := .symbol s }
  | .prim (.str s) => allocObj (Obj.stringWrapper (some stringProtoRef) s)
  | .prim _ => throwJsError .typeError "Cannot convert a primitive to an object"

/-- `[[Delete]]` (10.1.10) behind the `delete` operator, with the
strict-mode `TypeError` at the one refusal: a non-configurable own
property. A key that is not there is `true`, and so is every primitive
base but a string's own `length` or index, which are non-configurable
own properties of the String exotic object. An array's `length` is one
too. Deleting an array element leaves the length alone — the result is a
hole. -/
def deleteProp (base : Value) (key : Key) : EvalM Bool :=
  match base with
  | .prim .undef =>
    throwJsError .typeError s!"Cannot read properties of undefined (reading '{key}')"
  | .prim .null =>
    throwJsError .typeError s!"Cannot read properties of null (reading '{key}')"
  | .prim (.str s) =>
    if key == Key.str "length" || (key.arrayIndex?.any (fun i => i < s.length)) then
      throwJsError .typeError s!"Cannot delete property '{key}' of #<Object>"
    else pure true
  | .prim _ => pure true
  | .sym _ => pure true
  | .obj r => do
    let o ← readObj r
    match o.ownProperty key with
    | none => pure true
    | some p =>
      if p.configurable then do
        writeObj r (o.remove key)
        pure true
      else throwJsError .typeError s!"Cannot delete property '{key}' of #<Object>"

/-- FromPropertyDescriptor (6.2.6.4): the object
`Object.getOwnPropertyDescriptor` answers, whose keys are in the
specification's order — `value`, `writable` or `get`, `set`, then
`enumerable` and `configurable` — each an ordinary data property. -/
def fromProperty (p : Property) : EvalM Value := do
  let r ← newObject
  match p.slot with
  | .data v w =>
    modifyObj r (fun o =>
      (o.define "value" (Property.ordinary v)).define "writable"
        (Property.ordinary (.prim (.bool w))))
  | .accessor a =>
    modifyObj r (fun o =>
      (o.define "get" (Property.ordinary (a.getter.getD (.prim .undef)))).define "set"
        (Property.ordinary (a.setter.getD (.prim .undef))))
  modifyObj r (fun o =>
    (o.define "enumerable" (Property.ordinary (.prim (.bool p.enumerable)))).define "configurable"
      (Property.ordinary (.prim (.bool p.configurable))))
  pure (.obj r)

/-- Allocate a function object, in the order the specification builds
one: OrdinaryFunctionCreate sets `length`, SetFunctionName sets `name`,
and MakeConstructor sets `prototype`, so
`Object.getOwnPropertyNames(function f(a) {})` is
`["length", "name", "prototype"]`.

`length` is ExpectedArgumentCount — the parameters before the first
default. It and `name` are non-writable, non-enumerable, and configurable,
which is what makes `f.name = "x"` a strict-mode refusal while
`Object.defineProperty(f, "name", …)` succeeds. An ordinary function also
gets a fresh `prototype` object whose `constructor` points back at it,
which is what `new` links an instance to; that property is writable and
nothing else, and the object is created against `Object.prototype` like
any other. An arrow gets neither, because it cannot be constructed. The
function object's own `[[Prototype]]` is `Function.prototype`.

The `name` is NamedEvaluation's: `evalNamed` hands the binding's
spelling down, and an anonymous function reached any other way is named
`""`. -/
def makeFunction (c : Closure) (name : String) : EvalM Value := do
  -- Every function but an arrow gets `needsArguments` computed from its
  -- own text here, once, rather than at each call.
  let needsArguments :=
    match c.kind with
    | .arrow => false
    | _ => mentionsArguments c.params c.body
  let f ← allocObj
    { proto := some functionProtoRef,
      callable := some (.closure { c with needsArguments }),
      properties :=
        [ ("length", Property.attribute (Value.ofNat (expectedArgumentCount c.params))),
          ("name", Property.attribute (.prim (.str name))) ] }
  match c.kind with
  -- A method has no `prototype` because it cannot be constructed, and a
  -- class constructor's is built by `evalClass`, which needs the object
  -- before the closure that names it exists.
  | .arrow | .method | .classCtor _ _ => pure (.obj f)
  | .ordinary => do
    let proto ← newObject
    modifyObj proto (fun o => o.define "constructor" (Property.method (.obj f)))
    modifyObj f (fun o => o.define "prototype" (Property.functionPrototype (.obj proto)))
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
def allocNames (env : Env) (mutable : Bool) : List String → EvalM Env
  | [] => pure env
  | n :: rest => do
    let r ← allocCell { mutable }
    allocNames ((n, r) :: env) mutable rest

/-- A cell per parameter-bound name; see `allocNames`. A pattern
parameter's leaves are names like any other. -/
def allocParams (env : Env) (ps : List Param) : EvalM Env :=
  allocNames env true (Param.names ps)

/-- Pass one of block instantiation: a cell per declared name, holding
nothing. A `let` or `const` cell stays uninitialized until its declarator
runs, which is the temporal dead zone; a function declaration's is filled
in by pass two. -/
def hoistDeclarators (env : Env) (mutable : Bool) (ds : List Declarator) : EvalM Env :=
  allocNames env mutable (ds.flatMap (·.target.boundNames))

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
  | .varDecl .«var» declarators => declarators.flatMap (·.target.boundNames)
  | .block body => varNames body
  | .ifStmt _ consequent none => varNamesStmt consequent
  | .ifStmt _ consequent (some alternate) => varNamesStmt consequent ++ varNamesStmt alternate
  | .whileStmt _ body => varNamesStmt body
  | .doWhileStmt body _ => varNamesStmt body
  | .forStmt (some (.decl .«var» declarators)) _ _ body =>
    declarators.flatMap (·.target.boundNames) ++ varNamesStmt body
  | .forStmt _ _ _ body => varNamesStmt body
  -- A `for`-`in` head declares a `var` exactly as a `for` head does; a
  -- `let`, a `const`, and an assignment target declare nothing.
  | .forInStmt (.decl .«var» p) _ body => p.boundNames ++ varNamesStmt body
  | .forInStmt _ _ body => varNamesStmt body
  | .forOfStmt (.decl .«var» p) _ body => p.boundNames ++ varNamesStmt body
  | .forOfStmt _ _ body => varNamesStmt body
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
      let f ← makeFunction { params, body, env, kind := .ordinary } name
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
  | _ =>
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
  | _ =>
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
merge into one accessor property, which is `Obj.defineAccessorHalf`'s
business. Every one of them is non-enumerable and configurable, as
15.4.4 and 15.4.6 have it, and each function's `name` is the key for a
method and `"get x"` or `"set x"` for an accessor half.
Constructors and fields are not here: the first is the closure
`evalClass` built, the second runs per instance.

Outside the fixpoint block, like `instantiateBlock` and `initFunctions`
and for the same reason: a method's body is closed over here, never run,
so nothing this does can reach user code. -/
def defineMethods (env : Env) (F proto : Ref) : List ClassElement → EvalM Unit
  | [] => pure ()
  | .method kind isStatic name params body :: rest => do
    let target := if isStatic then F else proto
    let fname := match kind with
      | .method => name
      | .getter => "get " ++ name
      | .setter => "set " ++ name
    let f ← makeFunction { params, body, env, kind := .method, homeObject := some target } fname
    modifyObj target (fun o =>
      match kind with
      | .method => o.define name (Property.method f)
      | .getter => o.defineAccessorHalf name (some f) none false true
      | .setter => o.defineAccessorHalf name none (some f) false true)
    defineMethods env F proto rest
  | _ :: rest => defineMethods env F proto rest

/-- GetTemplateObject (13.2.8.4). The realm's `[[TemplateMap]]` is
`%TemplateMap%`, an object whose own keys are the decoder's site numbers,
so one site evaluated twice hands its tag the *identical* object and two
sites with the same text do not. The template object is an array of the
cooked strings — `undefined` where the cooked value is absent — carrying
the raw strings as `raw`, a non-writable, non-enumerable, non-configurable
property; both arrays are frozen, as steps 12 and 15 have them, so a
write to either is the strict-mode `TypeError` a frozen write is.

Outside the fixpoint block with `makeFunction`: it only touches the
heap, and nothing it does can reach user code. -/
def getTemplateObject (site : Nat) (strings : List TemplateString) : EvalM Value := do
  let key := Nat.repr site
  match (← readObj templateMapRef).getOwn key with
  | some t => pure t
  | none => do
    let raw ← allocObj ((Obj.array (some arrayProtoRef)
      (strings.map (fun s => Value.prim (.str s.raw)))).setIntegrity true)
    let t ← allocObj ((Obj.array (some arrayProtoRef)
      (strings.map (fun s =>
        match s.cooked with
        | some c => Value.prim (.str c)
        | none => undefValue))).define "raw" (Property.constant (.obj raw)) |>.setIntegrity true)
    modifyObj templateMapRef (fun o => o.setOwn key (.obj t))
    pure (.obj t)

-- The interpreter's block is one `partial_fixpoint` strongly connected
-- component of some sixty definitions, and both elaboration and code
-- generation run past the default heartbeat limit on it. That limit
-- guards against a search that will not stop; there is no search here,
-- only a large definition, so raising it is the knob rather than
-- splitting a block whose whole point is that its members may call one
-- another.
set_option maxHeartbeats 2000000 in
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
      match ← toPrimitive .number v with
      | .prim p => pure (applyUnary op p)
      | other => throwJsError .typeError (symbolOperandRefusal .sub other)
  | .binary op left right => do
    let l ← evalExpr env left
    let r ← evalExpr env right
    match op with
    | .instanceof => pure (.prim (.bool (← instanceOf l r)))
    | .«in» => do
      -- RelationalExpression : RelationalExpression `in` ShiftExpression
      -- (13.10.1): ToPropertyKey first, then HasProperty, so a poisoned
      -- key's `toString` runs even against a primitive right operand.
      let key ← toPropertyKey l
      match r with
      | .obj o => pure (.prim (.bool (← hasProperty o key)))
      | _ =>
        throwJsError .typeError
          s!"Cannot use 'in' operator to search for '{key}' in {formatValue r}"
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
  | .classExpr cls => evalClass env cls ""
  | .delete operand =>
    -- 13.5.1. A bare identifier is the strict-mode early error, reported
    -- here rather than at parse time; a property reference is
    -- `[[Delete]]`; anything else is evaluated for its effects and
    -- answers `true`, references being the only things `delete` deletes.
    match operand with
    | .ident _ =>
      throwJsError .syntaxError "Delete of an unqualified identifier in strict mode."
    | .member object name => do
      let base ← evalExpr env object
      pure (.prim (.bool (← deleteProp base name)))
    | .index object key => do
      let base ← evalExpr env object
      let k ← evalExpr env key
      pure (.prim (.bool (← deleteProp base (← toPropertyKey k))))
    | e => do
      let _ ← evalExpr env e
      pure (.prim (.bool true))
  | .call callee args => do
    let fr ← evalCallee env callee
    callFunction fr.1 fr.2 (← evalArgs env args)
  | .new callee args => do
    let f ← evalExpr env callee
    construct f f (← evalArgs env args)
  | .objectLit props => do
    let r ← newObject
    evalPropDefs env props r
    pure (.obj r)
  | .template strings exprs => evalTemplate env strings exprs ""
  -- 13.3.11.1: the tag's reference first, then GetTemplateObject, then
  -- the substitutions, which the tag receives after the template object.
  | .taggedTemplate tag site strings exprs => do
    let fr ← evalCallee env tag
    let t ← getTemplateObject site strings
    callFunction fr.1 fr.2 (t :: (← evalExprs env exprs))
  -- ArrayLiteral (13.2.4.2): a fresh array, then ArrayAccumulation,
  -- then `Set(array, "length", n)` — which on an array nobody else has
  -- seen is one field write.
  | .arrayLit elements => do
    let r ← allocObj (Obj.array (some arrayProtoRef) [])
    let n ← evalArrayElements env r 0 elements
    modifyObj r (fun o => { o with kind := .array n true })
    pure (.obj r)
  -- DestructuringAssignmentEvaluation (13.15.5): the value of the whole
  -- expression is the *right* operand's, whatever the pattern wrote.
  | .assignPattern p value => do
    let v ← evalExpr env value
    bindPattern env .assign p v
    pure v
  -- Neither can be reached through the decoder, which places a spread
  -- only in a list that iterates it and a hole only in an array literal.
  | .spread _ => throwJsError .syntaxError "Unexpected token '...'"
  | .hole => throwJsError .syntaxError "Unexpected token ','"

  | .funcExpr name params body =>
    match name with
    -- An anonymous function reached any way but NamedEvaluation's four
    -- is named the empty string, which is what the specification gives
    -- it: `(function () {}).name` is `""`.
    | none => makeFunction { params, body, env, kind := .ordinary } ""
    | some n => do
      -- A named function expression binds its own name, immutably, in a
      -- scope holding nothing else, so the body can recurse through it
      -- and no outer binding is shadowed for anyone else.
      let r ← allocCell { mutable := false }
      let inner := (n, r) :: env
      let f ← makeFunction { params, body, env := inner, kind := .ordinary } n
      initCell r f
      pure f
  | .arrow params body =>
    -- A concise body is a `return` of its expression: the two forms
    -- differ in syntax only, so `Closure` carries one shape.
    match body with
    | .block b => makeFunction { params, body := b, env, kind := .arrow } ""
    | .expr e =>
      makeFunction { params, body := [.returnStmt (some e)], env, kind := .arrow } ""
  | .assign target value =>
    match target with
    | .ident name => do
      -- NamedEvaluation: `x = function () {}` names the function `x`.
      let v ← evalNamed env name value
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
      let old ← toNumberValue (← evalExpr env (.ident name))
      let stepped := op.step old
      putIdent env name (.prim (.num stepped))
      pure (.prim (.num (if isPrefix then stepped else old)))
    | .member object name => do
      let base ← evalExpr env object
      let old ← toNumberValue (← getProp base name)
      let stepped := op.step old
      setProp base name (.prim (.num stepped))
      pure (.prim (.num (if isPrefix then stepped else old)))
    | .index object key => do
      let base ← evalExpr env object
      let k ← toPropertyKey (← evalExpr env key)
      let old ← toNumberValue (← getProp base k)
      let stepped := op.step old
      setProp base k (.prim (.num stepped))
      pure (.prim (.num (if isPrefix then stepped else old)))
    | .privateMember object name => do
      let base ← evalExpr env object
      let old ← toNumberValue (← readPrivate env base name)
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
    | .obj r =>
      -- GetSuperConstructor is the active function's `[[Prototype]]`.
      -- `class A extends null {}` gives that `%Function.prototype%`
      -- (15.7.14 step 10.b), which is callable and not a constructor, so
      -- the refusal is the same one a missing parent gets.
      match ← superConstructor r with
      | none =>
        throwJsError .typeError
          "Super constructor null of anonymous class is not a constructor"
      | some parent => do
        let newTarget ←
          match Env.lookup env newTargetName with
          | some ntr => readCell newTargetName ntr
          | none => pure undefValue
        let argv ← evalArgs env args
        let result ← construct (.obj parent) newTarget argv
        match Env.lookup env thisName with
        | none => throwJsError .syntaxError "'super' keyword unexpected here"
        | some tr =>
          match (← getCell tr).value with
          | some _ => throwJsError .referenceError "Super constructor may only be called once"
          | none => initCell tr result
        initializeInstance r result
        pure result
    | _ => throwJsError .syntaxError "'super' keyword unexpected here"
  partial_fixpoint

/-- ApplyStringOrNumericBinaryOperator: ToPrimitive on each operand with
the number hint, left first, and then the operator. `a op b` and
`a op= b` are the same computation once each side has a value, which is
what this names. -/
def applyCoercing (op : BinaryOp) (l r : Value) : EvalM Value := do
  let hint := match op with | .add => PrimHint.«default» | _ => PrimHint.number
  let lp ← toPrimitive hint l
  let rp ← toPrimitive hint r
  match lp, rp with
  | .prim a, .prim b => pure (applyBinary op a b)
  | .sym _, _ => throwJsError .typeError (symbolOperandRefusal op rp)
  | _, .sym _ => throwJsError .typeError (symbolOperandRefusal op lp)
  -- ToPrimitive never answers an object, so the last two arms cannot be
  -- reached; the message is the one a failed ToPrimitive would give.
  | _, _ => throwJsError .typeError "Cannot convert object to primitive value"
  partial_fixpoint

/-- GetIterator (7.4.3) for the sync hint. `next` is read once, here,
which is what makes replacing it mid-loop unobservable. A nullish operand
is answered before the lookup, as V8 answers it. -/
def getIterator (v : Value) : EvalM IteratorRecord := do
  match v with
  | .prim .undef | .prim .null =>
    throwJsError .typeError s!"{formatValue v} is not iterable"
  | _ => do
    let m ← getProp v WellKnownSymbol.iterator.key
    if ← isCallable m then
      match ← callFunction m v [] with
      | .obj r => do
        let next ← getProp (.obj r) "next"
        pure { iterator := .obj r, next }
      | _ =>
        throwJsError .typeError "Result of the Symbol.iterator method is not an object"
    else throwJsError .typeError s!"{formatValue v} is not iterable"
  partial_fixpoint

/-- IteratorStepValue (7.4.8): one step, `none` when the iterator said it
was done. A throw from the call, from `done`, or from `value` propagates
uncaught — 7.4.8 sets `[[Done]]` and rethrows, and nothing closes an
iterator that threw for itself. -/
def iteratorStep (ir : IteratorRecord) : EvalM (Option Value) := do
  match ← callFunction ir.next ir.iterator [] with
  | .obj r => do
    if toBooleanPrim (← getProp (.obj r) "done") then pure none
    else pure (some (← getProp (.obj r) "value"))
  | v => throwJsError .typeError s!"Iterator result {formatValue v} is not an object"
  partial_fixpoint

/-- IteratorClose (7.4.11). When the completion being carried out is a
throw, every outcome of reading and calling `return` is discarded (step
5), so the original throw is what reaches the caller; otherwise a
`return` that is absent or nullish is nothing, a non-callable one is the
ordinary `not a function`, a throwing one propagates, and one answering a
primitive is the `Iterator result` refusal. The caller rethrows the
completion it was carrying. -/
def iteratorClose (ir : IteratorRecord) (c : Option Completion) : EvalM Unit := do
  match c with
  | some (.throw _) => do
    let _ ← attempt (do
      match ← getProp ir.iterator "return" with
      | .prim .undef | .prim .null => pure ()
      | ret => do
        let _ ← callFunction ret ir.iterator []
        pure ())
    pure ()
  | _ => do
    match ← getProp ir.iterator "return" with
    | .prim .undef | .prim .null => pure ()
    | ret => do
      match ← callFunction ret ir.iterator [] with
      | .obj _ => pure ()
      | v => throwJsError .typeError s!"Iterator result {formatValue v} is not an object"
  partial_fixpoint

/-- IteratorToList (7.4.13): step until the iterator says stop. A throw
escapes, the iterator having thrown for itself. Recurses until a heap
value says stop, so it is `rw`'s and never a simp set's. -/
def iteratorToList (ir : IteratorRecord) : EvalM (List Value) := do
  match ← iteratorStep ir with
  | none => pure []
  | some v => do pure (v :: (← iteratorToList ir))
  partial_fixpoint

/-- A leaf target's reference, evaluated before the value it will be
written. An `Identifier` has nothing to evaluate; a member's object —
and a computed member's key — are evaluated here and once. -/
def evalLeafRef (env : Env) : Target → EvalM LeafRef
  | .ident n => pure (.ident n)
  | .member object name => do pure (.prop (← evalExpr env object) name)
  | .index object key => do
    let base ← evalExpr env object
    let k ← evalExpr env key
    pure (.prop base (← toPropertyKey k))
  | .privateMember object name => do pure (.priv (← evalExpr env object) name)
  partial_fixpoint

/-- Write one value through an already-evaluated leaf reference.
`.init` ends a cell's dead zone, which is what a declaration, a
parameter, a `catch` parameter, and a `for`-`of` declaration head do; the
other two modes are PutValue. A missing cell under `.init` cannot happen —
`allocNames` ran — and is `pure ()` as `initParams` has it. -/
def writeLeaf (env : Env) (mode : BindMode) : LeafRef → Value → EvalM Unit
  | .ident n, v =>
    match mode with
    | .init =>
      match Env.lookup env n with
      | some r => initCell r v
      | none => pure ()
    | _ => putIdent env n v
  | .prop base key, v => setProp base key v
  | .priv base name, v => writePrivate env base name v
  partial_fixpoint

/-- One walk for both pattern families (14.3.3 and 13.15.5), `mode`
deciding how a leaf is written. An object pattern is RequireObjectCoercible
and then its properties in source order; an array pattern is GetIterator,
its elements, its rest, and then IteratorClose on every exit but
exhaustion. -/
def bindPattern (env : Env) (mode : BindMode) : Pattern → Value → EvalM Unit
  | .target t, v => do writeLeaf env mode (← evalLeafRef env t) v
  | .object props rest, v => do
    match v with
    | .prim .undef | .prim .null =>
      throwJsError .typeError
        s!"Cannot destructure '{formatValue v}' as it is {formatValue v}."
    | _ => pure ()
    let seen ← bindProps env mode v [] props
    match rest with
    | none => pure ()
    | some t => do
      -- The rest's reference first, then a fresh ordinary object holding
      -- every own enumerable key the listed properties did not take.
      let lr ← evalLeafRef env t
      let r ← newObject
      copyDataProperties r v seen
      writeLeaf env mode lr (.obj r)
  | .array elements rest, v => do
    let ir ← getIterator v
    let (r, done) ← bindElements env mode ir false elements
    let (r', done') ←
      match r, rest with
      | .ok (), some p => bindRest env mode ir done p
      | _, _ => pure (r, done)
    if !done' then
      iteratorClose ir (match r' with | .ok () => none | .error c => some c)
    match r' with
    | .ok () => pure ()
    | .error c => throwCompletion c
  partial_fixpoint

/-- An assignment pattern evaluates a leaf target's *reference* before
the value is read or stepped (13.15.5.4, 13.15.5.5); a binding pattern
has none to evaluate, and neither does a nested pattern. -/
def patternLeafRef (env : Env) (mode : BindMode) : Pattern → EvalM (Option LeafRef)
  | .target t =>
    match mode with
    | .assign => do pure (some (← evalLeafRef env t))
    | _ => pure none
  | _ => pure none
  partial_fixpoint

/-- Write one destructuring element: the default in place of an
`undefined` value, then the leaf reference an assignment pattern already
evaluated or the nested pattern. It is one definition so that each caller
can hand the whole of it to `attempt` as a plain application, which is
what the monotonicity prover can see through. -/
def bindOne (env : Env) (mode : BindMode) (l : Option LeafRef) (target : Pattern)
    (dflt : Option Expr) (v : Value) : EvalM Unit := do
  let value ←
    match dflt, v with
    | some d, .prim .undef =>
      -- NamedEvaluation: a SingleNameBinding's default is named for it;
      -- a pattern's and a member leaf's are not.
      match target with
      | .target (.ident n) => evalNamed env n d
      | _ => evalExpr env d
    | _, _ => pure v
  match l with
  | some leaf => writeLeaf env mode leaf value
  | none => bindPattern env mode target value
  partial_fixpoint

/-- An object pattern's properties, in source order, answering the keys
it read so the rest can exclude them. The key is evaluated first, then —
in an assignment pattern with a leaf target — the target's reference,
then GetV, then the default, then the write (13.15.5.4). -/
def bindProps (env : Env) (mode : BindMode) (v : Value) (seen : List Key) :
    List PatternProp → EvalM (List Key)
  | [] => pure seen
  | p :: rest => do
    let k ← evalPropKey env p.key
    let lr ← patternLeafRef env mode p.target
    let x ← getProp v k
    bindOne env mode lr p.target p.default x
    bindProps env mode v (k :: seen) rest
  partial_fixpoint

/-- An array pattern's elements (14.3.3.2, 13.15.5.5). An elision steps
the iterator and binds nothing. An element evaluates its leaf's reference
first in an assignment pattern, then steps, then takes its default, then
writes; the step's own throw escapes, and every other throw is reified so
the caller can close. The `Bool` is whether the iterator is exhausted. -/
def bindElements (env : Env) (mode : BindMode) (ir : IteratorRecord) (done : Bool) :
    List (Option PatternElem) → EvalM (Except Completion Unit × Bool)
  | [] => pure (.ok (), done)
  | none :: rest => do
    let done' ←
      if done then pure true
      else
        match ← iteratorStep ir with
        | none => pure true
        | some _ => pure false
    bindElements env mode ir done' rest
  | some e :: rest => do
    match ← attempt (patternLeafRef env mode e.target) with
    | .error c => pure (.error c, done)
    | .ok l => do
      let (v, done') ←
        if done then pure (undefValue, true)
        else
          match ← iteratorStep ir with
          | none => pure (undefValue, true)
          | some v => pure (v, false)
      match ← attempt (bindOne env mode l e.target e.default v) with
      | .ok () => bindElements env mode ir done' rest
      | .error c => pure (.error c, done')
  partial_fixpoint

/-- An array pattern's `RestElement`: every value left, as a fresh array.
The leaf's reference comes first in an assignment pattern, and the walk
to exhaustion is what makes the answer's second component `true` — a rest
never leaves an iterator open. -/
def bindRest (env : Env) (mode : BindMode) (ir : IteratorRecord) (done : Bool)
    (p : Pattern) : EvalM (Except Completion Unit × Bool) := do
  match ← attempt (patternLeafRef env mode p) with
  | .error c => pure (.error c, done)
  | .ok l => do
    let xs ← if done then pure ([] : List Value) else iteratorToList ir
    let arr ← newArray xs
    match ← attempt (bindOne env mode l p none arr) with
    | .ok () => pure (.ok (), true)
    | .error c => pure (.error c, true)
  partial_fixpoint

/-- CopyDataProperties (7.3.26). A nullish source copies nothing; every
other primitive goes through ToObject, which is where a string meets
#391's refusal until the wrapper object exists. -/
def copyDataProperties (target : Ref) (source : Value) (excluded : List Key) :
    EvalM Unit := do
  match source with
  | .prim .undef | .prim .null => pure ()
  | _ => do
    let src ← toObjectValue source
    copyKeys target src excluded (← readObj src).ownKeys
  partial_fixpoint

/-- CopyDataProperties' key walk: each own enumerable key not excluded,
read through the source and *defined* on the target. -/
def copyKeys (target src : Ref) (excluded : List Key) : List Key → EvalM Unit
  | [] => pure ()
  | k :: rest => do
    if excluded.contains k then pure ()
    else
      -- `ownProperty` rather than `getOwnProperty`, so a String exotic
      -- object's synthesized indices are seen: `{ ..."ab" }` is two
      -- members.
      match (← readObj src).ownProperty k with
      | some prop =>
        if prop.enumerable then createDataProperty target k (← getProp (.obj src) k)
        else pure ()
      | none => pure ()
    copyKeys target src excluded rest
  partial_fixpoint

/-- ArgumentListEvaluation (13.3.8.1): the arguments left to right, a
`.spread` iterated in place. It replaces `evalExprs` at the three call
sites that admit a spread; a template's substitutions cannot have one and
keep `evalExprs`. -/
def evalArgs (env : Env) : List Expr → EvalM (List Value)
  | [] => pure []
  | .spread e :: rest => do
    let ir ← getIterator (← evalExpr env e)
    let vs ← iteratorToList ir
    let ws ← evalArgs env rest
    pure (vs ++ ws)
  | e :: rest => do
    let v ← evalExpr env e
    let vs ← evalArgs env rest
    pure (v :: vs)
  partial_fixpoint

/-- ArrayAccumulation (13.2.4.1) into an already-allocated array,
answering the next index. A hole advances the index and defines nothing,
which is what makes `1 in [1, , 2]` false; a spread is iterated and its
values defined one by one. -/
def evalArrayElements (env : Env) (r : Ref) (i : Nat) : List Expr → EvalM Nat
  | [] => pure i
  | .hole :: rest => evalArrayElements env r (i + 1) rest
  | .spread e :: rest => do
    let ir ← getIterator (← evalExpr env e)
    let vs ← iteratorToList ir
    let n ← defineFrom r i vs
    evalArrayElements env r n rest
  | e :: rest => do
    let v ← evalExpr env e
    createDataProperty r (Nat.repr i) v
    evalArrayElements env r (i + 1) rest
  partial_fixpoint

/-- CreateDataPropertyOrThrow at consecutive indices, answering the next
one. On a fresh array no definition can refuse. -/
def defineFrom (r : Ref) (i : Nat) : List Value → EvalM Nat
  | [] => pure i
  | v :: rest => do
    createDataProperty r (Nat.repr i) v
    defineFrom r (i + 1) rest
  partial_fixpoint

/-- AddEntriesFromIterable (24.1.1.2) for `Object.fromEntries`: each
value must be an object, its `"0"` is the key and its `"1"` the value,
and any throw between two steps closes the iterator. -/
def fromEntriesInto (ir : IteratorRecord) (obj : Ref) : EvalM Unit := do
  match ← iteratorStep ir with
  | none => pure ()
  | some e =>
    match ← attempt (do
      match e with
      | .obj _ => do
        let k ← getProp e "0"
        let v ← getProp e "1"
        createDataProperty obj (← toPropertyKey k) v
      | _ =>
        throwJsError .typeError
          s!"Iterator value {formatValue e} is not an entry object") with
    | .ok () => fromEntriesInto ir obj
    | .error c => do
      iteratorClose ir (some c)
      throwCompletion c
  partial_fixpoint

/-- GroupBy (7.3.35) with `property` keys, for `Object.groupBy`: the
callback takes the value and the zero-based index, its answer goes
through ToPropertyKey, and each key's array is made on first sight — so
the answer's own key order is first-sight order. -/
def groupByInto (ir : IteratorRecord) (cb : Value) (groups : Ref) (k : Nat) :
    EvalM Unit := do
  match ← iteratorStep ir with
  | none => pure ()
  | some v =>
    match ← attempt (do
      let key ← toPropertyKey (← callFunction cb undefValue [v, Value.ofNat k])
      match ← getProp (.obj groups) key with
      | .prim .undef => do
        let arr ← newArray [v]
        createDataProperty groups key arr
      | arr => do
        let len ← toLengthValue (← getProp arr "length")
        pushElements arr len [v]) with
    | .ok () => groupByInto ir cb groups (k + 1)
    | .error c => do
      iteratorClose ir (some c)
      throwCompletion c
  partial_fixpoint

/-- Evaluate an argument list, left to right. -/
def evalExprs (env : Env) : List Expr → EvalM (List Value)
  | [] => pure []
  | e :: rest => do
    let v ← evalExpr env e
    let vs ← evalExprs env rest
    pure (v :: vs)
  partial_fixpoint

/-- PropertyDefinitionEvaluation over an object literal's members, into
an already-allocated object: left to right, and within a member the key
before the value, so a repeated key keeps the last value and a throwing
key leaves nothing after it defined.

Every member is a *definition* rather than a write: `Obj.define`
replaces an accessor of the name rather than calling its setter, which is
what makes `{ get a() {}, a: 1 }` a data property. A method, a getter,
and a setter are each a `.method` closure whose home object is the
literal, so `super.x` inside one reads through the literal's prototype;
a getter and a setter of one name merge into one accessor property. -/
def evalPropDefs (env : Env) : List PropDef → Ref → EvalM Unit
  | [], _ => pure ()
  | .init key value :: rest, r => do
    -- CreateDataPropertyOrThrow, which is a *definition*: an object
    -- literal's member is writable, enumerable, and configurable
    -- whatever the prototype chain says. The key is NamedEvaluation's
    -- name, so `{ m: function () {} }.m.name` is `"m"` and
    -- `{ [k]: () => {} }` takes the key's ToPropertyKey.
    let k ← evalPropKey env key
    let v ← evalNamed env k.functionName value
    modifyObj r (fun o => o.define k (Property.ordinary v))
    evalPropDefs env rest r
  | .method kind key params body :: rest, r => do
    -- MethodDefinitionEvaluation with `enumerable: true` (15.4.5 step 6),
    -- which is where a literal's member differs from a class's: a class
    -- method is not enumerable, a literal's is. The name is SetFunctionName
    -- with the `get`/`set` prefix.
    let k ← evalPropKey env key
    let fname := match kind with
      | .method => k.functionName
      | .getter => "get " ++ k.functionName
      | .setter => "set " ++ k.functionName
    let f ← makeFunction { params, body, env, kind := .method, homeObject := some r } fname
    modifyObj r (fun o =>
      match kind with
      | .method => o.define k (Property.ordinary f)
      | .getter => o.defineAccessorHalf k (some f) none true true
      | .setter => o.defineAccessorHalf k none (some f) true true)
    evalPropDefs env rest r
  -- CopyDataProperties (7.3.26) with no excluded keys: every own
  -- enumerable key of the source, string and symbol both, *defined* on
  -- the literal — so a setter of that name on the literal is replaced
  -- rather than called.
  | .spread value :: rest, r => do
    copyDataProperties r (← evalExpr env value) []
    evalPropDefs env rest r
  -- B.3.1: `__proto__: v` sets `[[Prototype]]` when `v` is an object or
  -- `null`, and does nothing at all otherwise — no property is made.
  | .proto value :: rest, r => do
    match ← evalExpr env value with
    | .obj p => modifyObj r (fun o => { o with proto := some p })
    | .prim .null => modifyObj r (fun o => { o with proto := none })
    | _ => pure ()
    evalPropDefs env rest r
  partial_fixpoint

/-- An object literal member's key. A written key is already a string; a
computed one is its expression's value run through ToPropertyKey, which
is also how a numeric key gets its spelling and how `{ [s]: 1 }` gets a
symbol one. -/
def evalPropKey (env : Env) : PropKey → EvalM Key
  | .name s => pure (.str s)
  | .computed e => do toPropertyKey (← evalExpr env e)
  partial_fixpoint

/-- EvaluateCall's reference half (13.3.6.2 through 13.3.5.1): the
callee's value and the `this` a call through it passes. A property callee
passes its base as the receiver and evaluates that base *once*, which is
what `o.f()` and `o[k]()` need; a `super` callee passes the current
receiver rather than the parent; anything else passes `undefined`,
because nothing here has a `with` or a global object.

A tagged template shares this: it is EvaluateCall with a template object
in front of the substitutions, so a member tag gets its object as
`this`.

Both callers read the pair with `.1` and `.2` rather than destructuring
it in the bind: a pattern-matching bind puts a `match` on a pair between
`evalCallee` and `callFunction`, and `simp` pays for it — spelled this
way `Test/Tarski/CallSimpTest.lean` runs in the time it took before this
definition existed, and spelled the other way it took three times as
long (#471). -/
def evalCallee (env : Env) : Expr → EvalM (Value × Value)
  | .member object name => do
    let base ← evalExpr env object
    let f ← getProp base name
    pure (f, base)
  | .index object key => do
    let base ← evalExpr env object
    let k ← evalExpr env key
    let f ← getProp base (← toPropertyKey k)
    pure (f, base)
  | .privateMember object name => do
    let base ← evalExpr env object
    let f ← readPrivate env base name
    pure (f, base)
  -- `super.m()` is a method call on the *current* receiver: the function
  -- comes off the parent, the `this` it is handed does not.
  | .superMember name => do
    let (parent, receiver) ← superBase env
    let f ← superRead parent receiver name
    pure (f, receiver)
  | .superIndex key => do
    let (parent, receiver) ← superBase env
    let k ← evalExpr env key
    let f ← superRead parent receiver (← toPropertyKey k)
    pure (f, receiver)
  | callee => do
    let f ← evalExpr env callee
    pure (f, undefValue)
  partial_fixpoint

/-- SubstitutionEvaluation and TemplateStrings woven together: the cooked
string is built one substitution at a time, ToString running after each
expression is evaluated, so a later expression's throw comes after an
earlier value's `toString` has already run. The two lists are walked
together and the strings are one longer; a mismatch is a document the
decoder already refused, and answers what was built so far. -/
def evalTemplate (env : Env) : List String → List Expr → JsString → EvalM Value
  | [s], [], acc => pure (.prim (.str (acc ++ JsString.ofString s)))
  | s :: strs, e :: es, acc => do
    let v ← evalExpr env e
    let t ← toStringValue v
    evalTemplate env strs es (acc ++ JsString.ofString s ++ t)
  | _, _, acc => pure (.prim (.str acc))
  partial_fixpoint

/-- NamedEvaluation (8.6.2) as one definition rather than a hint
threaded through `evalExpr`: an anonymous function expression, arrow, or
class expression takes the name of the binding it is being given to, and
every other expression is evaluated as usual. The four call sites are
the specification's — a declarator, an assignment to an identifier, an
object literal's member, and a class field. -/
def evalNamed (env : Env) (name : String) : Expr → EvalM Value
  | .funcExpr none params body => makeFunction { params, body, env, kind := .ordinary } name
  | .arrow params (.block b) => makeFunction { params, body := b, env, kind := .arrow } name
  | .arrow params (.expr e) =>
    makeFunction { params, body := [.returnStmt (some e)], env, kind := .arrow } name
  | .classExpr cls => evalClass env cls name
  | e => evalExpr env e
  partial_fixpoint

/-- Get a property, walking the prototype chain. There is no fuel bound:
a cyclic chain is a program that does not terminate, which is `none`, and
that is the same answer the epic gives every other divergence.

Two own properties do not live in a property list. A string answers its
own `length` and its own index properties — the String exotic object's
`[[GetOwnProperty]]` — and every other key on it is read through
`String.prototype`. An array answers its own `length` out of its kind,
which is where the live length lives.

A Number, a Boolean, a String, or a Symbol base reads through its wrapper
prototype **without allocating a wrapper**: a Number's, a Boolean's, or a
Symbol's wrapper would have no own properties, and a String's own
properties are the ones answered above, so the answer is the same, and
the receiver a method call then gets is still the primitive, which is why
`thisNumberValue`, `thisStringValue`, and `thisSymbolValue` accept both. A
bigint base still answers `undefined`, `BigInt.prototype` being outside
this epic.

This is inside the fixpoint block because a getter is user code called
from here. It is no longer the walk itself, though: `getFrom` is, and
this is the dispatch onto it, so this one may join a simp set while
`getFrom` is unfolded a step at a time like every other heap
recursion. -/
def getProp (base : Value) (key : Key) : EvalM Value :=
  match base with
  | .prim .undef =>
    throwJsError .typeError s!"Cannot read properties of undefined (reading '{key}')"
  | .prim .null =>
    throwJsError .typeError s!"Cannot read properties of null (reading '{key}')"
  | .prim (.str s) =>
    if key == Key.str "length" then pure (Value.ofNat s.length)
    else
      match key.arrayIndex?.bind s.unitAt? with
      | some u => pure (.prim (.str u))
      | none => getFrom stringProtoRef key base
  | .prim (.num _) => getFrom numberProtoRef key base
  | .prim (.bool _) => getFrom booleanProtoRef key base
  | .sym _ => getFrom symbolProtoRef key base
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

The own step is `Obj.ownProperty`, the one `[[GetOwnProperty]]`, so an
array's `length` and a String object's indices are answered here by the
same definition `findProperty` and `deleteProp` read.

The walk is `getFromUp`'s, not this one's: what recurses on the heap
rather than on syntax may never join a simp set, so the step is a
definition of its own and `getFrom` is free to be in one. -/
def getFrom (r : Ref) (key : Key) (receiver : Value) : EvalM Value := do
  let o ← readObj r
  match o.ownProperty key with
  | some { slot := .accessor a, .. } =>
    match a.getter with
    | some g => callFunction g receiver []
    | none => pure undefValue
  | some { slot := .data v _, .. } => pure v
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
def getFromUp (parent : Ref) (key : Key) (receiver : Value) : EvalM Value :=
  getFrom parent key receiver
  partial_fixpoint

/-- The first own property under a key, starting at `r` and walking up:
what OrdinarySet reads to decide whether a write is allowed, and what
`in` and `Object.assign` ask for too. An array's `length` is synthesized
here — a non-enumerable, non-configurable data property whose value is
the live length and whose `[[Writable]]` is the kind's — because it is an
own property that does not live in the property list.

The step up is `findPropertyUp`'s, for the reason `getFrom` gives. -/
def findProperty (r : Ref) (key : Key) : EvalM (Option Property) := do
  let o ← readObj r
  match o.ownProperty key with
  | some p => pure (some p)
  | none =>
    match o.proto with
    | some p => findPropertyUp p key
    | none => pure none
  partial_fixpoint

/-- `findProperty`'s prototype step, split out for the reason
`getFromUp` is. -/
def findPropertyUp (parent : Ref) (key : Key) : EvalM (Option Property) :=
  findProperty parent key
  partial_fixpoint

/-- HasProperty (7.3.11): whether the key is anywhere on the chain. -/
def hasProperty (r : Ref) (key : Key) : EvalM Bool := do
  pure (← findProperty r key).isSome

/-- Set a property, OrdinarySet and OrdinarySetWithOwnDescriptor
(10.1.9). Strict mode throughout, so every refusal is a `TypeError`
rather than a silent no-op: a primitive base, a non-writable data
property anywhere on the chain, an accessor with no setter, and a write
that would add a key to a non-extensible object.

An array's own `length` is the one key whose write is not a property
write: assigning to it truncates or grows through ArraySetLength, and
assigning to an index at or past the end grows the length to hold it —
unless `length` is non-writable, in which case the write is refused as a
read-only property is. Inside the fixpoint block because ArraySetLength's
coercion can reach user code, and because a setter anywhere on the chain
is user code too. -/
def setProp (base : Value) (key : Key) (v : Value) : EvalM Unit :=
  match base with
  | .obj r => do
    match ← findProperty r key with
    | some { slot := .accessor a, .. } =>
      match a.setter with
      | some s => do
        let _ ← callFunction s base [v]
        pure ()
      | none =>
        throwJsError .typeError
          s!"Cannot set property {key} of #<Object> which has only a getter"
    | some { slot := .data _ false, .. } =>
      throwJsError .typeError
        s!"Cannot assign to read only property '{key}' of object '#<Object>'"
    | _ => do
      let o ← readObj r
      match o.kind with
      | .array len lengthWritable =>
        if key == Key.str "length" then setArrayLength r o v
        else
          match key.arrayIndex? with
          | some i =>
            if len ≤ i && !lengthWritable then
              throwJsError .typeError
                "Cannot assign to read only property 'length' of object '#<Object>'"
            else if (o.getOwnProperty key).isNone && !o.extensible then
              throwJsError .typeError s!"Cannot add property {key}, object is not extensible"
            else
              writeObj r { o.setOwn key v with kind := .array (max len (i + 1)) lengthWritable }
          | none =>
            if (o.getOwnProperty key).isNone && !o.extensible then
              throwJsError .typeError s!"Cannot add property {key}, object is not extensible"
            else writeObj r (o.setOwn key v)
      -- A wrapper object takes an ordinary write like any other object: its
      -- `[[NumberData]]` is a field, not a property, so nothing can reach it.
      | _ =>
        if (o.getOwnProperty key).isNone && !o.extensible then
          throwJsError .typeError s!"Cannot add property {key}, object is not extensible"
        else writeObj r (o.setOwn key v)
  | .prim _ =>
    throwJsError .typeError
      s!"Cannot set properties of {formatValue base} (setting '{key}')"
  | .sym _ =>
    throwJsError .typeError
      s!"Cannot set properties of {formatValue base} (setting '{key}')"
  partial_fixpoint

/-- ArraySetLength (10.4.2.4) as a *write* to `xs.length`. The value is
coerced first — ToUint32 of ToNumber, and anything else is a
`RangeError` — because a poisoned `valueOf` must run before any other
check; then `length`'s own `[[Writable]]` is consulted; then the
elements are dropped from the top down, stopping at the first
non-configurable one, whose index fixes the length that is actually
written and whose refusal is then reported. -/
def setArrayLength (r : Ref) (o : Obj) (v : Value) : EvalM Unit := do
  match uint32Of? (← toNumberValue v) with
  | none => throwJsError .rangeError "Invalid array length"
  | some n =>
    match o.arrayLength? with
    | some (_, false) =>
      throwJsError .typeError
        "Cannot assign to read only property 'length' of object '#<Object>'"
    | _ =>
      let (o', reached) := o.truncate n
      writeObj r o'
      if reached == n then pure ()
      else
        throwJsError .typeError
          "Cannot assign to read only property 'length' of object '#<Object>'"
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
def joinElements (arr : Value) (i len : Nat) (sep : JsString) : EvalM JsString := do
  if i < len then
    let s ← match ← getProp arr (Nat.repr i) with
      | .prim .undef => pure (JsString.ofString "")
      | .prim .null => pure (JsString.ofString "")
      | v => toStringValue v
    let rest ← joinElements arr (i + 1) len sep
    pure (if i + 1 < len then s ++ sep ++ rest else s ++ rest)
  else pure (JsString.ofString "")
  partial_fixpoint

/-- ToPrimitive (7.1.1). A primitive — a `JsVal` or a symbol — is
itself; an object is asked for its `@@toPrimitive` handler first, and
falls back to OrdinaryToPrimitive: `valueOf` then `toString` under the
number and default hints, `toString` then `valueOf` under the string one.
The first callable method whose result is a primitive wins, and a
`TypeError` if neither gives one.

The answer is a `Value` rather than a `JsVal` because a symbol is a
primitive ToPrimitive returns unchanged — `toPropertyKey(Object(sym))`
must yield the symbol — and the consumers that have no symbol to give
(`toStringValue`, `toNumberValue`, the operators) each raise the refusal
of their own. It is never `.obj`. -/
def toPrimitive (hint : PrimHint) (v : Value) : EvalM Value :=
  match v with
  | .prim _ => pure v
  | .sym _ => pure v
  | .obj _ => do
    -- GetMethod(v, @@toPrimitive) (7.1.1 step 2.a–c): a callable handler
    -- is called with the hint's name and must answer a primitive.
    let handler ← getProp v WellKnownSymbol.toPrimitive.key
    if ← isCallable handler then
      match ← callFunction handler v [.prim (.str hint.name)] with
      | .obj _ => throwJsError .typeError "Cannot convert object to primitive value"
      | p => pure p
    else
      match ← primitiveFrom v (hintOrder hint).1 with
      | some p => pure p
      | none =>
        match ← primitiveFrom v (hintOrder hint).2 with
        | some p => pure p
        | none => throwJsError .typeError "Cannot convert object to primitive value"
  partial_fixpoint

/-- ToString on values: ToPrimitive with hint string, then ToString on
the primitive. `String(v)`, `join`, and the `Error` constructor's
`message` all spell it this way. A symbol has no ToString: 7.1.17 step 2
is a `TypeError`, which is why `String(sym)` is the `String`
constructor's own arm rather than this. -/
def toStringValue (v : Value) : EvalM JsString := do
  match ← toPrimitive .string v with
  | .prim p => pure (toStringPrim p)
  | .sym _ => throwJsError .typeError "Cannot convert a Symbol value to a string"
  | .obj _ => throwJsError .typeError "Cannot convert object to primitive value"
  partial_fixpoint

/-- One step of OrdinaryToPrimitive: call the named method on the object
if it has a callable one, and answer its result when that is a
primitive — a symbol among them. -/
def primitiveFrom (o : Value) (name : Key) : EvalM (Option Value) := do
  let m ← getProp o name
  if ← isCallable m then
    match ← callFunction m o [] with
    | .obj _ => pure none
    | p => pure (some p)
  else
    pure none
  partial_fixpoint

/-- ToPropertyKey (7.1.19): a symbol is a key as it stands, and
everything else is ToString of its ToPrimitive with the string hint. -/
def toPropertyKey (v : Value) : EvalM Key :=
  match v with
  | .sym s => pure (.sym s)
  | .prim p => pure (.str (toStringPrim p).toKey)
  | .obj _ => do
    match ← toPrimitive .string v with
    | .sym s => pure (.sym s)
    | .prim p => pure (.str (toStringPrim p).toKey)
    | .obj _ => throwJsError .typeError "Cannot convert object to primitive value"
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
  | p :: ps, args =>
    if p.rest then do
      -- A rest parameter takes everything left as a fresh array and ends
      -- the walk; the grammar puts it last and never defaults it.
      let arr ← newArray args
      bindPattern env .init p.target arr
    else do
      let (a, rest) := match args with
        | [] => (undefValue, ([] : List Value))
        | a :: as => (a, as)
      -- NamedEvaluation: `function f(g = function () {}) {}` names the
      -- default `g`, as a declarator's initializer is named. A pattern
      -- parameter's default names nothing.
      let v ← match p.default, a with
        | some d, .prim .undef =>
          match p.target with
          | .target (.ident n) => evalNamed env n d
          | _ => evalExpr env d
        | _, _ => pure a
      bindPattern env .init p.target v
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
  | .sym _ => throwJsError .typeError "not a function"
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
      -- `[[ErrorData]]` is what `Object.prototype.toString` reads.
      let fresh ← allocFromConstructor f k.protoRef
      modifyObj fresh (fun o => { o with kind := .error })
      callNative (.errorCtor k) (.obj fresh) args
    | some (.native .aggregateErrorCtor) => do
      -- `AggregateError(errors)` is `new AggregateError(errors)`, for the
      -- reason the seven above are, and written out for the same one.
      let fresh ← allocFromConstructor f aggregateErrorProtoRef
      modifyObj fresh (fun o => { o with kind := .error })
      callNative .aggregateErrorCtor (.obj fresh) args
    | some (.native n) => callNative n thisArg args
    | some (.bound b) => callBound b args
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

/-- `[[Call]]` of a bound function exotic object (10.4.1.1): the target,
with the bound `this` and the bound arguments in front of the call's own.

It is a definition of its own for the reason `getFromUp` is one. The
target is a *heap link*, so `simp` would unfold this under a `target` it
has not resolved and never stop; splitting the step out leaves
`callFunction`'s own equation free of that recursion, so it may still
join a simp set, and a bound call costs one `rw [callBound]` per link. -/
def callBound (b : BoundFunction) (args : List Value) : EvalM Value :=
  callFunction (.obj b.target) b.boundThis (b.boundArgs ++ args)
  partial_fixpoint

/-- ToNumber on values: ToPrimitive with the number hint, then ToNumber
on the primitive. The twin of `toStringValue`, and what every coercing
built-in argument goes through. A symbol is 7.1.4 step 1's
`TypeError`. -/
def toNumberValue (v : Value) : EvalM Float := do
  match ← toPrimitive .number v with
  | .prim p => pure (toNumberPrim p)
  | .sym _ => throwJsError .typeError "Cannot convert a Symbol value to a number"
  | .obj _ => throwJsError .typeError "Cannot convert object to primitive value"
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

/-- A whole argument list coerced to Strings, left to right:
`toNumberValues`'s twin, and what `console.log` joins with a space. The
recursion is explicit for the reason its twin's is — a `mapM` inside the
fixpoint block would need its own monotonicity lemma. -/
def toStringValues : List Value → EvalM (List JsString)
  | [] => pure []
  | v :: rest => do
    let x ← toStringValue v
    let xs ← toStringValues rest
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
  -- 20.4.1: `Symbol` has a `[[Construct]]`, and all it does is refuse.
  | .symbolCtor => throwJsError .typeError "Symbol is not a constructor"
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
  | .stringCtor => do
    -- StringCreate (10.4.3.4): `length` is a real own property, defined
    -- once, so it lands ahead of anything a subclass constructor adds.
    let s ← match args with
      | [] => pure (JsString.ofString "")
      | v :: _ => toStringValue v
    let r ← allocFromConstructor newTarget stringProtoRef
    modifyObj r (fun o =>
      { o with
        kind := .string s,
        properties := ("length", Property.constant (Value.ofNat s.length)) :: o.properties })
    pure (.obj r)
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
      | _ => pure arr
    | v => pure v
  | _ => callNative n undefValue args
  partial_fixpoint

/-- ToLength (7.1.20) on a value, the length `apply` reads off an
array-like. Either infinity answers 0: `+∞` would ask for a list of
2^53 - 1 values, which no heap here can hold, so the choice is between a
wrong answer and a run that never ends, and a wrong answer can at least
be seen.
-/
def toLengthValue (v : Value) : EvalM Nat := do
  match ← toIntegerOrInfinityValue v with
  | none => pure 0
  | some i => pure (if i ≤ 0 then 0 else i.toNat)
  partial_fixpoint

/-- CreateListFromArrayLike (7.3.18): the index properties `0 … len - 1`,
read through `getProp` so that a getter runs. `joinElements`'s twin, and
`rw`'s for the same reason — it recurses on a length the heap named. -/
def listFromArrayLike (arr : Value) (i len : Nat) : EvalM (List Value) := do
  if i < len then do
    let v ← getProp arr (Nat.repr i)
    let rest ← listFromArrayLike arr (i + 1) len
    pure (v :: rest)
  else pure []
  partial_fixpoint

/-- One field of a descriptor object: `HasProperty` then `Get`, which is
the pair 6.2.6.5 performs for each of the six. `none` is the field being
absent, which is not the same as its being `undefined`. -/
def descriptorField (r : Ref) (key : Key) : EvalM (Option Value) := do
  if ← hasProperty r key then pure (some (← getProp (.obj r) key)) else pure none
  partial_fixpoint

/-- ToPropertyDescriptor (6.2.6.5). The six fields are read in the
specification's order, and `get` is checked before `set` is read, so a
poisoned descriptor object's methods run in the order an engine runs
them. Both kinds of field at once is the last refusal. -/
def toDescriptor (v : Value) : EvalM Descriptor := do
  match v with
  | .obj r => do
    let enumerable ← descriptorField r "enumerable"
    let configurable ← descriptorField r "configurable"
    let value ← descriptorField r "value"
    let writable ← descriptorField r "writable"
    let getter ← descriptorField r "get"
    match getter with
    | some g =>
      if !(← isCallable g) && g != undefValue then
        throwJsError .typeError s!"Getter must be a function: {formatValue g}"
    | none => pure ()
    let setter ← descriptorField r "set"
    match setter with
    | some t =>
      if !(← isCallable t) && t != undefValue then
        throwJsError .typeError s!"Setter must be a function: {formatValue t}"
    | none => pure ()
    let d : Descriptor :=
      { value, getter, setter,
        writable := writable.map toBooleanPrim,
        enumerable := enumerable.map toBooleanPrim,
        configurable := configurable.map toBooleanPrim }
    if d.isAccessor && d.isData then
      throwJsError .typeError
        ("Invalid property descriptor. Cannot both specify accessors and a value or " ++
          "writable attribute")
    else pure d
  | _ =>
    throwJsError .typeError s!"Property description must be an object: {formatValue v}"
  partial_fixpoint

/-- The refusal a rejected `[[DefineOwnProperty]]` reports: the
not-extensible message when the key is new and the object is closed, and
the redefinition message otherwise. -/
def refuseDefine (o : Obj) (key : Key) : EvalM Unit :=
  if (o.ownProperty key).isNone && !o.extensible then
    throwJsError .typeError s!"Cannot define property {key}, object is not extensible"
  else throwJsError .typeError s!"Cannot redefine property: {key}"

/-- ArraySetLength (10.4.2.4) as a *definition* of `length`. A descriptor
with no `[[Value]]` only changes attributes, and the one attribute an
array's `length` has is its writability; a descriptor with one coerces
first (a `RangeError` for anything that is not a uint32), then consults
that writability, then truncates from the top down, and reports the first
non-configurable element as a refusal after writing the length the scan
reached. -/
def defineArrayLength (r : Ref) (o : Obj) (len : Nat) (lengthWritable : Bool)
    (d : Descriptor) : EvalM Unit := do
  if d.isAccessor || d.enumerable == some true || d.configurable == some true then
    throwJsError .typeError "Cannot redefine property: length"
  else
    match d.value with
    | none =>
      if d.writable == some true && !lengthWritable then
        throwJsError .typeError "Cannot redefine property: length"
      else
        match d.writable with
        | some w => writeObj r { o with kind := .array len (lengthWritable && w) }
        | none => pure ()
    | some v => do
      let n ← match uint32Of? (← toNumberValue v) with
        | none => throwJsError .rangeError "Invalid array length"
        | some n => pure n
      -- A non-writable `length` refuses a different value and refuses
      -- `writable: true` (10.1.6.3 step 5.e), whatever the value.
      if !lengthWritable && d.writable == some true then
        throwJsError .typeError "Cannot redefine property: length"
      else if len ≤ n then
        if !lengthWritable && n != len then
          throwJsError .typeError "Cannot redefine property: length"
        else
          writeObj r { o with kind := .array n (lengthWritable && d.writable.getD true) }
      else if !lengthWritable then
        throwJsError .typeError "Cannot redefine property: length"
      else do
        let (o', reached) := o.truncate n
        writeObj r { o' with kind := .array reached (lengthWritable && d.writable.getD true) }
        if reached == n then pure ()
        else throwJsError .typeError "Cannot redefine property: length"
  partial_fixpoint

/-- DefinePropertyOrThrow (7.3.8) over `Obj.applyDescriptor`, with the
Array exotic object's `[[DefineOwnProperty]]` (10.4.2.1) in front of it:
`length` is ArraySetLength's, an index at or past a non-writable length
is refused, and an index that lands past the end grows the length. -/
def definePropertyOrThrow (r : Ref) (key : Key) (d : Descriptor) : EvalM Unit := do
  let o ← readObj r
  match o.arrayLength? with
  | some (len, lengthWritable) =>
    if key == Key.str "length" then defineArrayLength r o len lengthWritable d
    else
      match key.arrayIndex? with
      | some i =>
        if len ≤ i && !lengthWritable then
          throwJsError .typeError s!"Cannot redefine property: {key}"
        else
          match o.applyDescriptor key d with
          | none => refuseDefine o key
          | some o' =>
            writeObj r
              (if len ≤ i then { o' with kind := .array (i + 1) lengthWritable } else o')
      | none =>
        match o.applyDescriptor key d with
        | none => refuseDefine o key
        | some o' => writeObj r o'
  | none =>
    match o.applyDescriptor key d with
    | none => refuseDefine o key
    | some o' => writeObj r o'
  partial_fixpoint

/-- ObjectDefineProperties (20.1.2.3.1) step 5: **every** descriptor is
read before any is applied, so a descriptor object whose later getter
throws leaves nothing defined. -/
def readDescriptors (props : Ref) : List Key → EvalM (List (Key × Descriptor))
  | [] => pure []
  | k :: rest => do
    match (← readObj props).ownProperty k with
    | some p =>
      if p.enumerable then do
        let d ← toDescriptor (← getProp (.obj props) k)
        pure ((k, d) :: (← readDescriptors props rest))
      else readDescriptors props rest
    | none => readDescriptors props rest
  partial_fixpoint

/-- ObjectDefineProperties step 6: the definitions, in the order they
were read. -/
def applyDescriptors (r : Ref) : List (Key × Descriptor) → EvalM Unit
  | [] => pure ()
  | (k, d) :: rest => do
    definePropertyOrThrow r k d
    applyDescriptors r rest
  partial_fixpoint

/-- ObjectDefineProperties, what both `Object.defineProperties` and
`Object.create`'s second argument run. -/
def defineProperties (target : Value) (propsVal : Value) : EvalM Value := do
  match target with
  | .obj r => do
    let props ← toObjectValue propsVal
    let ds ← readDescriptors props (← readObj props).ownKeys
    applyDescriptors r ds
    pure target
  | _ => throwJsError .typeError "Object.defineProperties called on non-object"
  partial_fixpoint

/-- EnumerableOwnProperties (7.3.23) for `Object.values` and
`Object.entries`: every own key is re-read before its value is taken,
because a getter already run may have deleted a later key or made it
non-enumerable. -/
def enumerableOwn (r : Ref) (wantKey : Bool) : List String → EvalM (List Value)
  | [] => pure []
  | k :: rest => do
    match (← readObj r).ownProperty k with
    | some p =>
      if p.enumerable then do
        let v ← getProp (.obj r) k
        let entry ← if wantKey then newArray [.prim (.str k), v] else pure v
        pure (entry :: (← enumerableOwn r wantKey rest))
      else enumerableOwn r wantKey rest
    | none => enumerableOwn r wantKey rest
  partial_fixpoint

/-- `Object.assign`'s inner loop: each enumerable own key of one source
read with `Get` and written with `Set`, so a getter on the source and a
setter on the target both run. -/
def assignKeys (target : Value) (source : Ref) : List Key → EvalM Unit
  | [] => pure ()
  | k :: rest => do
    match (← readObj source).ownProperty k with
    | some p =>
      if p.enumerable then do
        let v ← getProp (.obj source) k
        setProp target k v
      else pure ()
    | none => pure ()
    assignKeys target source rest
  partial_fixpoint

/-- `Object.assign`'s outer loop; a nullish source is skipped. -/
def assignSources (target : Value) : List Value → EvalM Unit
  | [] => pure ()
  | v :: rest => do
    match v with
    | .prim .undef => pure ()
    | .prim .null => pure ()
    | _ => do
      let source ← toObjectValue v
      assignKeys target source (← readObj source).ownKeys
    assignSources target rest
  partial_fixpoint

/-- `Object.getOwnPropertyDescriptors`' loop: one descriptor object per
own key, each an ordinary data property of the answer. -/
def descriptorsInto (source target : Ref) : List Key → EvalM Unit
  | [] => pure ()
  | k :: rest => do
    match (← readObj source).ownProperty k with
    | some p => do
      let d ← fromProperty p
      modifyObj target (fun o => o.define k (Property.ordinary d))
    | none => pure ()
    descriptorsInto source target rest
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

The rest are #380's floor. `String(v)` is ToString and nothing else;
`new String(v)` is `constructNative`'s, and the two differ only there, as
`Number`'s two spellings do. `Object(v)` is an ordinary object for a
nullish argument and ToObject otherwise — the argument itself for an
object, and the wrapper for a Number, a Boolean, or a String.
`Object.keys` is ToObject and then OrdinaryOwnPropertyKeys, so a string's
answer is its index keys and a Number's is empty. `push` and `join` require an Array exotic receiver: the
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
    | .prim .undef :: _ => do
      installErrorCause thisArg (args[1]?.getD undefValue)
      pure thisArg
    | m :: _ => do
      -- CreateNonEnumerableDataPropertyOrThrow (20.5.1.1 step 4): a
      -- *definition*, and a non-enumerable one, so `Object.keys(e)` is
      -- empty and no prototype setter can intercept it.
      let msg ← toStringValue m
      match thisArg with
      | .obj r => modifyObj r (fun o => o.define "message" (Property.method (.prim (.str msg))))
      | _ => pure ()
      installErrorCause thisArg (args[1]?.getD undefValue)
      pure thisArg
  | .errorToString =>
    match thisArg with
    | .obj _ => do
      let name ← match ← getProp thisArg "name" with
        | .prim .undef => pure (JsString.ofString "Error")
        | v => toStringValue v
      let msg ← match ← getProp thisArg "message" with
        | .prim .undef => pure (JsString.ofString "")
        | v => toStringValue v
      if name.isEmpty then pure (.prim (.str msg))
      else if msg.isEmpty then pure (.prim (.str name))
      else pure (.prim (.str (name ++ JsString.ofString ": " ++ msg)))
    | _ => throwJsError .typeError "Error.prototype.toString called on non-object"
  | .stringCtor =>
    -- 22.1.1.1 step 1.a: `String(sym)` is SymbolDescriptiveString, the
    -- one route from a symbol to a string that is not a `TypeError`.
    match args with
    | [] => pure (.prim (.str ""))
    | .sym sy :: _ => pure (.prim (.str sy.descriptiveString))
    | v :: _ => do pure (.prim (.str (← toStringValue v)))
  | .objectCtor =>
    match args with
    | [] => do pure (.obj (← newObject))
    | .prim .undef :: _ => do pure (.obj (← newObject))
    | .prim .null :: _ => do pure (.obj (← newObject))
    -- Everything else is ToObject: an object is itself, and a Number, a
    -- Boolean, or a String is its wrapper.
    | v :: _ => do pure (.obj (← toObjectValue v))
  | .objectIs =>
    pure (.prim (.bool (sameValueValue (args[0]?.getD undefValue) (args[1]?.getD undefValue))))
  | .objectKeys => do
    -- ToObject like every other arm: a string's wrapper has its indices
    -- as enumerable own properties, so `Object.keys("ab")` is `["0","1"]`.
    let r ← toObjectValue (args[0]?.getD undefValue)
    newArray ((← readObj r).enumerableKeys.map (fun k => .prim (.str (JsString.ofString k))))
  | .objectHasOwnProperty =>
    match thisArg with
    -- ToObject of a Number or a Boolean has no own properties, so the
    -- answer is `false` — but the key is converted first, as the spec
    -- orders it, so a `toString` on it still runs.
    | .prim (.num _) | .prim (.bool _) => do
      let _ ← toPropertyKey (args[0]?.getD undefValue)
      pure (.prim (.bool false))
    -- A string's wrapper *does* have own properties, and they are a
    -- function of the string alone, so the answer costs no allocation
    -- either.
    | .prim (.str s) => do
      let key ← toPropertyKey (args[0]?.getD undefValue)
      pure (.prim (.bool ((Obj.stringWrapper none s).hasOwn key)))
    | .obj r => do
      let key ← toPropertyKey (args[0]?.getD undefValue)
      pure (.prim (.bool ((← readObj r).hasOwn key)))
    | .sym _ => do
      let _ ← toPropertyKey (args[0]?.getD undefValue)
      pure (.prim (.bool false))
    | .prim _ => throwJsError .typeError "Cannot convert a primitive to an object"
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
    | _ => pure (.prim (.bool false))
  | .arrayPush =>
    match thisArg with
    | .obj r => do
      match (← readObj r).kind with
      | .array len _ => do
        pushElements thisArg len args
        pure (Value.ofNat (len + args.length))
      | _ => throwJsError .typeError "Array.prototype.push called on non-array"
    | _ => throwJsError .typeError "Array.prototype.push called on non-array"
  | .arrayJoin =>
    match thisArg with
    | .obj r => do
      match (← readObj r).kind with
      | .array len _ => do
        let sep ← match args with
          | [] => pure (JsString.ofString ",")
          | .prim .undef :: _ => pure (JsString.ofString ",")
          | v :: _ => toStringValue v
        pure (.prim (.str (← joinElements thisArg 0 len sep)))
      | _ => throwJsError .typeError "Array.prototype.join called on non-array"
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
    pure (.prim (.num (Number.parseFloat s.toStringLossy)))
  | .parseInt => do
    let s ← toStringValue (args.headD undefValue)
    let r ← toNumberValue (args[1]?.getD undefValue)
    pure (.prim (.num (Number.parseInt s.toStringLossy (Number.FloatOps.tsToInt32 r))))
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
  -- The `Object` and `Function` surface is a definition of its own. It is
  -- not a matter of taste: `NativeFn` has sixty constructors now, and a
  -- `match` over all of them with a body this size is one whose equation
  -- lemmas the compiler cannot generate — `rw [callNative]` and
  -- `attribute [simp] callNative` both diverge on it. Splitting the group
  -- out leaves each match small enough to unfold, which is what
  -- `Test/Tarski/MathSimpTest.lean` and its neighbours need.
  | .objectProtoToString | .objectProtoValueOf | .objectProtoToLocaleString
  | .objectProtoIsPrototypeOf | .objectProtoPropertyIsEnumerable
  | .objectAssign | .objectCreate | .objectDefineProperties | .objectDefineProperty
  | .objectEntries | .objectFreeze | .objectGetOwnPropertyDescriptor
  | .objectGetOwnPropertyDescriptors | .objectGetOwnPropertyNames
  | .objectGetPrototypeOf | .objectHasOwn | .objectIsExtensible | .objectIsFrozen
  | .objectIsSealed | .objectPreventExtensions | .objectSeal | .objectSetPrototypeOf
  | .objectValues
  | .functionProto | .functionCtor | .functionCall | .functionApply | .functionBind
  | .functionToString => callReflectNative f thisArg args
  -- The `Symbol` surface and `JSON` are two more groups of their own,
  -- for the same reason and with `callReflectNative`'s standing: neither
  -- is in `tarski_eval`.
  | .symbolCtor | .symbolFor | .symbolKeyFor | .symbolProtoToString
  | .symbolProtoValueOf | .symbolDescription | .symbolToPrimitive
  | .aggregateErrorCtor | .functionHasInstance | .objectGetOwnPropertySymbols
  | .errorIsError => callSymbolNative f thisArg args
  | .jsonParse | .jsonStringify => callJsonNative f thisArg args
  | .string g => callStringNative g thisArg args
  -- The iterator surface is a fourth group, split out for
  -- `callReflectNative`'s reason but — unlike the other three —
  -- **registered** in `tarski_eval`: seven arms are nowhere near the
  -- ceiling, and a closed destructuring or one `for`-`of` step has to
  -- reduce without a local lemma list.
  | .iteratorProtoIterator | .arrayIteratorNext | .arrayKeys | .arrayValues
  | .arrayEntries | .objectFromEntries | .objectGroupBy
  | .stringProtoIterator | .stringIteratorNext =>
    callIteratorNative f thisArg args
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
  | .consoleLog => do
    -- `lakatos exe`'s output binding, and `print`'s twin: it writes to
    -- the same log, so a program that mixes the two gets one sequence in
    -- program order. Every argument goes through ToString and the parts
    -- are joined by one space; no argument at all is one empty line,
    -- which is what `console.log()` prints under Node.
    let parts ← toStringValues args
    let _ ← callNative .arrayPush (.obj printLogRef)
      [.prim (.str (JsString.intercalate (JsString.ofString " ") parts))]
    pure undefValue
  partial_fixpoint

/-- The `Object` reflection surface and `Function.prototype`'s four
methods: the half of the property protocol a script reaches by name.

It is a definition of its own rather than twenty-nine more arms of
`callNative` because `NativeFn` has sixty constructors, and a `match`
over all of them whose body is this large is one whose equation lemmas
the compiler cannot generate at all — `rw [callNative]` diverges, and so
does putting it in a simp set, which the reduction tests do.

The `Object` arms are ToObject, ToPropertyDescriptor,
FromPropertyDescriptor, SetIntegrityLevel, and the enumeration helpers
over those, each in the specification's own step order: a key is
converted before the receiver, every descriptor is read before any is
applied, and an own property is re-read before its value is taken. The
`Function` arms are 20.2.3's: `call` and `apply` differ only in how the
argument list is built, `bind` builds a `Callable.bound` whose `length`
and `name` are computed once, and `toString` answers the NativeFunction
form for every function, the bridge keeping no source text.

The arm for anything else is unreachable: `callNative` routes exactly
the twenty-nine constructors below here. -/
def callReflectNative (f : NativeFn) (thisArg : Value) (args : List Value) : EvalM Value :=
  match f with
  | .objectProtoToString =>
    -- 20.1.3.6. The two nullish tags come first, then ToObject, the
    -- builtin tag — which reads `[[StringData]]` as `String` — and
    -- finally `Get(O, @@toStringTag)`: a string there replaces the tag,
    -- which is what makes `[object Math]`, `[object JSON]`,
    -- `[object Symbol]`, and a user's own tag.
    match thisArg with
    | .prim .undef => pure (.prim (.str "[object Undefined]"))
    | .prim .null => pure (.prim (.str "[object Null]"))
    | v => do
      let r ← toObjectValue v
      let builtin := builtinTag (← readObj r)
      match ← getProp (.obj r) WellKnownSymbol.toStringTag.key with
      | .prim (.str tag) => pure (.prim (.str ("[object " ++ tag ++ "]")))
      | _ => pure (.prim (.str ("[object " ++ builtin ++ "]")))
  | .objectProtoValueOf => do pure (.obj (← toObjectValue thisArg))
  | .objectProtoToLocaleString => do
    -- 20.1.3.5 is Invoke(this, "toString"), not a call of the intrinsic:
    -- a `toString` of one's own is what runs.
    let f ← getProp thisArg "toString"
    callFunction f thisArg []
  | .objectProtoIsPrototypeOf =>
    match args[0]?.getD undefValue with
    | .obj v => do
      let r ← toObjectValue thisArg
      pure (.prim (.bool (← protoChainHas v r)))
    | _ => pure (.prim (.bool false))
  | .objectProtoPropertyIsEnumerable => do
    -- ToPropertyKey first, then ToObject, as 20.1.3.4 orders them.
    let key ← toPropertyKey (args[0]?.getD undefValue)
    let r ← toObjectValue thisArg
    match (← readObj r).ownProperty key with
    | some p => pure (.prim (.bool p.enumerable))
    | none => pure (.prim (.bool false))
  | .objectAssign => do
    let target ← toObjectValue (args[0]?.getD undefValue)
    assignSources (.obj target) (args.drop 1)
    pure (.obj target)
  | .objectCreate => do
    let proto ← match args[0]?.getD undefValue with
      | .obj p => pure (some p)
      | .prim .null => pure none
      | v =>
        throwJsError .typeError
          s!"Object prototype may only be an Object or null: {formatValue v}"
    let r ← allocObj { proto }
    match args[1]?.getD undefValue with
    | .prim .undef => pure (.obj r)
    | props => defineProperties (.obj r) props
  | .objectDefineProperties => do
    match args[0]?.getD undefValue with
    | .obj r => defineProperties (.obj r) (args[1]?.getD undefValue)
    | _ => throwJsError .typeError "Object.defineProperties called on non-object"
  | .objectDefineProperty => do
    match args[0]?.getD undefValue with
    | .obj r => do
      let key ← toPropertyKey (args[1]?.getD undefValue)
      let d ← toDescriptor (args[2]?.getD undefValue)
      definePropertyOrThrow r key d
      pure (.obj r)
    | _ => throwJsError .typeError "Object.defineProperty called on non-object"
  | .objectEntries => do
    let r ← toObjectValue (args[0]?.getD undefValue)
    newArray (← enumerableOwn r true (← readObj r).stringKeys)
  | .objectValues => do
    let r ← toObjectValue (args[0]?.getD undefValue)
    newArray (← enumerableOwn r false (← readObj r).stringKeys)
  | .objectFreeze =>
    -- 20.1.2.6: a primitive answers itself, having no properties to
    -- close.
    match args[0]?.getD undefValue with
    | .obj r => do
      modifyObj r (fun o => o.setIntegrity true)
      pure (.obj r)
    | v => pure v
  | .objectSeal =>
    match args[0]?.getD undefValue with
    | .obj r => do
      modifyObj r (fun o => o.setIntegrity false)
      pure (.obj r)
    | v => pure v
  | .objectPreventExtensions =>
    match args[0]?.getD undefValue with
    | .obj r => do
      modifyObj r (fun o => { o with extensible := false })
      pure (.obj r)
    | v => pure v
  | .objectIsFrozen =>
    -- A primitive is frozen, sealed, and not extensible: it has no
    -- properties to be otherwise about.
    match args[0]?.getD undefValue with
    | .obj r => do pure (.prim (.bool ((← readObj r).testIntegrity true)))
    | _ => pure (.prim (.bool true))
  | .objectIsSealed =>
    match args[0]?.getD undefValue with
    | .obj r => do pure (.prim (.bool ((← readObj r).testIntegrity false)))
    | _ => pure (.prim (.bool true))
  | .objectIsExtensible =>
    match args[0]?.getD undefValue with
    | .obj r => do pure (.prim (.bool (← readObj r).extensible))
    | _ => pure (.prim (.bool false))
  | .objectGetOwnPropertyDescriptor => do
    let r ← toObjectValue (args[0]?.getD undefValue)
    let key ← toPropertyKey (args[1]?.getD undefValue)
    match (← readObj r).ownProperty key with
    | some p => fromProperty p
    | none => pure undefValue
  | .objectGetOwnPropertyDescriptors => do
    let r ← toObjectValue (args[0]?.getD undefValue)
    let target ← newObject
    descriptorsInto r target (← readObj r).ownKeys
    pure (.obj target)
  | .objectGetOwnPropertyNames => do
    let r ← toObjectValue (args[0]?.getD undefValue)
    newArray ((← readObj r).stringKeys.map (fun k => .prim (.str (JsString.ofString k))))
  | .objectGetPrototypeOf =>
    -- A Number or a Boolean answers its wrapper prototype without
    -- allocating a wrapper, as `getProp` does for the same reason.
    match args[0]?.getD undefValue with
    | .prim (.num _) => pure (.obj numberProtoRef)
    | .prim (.bool _) => pure (.obj booleanProtoRef)
    | .prim (.str _) => pure (.obj stringProtoRef)
    | v => do
      let r ← toObjectValue v
      match (← readObj r).proto with
      | some p => pure (.obj p)
      | none => pure (.prim .null)
  | .objectHasOwn => do
    let r ← toObjectValue (args[0]?.getD undefValue)
    let key ← toPropertyKey (args[1]?.getD undefValue)
    pure (.prim (.bool ((← readObj r).hasOwn key)))
  | .objectSetPrototypeOf => do
    let target := args[0]?.getD undefValue
    match target with
    | .prim .undef => throwJsError .typeError "Object.setPrototypeOf called on null or undefined"
    | .prim .null => throwJsError .typeError "Object.setPrototypeOf called on null or undefined"
    | _ => pure ()
    let proto ← match args[1]?.getD undefValue with
      | .obj p => pure (some p)
      | .prim .null => pure none
      | v =>
        throwJsError .typeError
          s!"Object prototype may only be an Object or null: {formatValue v}"
    match target with
    | .obj r => do
      let o ← readObj r
      if o.proto == proto then pure target
      -- `Object.prototype` is an immutable prototype exotic object
      -- (10.4.7): SetImmutablePrototype answers `false` for anything but
      -- the prototype it already has, whatever `[[Extensible]]` says.
      else if r == objectProtoRef then
        throwJsError .typeError "Immutable prototype object '#<Object>' cannot have their prototype set"
      else if !o.extensible then throwJsError .typeError "#<Object> is not extensible"
      else
        match proto with
        | none => do
          writeObj r { o with proto := none }
          pure target
        | some p =>
          if p == r then throwJsError .typeError "Cyclic __proto__ value"
          else if ← protoChainHas p r then throwJsError .typeError "Cyclic __proto__ value"
          else do
            writeObj r { o with proto := some p }
            pure target
    -- A primitive `O` answers itself once the prototype has been
    -- checked: there is nothing to write.
    | _ => pure target
  | .functionProto =>
    -- 20.2.3: `%Function.prototype%` accepts anything and answers
    -- `undefined`.
    pure undefValue
  | .functionCtor =>
    throwJsError .typeError "Function constructor is out of scope"
  | .functionCall =>
    -- 20.2.3.3. The IsCallable check is `callFunction`'s own `not a
    -- function`, which is the same refusal by another spelling.
    callFunction thisArg (args.headD undefValue) (args.drop 1)
  | .functionApply => do
    if !(← isCallable thisArg) then
      throwJsError .typeError
        s!"Function.prototype.apply was called on {formatValue thisArg}, which is not a function"
    else
      let argList ← match args[1]?.getD undefValue with
        | .prim .undef => pure []
        | .prim .null => pure []
        | .obj r => do
          let len ← toLengthValue (← getProp (.obj r) "length")
          listFromArrayLike (.obj r) 0 len
        | _ => throwJsError .typeError "CreateListFromArrayLike called on non-object"
      callFunction thisArg (args.headD undefValue) argList
  | .functionBind => do
    match thisArg with
    | .obj t =>
      if !(← isCallable thisArg) then
        throwJsError .typeError "Bind must be called on a function"
      else do
        let target ← readObj t
        -- 20.2.3.2 steps 4–7: when the target has an own `length`, it is
        -- read with Get — so an accessor runs — and, when it is a Number,
        -- `+∞` stays `+∞`, `-∞` is 0, and anything else is
        -- ToIntegerOrInfinity less the bound arguments and never below
        -- zero. `Nat` subtraction is the clamp.
        let boundArgs := args.drop 1
        let length ←
          if target.hasOwn "length" then
            match ← getProp thisArg "length" with
            | .prim (.num x) =>
              match Number.FloatOps.integerOrInfinity? x with
              | some i => pure (Value.ofNat ((if i ≤ 0 then 0 else i.toNat) - boundArgs.length))
              | none =>
                -- `integerOrInfinity?` is `none` for either infinity.
                pure (if x < 0.0 then Value.ofNat 0 else .prim (.num Number.POSITIVE_INFINITY))
            | _ => pure (Value.ofNat 0)
          else pure (Value.ofNat 0)
        let constructs ← isConstructor thisArg
        -- Step 12 is `Get(Target, "name")`, not a read of the property
        -- list: a `name` getter runs, and its throw is `bind`'s. Step 14
        -- gives anything that is not a String the empty string.
        let name ← match ← getProp thisArg "name" with
          | .prim (.str n) => pure n.toStringLossy
          | _ => pure ""
        let f ← allocObj
          { proto := target.proto,
            callable :=
              some (.bound { target := t, boundThis := args.headD undefValue,
                             boundArgs, constructs }),
            properties :=
              [ (Key.str "length", Property.attribute length),
                (Key.str "name", Property.attribute (.prim (.str ("bound " ++ name)))) ] }
        pure (.obj f)
    | _ => throwJsError .typeError "Bind must be called on a function"
  | .functionToString => do
    -- 20.2.3.5 allows the NativeFunction form for any function whose
    -- `[[SourceText]]` is unavailable, and the bridge keeps none: the
    -- evaluator is handed an AST, not a script.
    if ← isCallable thisArg then
      pure (.prim (.str (functionSourceText (← nameOf thisArg))))
    else
      throwJsError .typeError
        "Function.prototype.toString requires that 'this' be a Function"
  | _ => pure undefValue
  partial_fixpoint

/-- InstallErrorCause (20.5.8.1): when `options` is an object with a
`cause`, the error gets a non-enumerable `cause` of its own, defined
after `message`. Every other `options` — a primitive, or an object with
no such key — leaves the error without one, which is what makes
`"cause" in new Error("m")` false. -/
def installErrorCause (target : Value) (options : Value) : EvalM Unit := do
  match options, target with
  | .obj o, .obj r =>
    if ← hasProperty o "cause" then do
      let cause ← getProp options "cause"
      modifyObj r (fun ob => ob.define "cause" (Property.method cause))
    else pure ()
  | _, _ => pure ()
  partial_fixpoint

/-- The `Symbol` surface, `AggregateError`, `Error.isError`,
`Object.getOwnPropertySymbols`, and `%Function.prototype[@@hasInstance]%`.

It is a definition of its own, and **not** in `tarski_eval`, for
`callReflectNative`'s reason: `callNative`'s arms are already past the
depth at which Lean generates a match's equation lemmas, and no proof
today reads a symbol. `callNative` routes exactly the constructors below
here, so the last arm is unreachable. -/
def callSymbolNative (f : NativeFn) (thisArg : Value) (args : List Value) : EvalM Value :=
  match f with
  | .symbolCtor =>
    -- 20.4.1.1. A *missing* description and an `undefined` one are the
    -- same absent description; everything else is ToString'd.
    match args with
    | [] => do pure (.sym (← allocSymbol none))
    | .prim .undef :: _ => do pure (.sym (← allocSymbol none))
    | d :: _ => do
      -- A description is a Lean `String`, as a property key is, so it is
      -- lossy at a lone surrogate (#519's boundary).
      let text ← toStringValue d
      pure (.sym (← allocSymbol (some text.toStringLossy)))
  | .symbolFor => do
    -- 20.4.2.2: the registry's own key, or a fresh symbol written there
    -- under it. The description of a registered symbol is its key.
    let key := (← toStringValue (args.headD undefValue)).toKey
    match (← readObj symbolRegistryRef).getOwn (.str key) with
    | some v => pure v
    | none => do
      let sy ← allocSymbol (some key)
      modifyObj symbolRegistryRef (fun o => o.define (.str key) (Property.ordinary (.sym sy)))
      pure (.sym sy)
  | .symbolKeyFor =>
    match args.headD undefValue with
    | .sym sy => do pure (registryKeyFor (← readObj symbolRegistryRef).properties sy)
    | v => throwJsError .typeError s!"{formatValue v} is not a symbol"
  | .symbolProtoToString => do
    let sy ← thisSymbolValue "toString" thisArg
    pure (.prim (.str sy.descriptiveString))
  | .symbolProtoValueOf => do pure (.sym (← thisSymbolValue "valueOf" thisArg))
  | .symbolDescription => do
    let sy ← thisSymbolValue "description" thisArg
    match sy.description with
    | some d => pure (.prim (.str d))
    | none => pure undefValue
  | .symbolToPrimitive => do
    -- 20.4.3.5 ignores the hint: a symbol is already a primitive.
    pure (.sym (← thisSymbolValue "[Symbol.toPrimitive]" thisArg))
  | .functionHasInstance => do
    pure (.prim (.bool (← ordinaryHasInstance thisArg (args.headD undefValue))))
  | .objectGetOwnPropertySymbols => do
    let r ← toObjectValue (args.headD undefValue)
    newArray ((← readObj r).symbolKeys.map Value.sym)
  | .errorIsError =>
    -- 20.5.2.1: the question is `[[ErrorData]]`, which is `ObjKind.error`,
    -- so `Error.prototype` — an ordinary object — answers `false`.
    match args.headD undefValue with
    | .obj r => do
      match (← readObj r).kind with
      | .error => pure (.prim (.bool true))
      | _ => pure (.prim (.bool false))
    | _ => pure (.prim (.bool false))
  | .aggregateErrorCtor => do
    -- 20.5.7.1.1, in its order: `message`, then the cause, then
    -- `errors`, which step 4 reads with IterableToList. A string
    -- argument is therefore `is not iterable` until `String.prototype`
    -- has an `@@iterator` (#391).
    match args[1]?.getD undefValue with
    | .prim .undef => pure ()
    | m => do
      let msg ← toStringValue m
      match thisArg with
      | .obj r => modifyObj r (fun o => o.define "message" (Property.method (.prim (.str msg))))
      | _ => pure ()
    installErrorCause thisArg (args[2]?.getD undefValue)
    let errorsArg := args.headD undefValue
    let items ← iteratorToList (← getIterator errorsArg)
    let arr ← newArray items
    match thisArg with
    | .obj r => modifyObj r (fun o => o.define "errors" (Property.method arr))
    | _ => pure ()
    pure thisArg
  | _ => pure undefValue
  partial_fixpoint

/-- `JSON.stringify`'s replacer (25.5.2 steps 4–5): a callable one is
carried as it stands, an array one is reduced to its PropertyList, and
anything else is neither. -/
def jsonReplacerOf (replacerArg : Value) : EvalM (Option Value × Option (List String)) := do
  match replacerArg with
  | .obj rr =>
    if ← isCallable replacerArg then pure (some replacerArg, none)
    else
      match (← readObj rr).arrayLength? with
      | some (len, _) => do
        let items ← listFromArrayLike replacerArg 0 len
        pure (none, some (← propertyListOf [] items))
      | none => pure (none, none)
  | _ => pure (none, none)
  partial_fixpoint

/-- `JSON.stringify`'s `space` (25.5.2 step 6) with its wrapper
unwrapped; the clamping is the caller's. -/
def jsonSpaceOf (spaceArg : Value) : EvalM Value := do
  match spaceArg with
  | .obj r =>
    match (← readObj r).kind with
    | .number _ => do pure (Value.prim (.num (← toNumberValue spaceArg)))
    | .string _ => do pure (Value.prim (.str (← toStringValue spaceArg)))
    | _ => pure spaceArg
  | _ => pure spaceArg
  partial_fixpoint

/-- The iteration surface: `%IteratorPrototype%[@@iterator]`, the Array
Iterator, and the two `Object` members that consume an iterable.

It is a definition of its own for `callReflectNative`'s reason —
`callNative`'s `match` is already past the depth at which Lean generates
equation lemmas — but it **is** in `tarski_eval`, because a closed
destructuring or a single `for`-`of` step must reduce without a local
lemma list, and seven arms are far below the ceiling.

The three constructors take ToObject of their receiver (23.1.3.19 step
1), so an array-like works and `Array.prototype.values.call({length: 1})`
iterates. `next` reads its length every step, which is what makes an
array that grows mid-iteration visit the new elements, and writes
`undefined` into `[[IteratedArrayLike]]` when it runs out, which is what
keeps an exhausted iterator done.

The String Iterator is here too, and it is the one walk that steps by
**code point** rather than by code unit: `JsString.codePointAt?` answers
the point starting at an index and how many units it took, which is
exactly the step 22.1.5.1.1 takes.

The arm for anything else is unreachable: `callNative` routes exactly
the nine constructors below here. -/
def callIteratorNative (f : NativeFn) (thisArg : Value) (args : List Value) :
    EvalM Value :=
  match f with
  | .iteratorProtoIterator => pure thisArg
  | .arrayKeys | .arrayValues | .arrayEntries => do
    let o ← toObjectValue thisArg
    let kind := match f with
      | .arrayKeys => IterKind.keys
      | .arrayEntries => IterKind.entries
      | _ => IterKind.values
    let r ← allocObj
      { proto := some arrayIteratorProtoRef,
        kind := .arrayIterator (some (.obj o)) kind 0 }
    pure (.obj r)
  | .arrayIteratorNext =>
    match thisArg with
    | .obj r => do
      match (← readObj r).kind with
      | .arrayIterator iterated kind index =>
        match iterated with
        | none => createIterResult undefValue true
        | some a => do
          let len ← toLengthValue (← getProp a "length")
          if index ≥ len then do
            modifyObj r (fun o => { o with kind := .arrayIterator none kind index })
            createIterResult undefValue true
          else do
            modifyObj r (fun o =>
              { o with kind := .arrayIterator (some a) kind (index + 1) })
            let v ← match kind with
              | .keys => pure (Value.ofNat index)
              | .values => getProp a (Nat.repr index)
              | .entries => do newArray [Value.ofNat index, ← getProp a (Nat.repr index)]
            createIterResult v false
      | _ =>
        throwJsError .typeError
          s!"next method called on incompatible receiver {formatValue thisArg}"
    | _ =>
      throwJsError .typeError
        s!"next method called on incompatible receiver {formatValue thisArg}"
  | .objectFromEntries => do
    match args.headD undefValue with
    | .prim .undef | .prim .null =>
      throwJsError .typeError "Cannot convert undefined or null to object"
    | items => do
      let obj ← newObject
      let ir ← getIterator items
      fromEntriesInto ir obj
      pure (.obj obj)
  | .stringProtoIterator => do
    -- 22.1.3.36: RequireObjectCoercible, then ToString, then a fresh
    -- iterator over the *string* — a receiver that is a wrapper object
    -- is read through its own `toString`.
    match thisArg with
    | .prim .undef | .prim .null =>
      throwJsError .typeError "Cannot convert undefined or null to object"
    | _ => pure ()
    let str ← toStringValue thisArg
    let r ← allocObj
      { proto := some stringIteratorProtoRef, kind := .stringIterator (some str) 0 }
    pure (.obj r)
  | .stringIteratorNext =>
    match thisArg with
    | .obj r => do
      match (← readObj r).kind with
      | .stringIterator iterated index =>
        match iterated with
        | none => createIterResult undefValue true
        | some str =>
          match str.codePointAt? index with
          | none => do
            modifyObj r (fun o => { o with kind := .stringIterator none index })
            createIterResult undefValue true
          | some (_, taken) => do
            modifyObj r (fun o =>
              { o with kind := .stringIterator (some str) (index + taken) })
            createIterResult (.prim (.str (str.extract index (index + taken)))) false
      | _ =>
        throwJsError .typeError
          s!"next method called on incompatible receiver {formatValue thisArg}"
    | _ =>
      throwJsError .typeError
        s!"next method called on incompatible receiver {formatValue thisArg}"
  | .objectGroupBy => do
    match args.headD undefValue with
    | .prim .undef | .prim .null =>
      throwJsError .typeError "Cannot convert undefined or null to object"
    | items => do
      let cb := args[1]?.getD undefValue
      if ← isCallable cb then do
        -- 7.3.35 step 2: a null-prototyped object, so a group named
        -- `toString` is a group and not an inherited method.
        let groups ← allocObj { proto := none }
        let ir ← getIterator items
        groupByInto ir cb groups 0
        pure (.obj groups)
      else throwJsError .typeError "not a function"
  | _ => pure undefValue
  partial_fixpoint

/-- `JSON.parse`'s tree-to-heap step: allocation and nothing else. An
object's members are *definitions*, so a repeated key is the last one and
`__proto__` becomes an own property rather than a prototype change. -/
def jsonToValue : JsonTree → EvalM Value
  | .null => pure (.prim .null)
  | .bool b => pure (.prim (.bool b))
  | .num x => pure (.prim (.num x))
  | .str text => pure (.prim (.str text))
  | .arr items => do newArray (← jsonToValues items)
  | .obj members => do
    let r ← newObject
    jsonMembersInto r members
    pure (.obj r)
  partial_fixpoint

/-- `jsonToValue`'s list walk. -/
def jsonToValues : List JsonTree → EvalM (List Value)
  | [] => pure []
  | t :: rest => do
    let v ← jsonToValue t
    let vs ← jsonToValues rest
    pure (v :: vs)
  partial_fixpoint

/-- `jsonToValue`'s member walk. -/
def jsonMembersInto (r : Ref) : List (String × JsonTree) → EvalM Unit
  | [] => pure ()
  | (k, t) :: rest => do
    let v ← jsonToValue t
    modifyObj r (fun o => o.define (.str k) (Property.ordinary v))
    jsonMembersInto r rest
  partial_fixpoint

/-- InternalizeJSONProperty (25.5.1.1): the reviver's walk, depth first,
each member replaced or deleted before the holder itself is offered. An
array is walked by its length and an object by its enumerable own string
keys, both re-read from the heap as the walk goes, which is what lets a
reviver see what an earlier call did. -/
def internalizeJsonProperty (holder : Ref) (key : String) (reviver : Value) : EvalM Value := do
  let val ← getProp (.obj holder) key
  match val with
  | .obj r => do
    match (← readObj r).arrayLength? with
    | some (len, _) => reviveElements r reviver 0 len
    | none => reviveKeys r reviver (← readObj r).enumerableKeys
  | _ => pure ()
  callFunction reviver (.obj holder) [.prim (.str key), val]
  partial_fixpoint

/-- The reviver's walk over an array's indices. -/
def reviveElements (r : Ref) (reviver : Value) (i len : Nat) : EvalM Unit := do
  if i < len then do
    let newElement ← internalizeJsonProperty r (Nat.repr i) reviver
    match newElement with
    | .prim .undef => removeIfConfigurable r (.str (Nat.repr i))
    | v => createDataProperty r (.str (Nat.repr i)) v
    reviveElements r reviver (i + 1) len
  else pure ()
  partial_fixpoint

/-- The reviver's walk over an object's keys. -/
def reviveKeys (r : Ref) (reviver : Value) : List String → EvalM Unit
  | [] => pure ()
  | k :: rest => do
    let newElement ← internalizeJsonProperty r k reviver
    match newElement with
    | .prim .undef => removeIfConfigurable r (.str k)
    | v => createDataProperty r (.str k) v
    reviveKeys r reviver rest
  partial_fixpoint

/-- `JSON.stringify`'s PropertyList (25.5.2 step 4.b): the array
replacer's members, strings and Numbers only, ToString'd and
deduplicated, keeping the first occurrence's place. -/
def propertyListOf (acc : List String) : List Value → EvalM (List String)
  | [] => pure acc
  | v :: rest => do
    match ← propertyListItem? v with
    | some k => propertyListOf (if acc.contains k then acc else acc ++ [k]) rest
    | none => propertyListOf acc rest
  partial_fixpoint

/-- One member of an array replacer: a string, a Number, or a wrapper
around one of those, and `none` for everything else. The key it becomes
is a Lean `String`, so it is `toKey`'s lossy conversion at a lone
surrogate, as every property key is. -/
def propertyListItem? (v : Value) : EvalM (Option String) := do
  match v with
  | .prim (.str text) => pure (some text.toKey)
  | .prim (.num x) => pure (some (Number.toDecimalString x))
  | .obj r =>
    match (← readObj r).kind with
    | .number _ | .string _ => do pure (some (← toStringValue v).toKey)
    | _ => pure none
  | _ => pure none
  partial_fixpoint

/-- SerializeJSONProperty (25.5.2.2): one member of a holder, or `none`
for a value JSON has no text for — `undefined`, a symbol, and a callable
— which an object omits and an array writes as `null`. -/
def serializeJsonProperty (st : JsonState) (stack : List Ref) (indent : String)
    (key : String) (holder : Ref) : EvalM (Option String) := do
  let read ← getProp (.obj holder) key
  let converted ← jsonToJson read key
  -- A replacer function is called on the *holder*, with the key.
  let replaced ←
    match st.replacer with
    | some rep => callFunction rep (.obj holder) [.prim (.str key), converted]
    | none => pure converted
  serializeJsonValue st stack indent (← jsonUnwrap replaced)
  partial_fixpoint

/-- SerializeJSONProperty's steps 4–11, once the value is the one to be
written. -/
def serializeJsonValue (st : JsonState) (stack : List Ref) (indent : String) (value : Value) :
    EvalM (Option String) := do
  match value with
  | .prim .null => pure (some "null")
  | .prim (.bool b) => pure (some (if b then "true" else "false"))
  -- The JSON text is a Lean `String`, so a lone surrogate in the value is
  -- U+FFFD here rather than 25.5.2.3's `\ud800` escape (#522).
  | .prim (.str text) => pure (some (quoteJsonString text.toStringLossy))
  | .prim (.num x) =>
    -- A finite Number is `Number::toString`, which is what makes `-0`
    -- serialize as `0`; NaN and the infinities are `null`.
    if Number.FloatOps.tsIsFinite x then pure (some (Number.toDecimalString x))
    else pure (some "null")
  | .prim (.bigint _) => throwJsError .typeError "Do not know how to serialize a BigInt"
  | .prim .undef => pure none
  | .sym _ => pure none
  | .obj r => do
    if ← isCallable value then pure none
    else if stack.contains r then
      throwJsError .typeError "Converting circular structure to JSON"
    else if (← readObj r).isArray then serializeJsonArray st (r :: stack) indent r
    else serializeJsonObject st (r :: stack) indent r
  partial_fixpoint

/-- SerializeJSONProperty step 2: `toJSON` looked up on the value with
`GetV` and called with the key. Only an object has one to look up; a
BigInt's is unreachable, `serializeJsonValue` refusing every BigInt. -/
def jsonToJson (value : Value) (key : String) : EvalM Value := do
  match value with
  | .obj _ => do
    let toJson ← getProp value "toJSON"
    if ← isCallable toJson then callFunction toJson value [.prim (.str key)]
    else pure value
  | _ => pure value
  partial_fixpoint

/-- SerializeJSONProperty steps 4–6: a Number, a String, or a Boolean
wrapper is unwrapped. -/
def jsonUnwrap (value : Value) : EvalM Value := do
  match value with
  | .obj r =>
    match (← readObj r).kind with
    | .number _ => do pure (Value.prim (.num (← toNumberValue value)))
    | .string _ => do pure (Value.prim (.str (← toStringValue value)))
    | .boolean b => pure (.prim (.bool b))
    | _ => pure value
  | _ => pure value
  partial_fixpoint

/-- SerializeJSONObject (25.5.2.4). -/
def serializeJsonObject (st : JsonState) (stack : List Ref) (indent : String) (r : Ref) :
    EvalM (Option String) := do
  let stepback := indent
  let inner := indent ++ st.gap
  let keys ←
    match st.propertyList with
    | some ks => pure ks
    | none => pure (← readObj r).enumerableKeys
  let parts ← serializeJsonMembers st stack inner r keys
  if parts.isEmpty then pure (some "{}")
  else if st.gap.isEmpty then pure (some ("{" ++ String.intercalate "," parts ++ "}"))
  else
    pure (some ("{\n" ++ inner ++ String.intercalate (",\n" ++ inner) parts ++
      "\n" ++ stepback ++ "}"))
  partial_fixpoint

/-- An object's members, in order, the omitted ones dropped. -/
def serializeJsonMembers (st : JsonState) (stack : List Ref) (indent : String) (r : Ref) :
    List String → EvalM (List String)
  | [] => pure []
  | k :: rest => do
    let member ← serializeJsonProperty st stack indent k r
    let tail ← serializeJsonMembers st stack indent r rest
    match member with
    | some text =>
      pure ((quoteJsonString k ++ (if st.gap.isEmpty then ":" else ": ") ++ text) :: tail)
    | none => pure tail
  partial_fixpoint

/-- SerializeJSONArray (25.5.2.5). -/
def serializeJsonArray (st : JsonState) (stack : List Ref) (indent : String) (r : Ref) :
    EvalM (Option String) := do
  let stepback := indent
  let inner := indent ++ st.gap
  let len ← toLengthValue (← getProp (.obj r) "length")
  let parts ← serializeJsonElements st stack inner r 0 len
  if parts.isEmpty then pure (some "[]")
  else if st.gap.isEmpty then pure (some ("[" ++ String.intercalate "," parts ++ "]"))
  else
    pure (some ("[\n" ++ inner ++ String.intercalate (",\n" ++ inner) parts ++
      "\n" ++ stepback ++ "]"))
  partial_fixpoint

/-- An array's elements, an omitted one written as `null`. -/
def serializeJsonElements (st : JsonState) (stack : List Ref) (indent : String) (r : Ref)
    (i len : Nat) : EvalM (List String) := do
  if i < len then do
    let element ← serializeJsonProperty st stack indent (Nat.repr i) r
    let rest ← serializeJsonElements st stack indent r (i + 1) len
    pure ((element.getD "null") :: rest)
  else pure []
  partial_fixpoint

/-- `JSON.parse` and `JSON.stringify`. Out of `tarski_eval` for
`callSymbolNative`'s reason. -/
def callJsonNative (f : NativeFn) (_thisArg : Value) (args : List Value) : EvalM Value :=
  match f with
  | .jsonParse => do
    -- The grammar reads a Lean `String`, so a lone surrogate in the text
    -- is U+FFFD before it is parsed (#522).
    let text ← toStringValue (args.headD undefValue)
    match parseJson text.toStringLossy with
    | .error e => throwJsError .syntaxError e.message
    | .ok tree => do
      let unfiltered ← jsonToValue tree
      let reviver := args[1]?.getD undefValue
      if ← isCallable reviver then do
        let root ← newObject
        modifyObj root (fun o => o.define (.str "") (Property.ordinary unfiltered))
        internalizeJsonProperty root "" reviver
      else pure unfiltered
  | .jsonStringify => do
    let value := args.headD undefValue
    let (replacer, propertyList) ← jsonReplacerOf (args[1]?.getD undefValue)
    let space ← jsonSpaceOf (args[2]?.getD undefValue)
    -- A number is clamped to ten spaces, a string is cut to its first
    -- ten characters, and anything else gives no gap at all.
    let gap :=
      match space with
      | .prim (.num x) =>
        match Number.FloatOps.integerOrInfinity? x with
        | some i => spaces (if i ≤ 0 then 0 else if 10 ≤ i then 10 else i.toNat)
        | none => spaces (if x < 0.0 then 0 else 10)
      | .prim (.str text) => (JsString.mk (text.units.take 10)).toStringLossy
      | _ => ""
    let st : JsonState := { replacer, propertyList, gap }
    let wrapper ← newObject
    modifyObj wrapper (fun o => o.define (.str "") (Property.ordinary value))
    match ← serializeJsonProperty st [] "" "" wrapper with
    | some text => pure (.prim (.str text))
    | none => pure undefValue
  | _ => pure undefValue
  partial_fixpoint

/-- RequireObjectCoercible (7.2.1) and then ToString, which is how every
`String.prototype` method but `toString` and `valueOf` reads its
receiver: they are **generic**, so `String.prototype.indexOf.call(123,
"2")` is `1`. `who` names the method, so the refusal says which one was
called on `null`. -/
def requireStringThis (who : String) (v : Value) : EvalM JsString := do
  match v with
  | .prim .undef | .prim .null =>
    throwJsError .typeError s!"String.prototype.{who} called on null or undefined"
  | _ => toStringValue v
  partial_fixpoint

/-- ToUint32 (7.1.6) on a value: ToNumber and then the library's. -/
def toUint32Value (v : Value) : EvalM Nat := do
  pure (Number.FloatOps.tsToUint32 (← toNumberValue v))
  partial_fixpoint

/-- ToUint16 (7.1.7) on a value, which is what each argument of
`String.fromCharCode` goes through. -/
def toUint16Value (v : Value) : EvalM UInt16 := do
  pure (Number.FloatOps.tsToUint16 (← toNumberValue v))
  partial_fixpoint

/-- A whole argument list through ToUint16, left to right. -/
def toUint16Values : List Value → EvalM (List UInt16)
  | [] => pure []
  | v :: rest => do
    let u ← toUint16Value v
    let us ← toUint16Values rest
    pure (u :: us)
  partial_fixpoint

/-- A relative index argument — `slice`'s and `at`'s — as an absolute
one. The sign of an infinity is read off the Number itself, the library's
`integerOrInfinity?` reporting both the same way. -/
def relativeArg (v : Value) (len : Nat) : EvalM Nat := do
  let x ← toNumberValue v
  pure (JsString.relativeIndex len (Number.FloatOps.integerOrInfinity? x) (x < 0.0))
  partial_fixpoint

/-- A position argument clamped to `[0, len]`, where a negative is 0
rather than an offset from the end: `indexOf`'s, `substring`'s,
`startsWith`'s, and `endsWith`'s. -/
def clampArg (v : Value) (len : Nat) : EvalM Nat := do
  let x ← toNumberValue v
  pure (JsString.clampIndex len (Number.FloatOps.integerOrInfinity? x) (x < 0.0))
  partial_fixpoint

/-- `String.raw`'s walk (22.1.2.4 step 8): each raw segment read through
`Get`, so a getter runs, with the substitution after it — the
substitutions being the arguments after the template. It recurses on a
length the heap named, so it is `rw`'s like `joinElements`. -/
def rawSegments (raw : Ref) (len i : Nat) (subs : List Value) : EvalM JsString := do
  if i < len then
    let seg ← toStringValue (← getProp (.obj raw) (Nat.repr i))
    if i + 1 == len then pure seg
    else do
      let sub ← match subs[i]? with
        | some v => toStringValue v
        | none => pure (JsString.ofString "")
      let rest ← rawSegments raw len (i + 1) subs
      pure (seg ++ sub ++ rest)
  else pure (JsString.ofString "")
  partial_fixpoint

/-- `replaceAll`'s splice over the positions `JsString.matchPositions`
found: the text between two matches, then the replacement, which is a
user function's answer when the replacer is callable and
GetSubstitution's when it is a string. `replace` is this over the one
position `indexOf` found. -/
def spliceMatches (s search : JsString) (repl : Value) (functional : Bool)
    (replStr : JsString) (start : Nat) : List Nat → EvalM JsString
  | [] => pure ⟨s.units.drop start⟩
  | p :: rest => do
    let replacement ←
      if functional then
        toStringValue (← callFunction repl undefValue
          [.prim (.str search), Value.ofNat p, .prim (.str s)])
      else pure (JsString.getSubstitution search s p replStr)
    let tail ← spliceMatches s search repl functional replStr (p + search.length) rest
    pure (⟨(s.units.drop start).take (p - start)⟩ ++ replacement ++ tail)
  partial_fixpoint

/-- The `String` surface: 22.1.2's three statics and 22.1.3's thirty-one
prototype methods.

It is a definition of its own, next to `callReflectNative` and for its
reason: `NativeFn` is already at the ceiling `Tarski/Simp.lean` records,
and these arms are behind one constructor over `StringFn` so that
`callNative`'s own `match` does not grow by thirty-four. Like
`callReflectNative`, it is **not** in `tarski_eval`.

Every arm keeps the specification's step order — the receiver coerced
first, then the arguments left to right — because the suite's
`return-abrupt-from-*` tests pin exactly that; what each one then
computes is one of `Js/String/Ops.lean`'s total functions.

The regex and `Symbol` branches of `split`, `replace`, `replaceAll`,
`includes`, `startsWith`, and `endsWith` are unreachable: there is no
`RegExp` (#376) and no `Symbol` (#392), so a non-string search value is
ToString'd. -/
def callStringNative (f : StringFn) (thisArg : Value) (args : List Value) : EvalM Value :=
  match f with
  | .fromCharCode => do
    pure (.prim (.str (JsString.fromCharCode (← toUint16Values args))))
  | .fromCodePoint => do
    match JsString.fromCodePoints (← toNumberValues args) with
    | .ok s => pure (.prim (.str s))
    | .error x =>
      throwJsError .rangeError s!"Invalid code point {Number.toDecimalString x}"
  | .raw => do
    let cooked ← toObjectValue (argAt args 0)
    let raw ← toObjectValue (← getProp (.obj cooked) "raw")
    let len ← toLengthValue (← getProp (.obj raw) "length")
    pure (.prim (.str (← rawSegments raw len 0 (args.drop 1))))
  | .at => do
    let s ← requireStringThis "at" thisArg
    let x ← toNumberValue (argAt args 0)
    match Number.FloatOps.integerOrInfinity? x with
    | none => pure undefValue
    | some n =>
      let k := if n < 0 then (s.length : Int) + n else n
      if k < 0 || (s.length : Int) ≤ k then pure undefValue
      else pure (.prim (.str ((s.unitAt? k.toNat).getD (JsString.ofString ""))))
  | .charAt => do
    let s ← requireStringThis "charAt" thisArg
    let i ← toIntegerOrInfinityValue (argAt args 0)
    match i.bind (fun n => if 0 ≤ n then s.unitAt? n.toNat else none) with
    | some u => pure (.prim (.str u))
    | none => pure (.prim (.str ""))
  | .charCodeAt => do
    let s ← requireStringThis "charCodeAt" thisArg
    let i ← toIntegerOrInfinityValue (argAt args 0)
    match i.bind (fun n => if 0 ≤ n then s.codeUnitAt? n.toNat else none) with
    | some u => pure (Value.ofNat u.toNat)
    | none => pure (.prim (.num Js.floatNaN))
  | .codePointAt => do
    let s ← requireStringThis "codePointAt" thisArg
    let i ← toIntegerOrInfinityValue (argAt args 0)
    match i.bind (fun n => if 0 ≤ n then s.codePointAt? n.toNat else none) with
    | some (cp, _) => pure (Value.ofNat cp)
    | none => pure undefValue
  | .concat => do
    let s ← requireStringThis "concat" thisArg
    let parts ← toStringValues args
    pure (.prim (.str (parts.foldl (fun acc t => acc ++ t) s)))
  | .endsWith => do
    let s ← requireStringThis "endsWith" thisArg
    let pat ← toStringValue (argAt args 0)
    let stop ← match argAt args 1 with
      | .prim .undef => pure s.length
      | v => clampArg v s.length
    pure (.prim (.bool (JsString.endsWith s pat stop)))
  | .includes => do
    let s ← requireStringThis "includes" thisArg
    let pat ← toStringValue (argAt args 0)
    let start ← clampArg (argAt args 1) s.length
    pure (.prim (.bool (JsString.includes s pat start)))
  | .indexOf => do
    let s ← requireStringThis "indexOf" thisArg
    let pat ← toStringValue (argAt args 0)
    let start ← clampArg (argAt args 1) s.length
    match JsString.indexOf s pat start with
    | some i => pure (Value.ofNat i)
    | none => pure (.prim (.num (-1.0)))
  | .isWellFormed => do
    let s ← requireStringThis "isWellFormed" thisArg
    pure (.prim (.bool s.isWellFormed))
  | .lastIndexOf => do
    let s ← requireStringThis "lastIndexOf" thisArg
    let pat ← toStringValue (argAt args 0)
    let x ← toNumberValue (argAt args 1)
    -- A NaN position is `+∞`, which is what makes the search start at
    -- the end rather than at 0.
    let start :=
      if !(x == x) then s.length
      else JsString.clampIndex s.length (Number.FloatOps.integerOrInfinity? x) (x < 0.0)
    match JsString.lastIndexOf s pat start with
    | some i => pure (Value.ofNat i)
    | none => pure (.prim (.num (-1.0)))
  | .localeCompare => do
    let s ← requireStringThis "localeCompare" thisArg
    let that ← toStringValue (argAt args 0)
    pure (.prim (.num (JsString.localeCompareUnits s that)))
  | .normalize => do
    let s ← requireStringThis "normalize" thisArg
    let form ← match argAt args 0 with
      | .prim .undef => pure (JsString.ofString "NFC")
      | v => toStringValue v
    match JsString.normalizeForm? s form with
    | some t => pure (.prim (.str t))
    | none =>
      throwJsError .rangeError
        "The normalization form should be one of NFC, NFD, NFKC, NFKD."
  | .padEnd => do pure (.prim (.str (← padWith "padEnd" thisArg args false)))
  | .padStart => do pure (.prim (.str (← padWith "padStart" thisArg args true)))
  | .«repeat» => do
    let s ← requireStringThis "repeat" thisArg
    let x ← toNumberValue (argAt args 0)
    match Number.FloatOps.integerOrInfinity? x with
    | none => throwJsError .rangeError s!"Invalid count value: {Number.toDecimalString x}"
    | some n =>
      if n < 0 then
        throwJsError .rangeError s!"Invalid count value: {Number.toDecimalString x}"
      -- `n = 0` and an empty receiver both answer `""` before the
      -- length check, so `"".repeat(2 ** 31 - 1)` is a string rather
      -- than a `RangeError` and rather than two billion appends.
      else if n == 0 || s.isEmpty then pure (.prim (.str ""))
      else if JsString.maxStringLength < n.toNat * s.length then
        throwJsError .rangeError "Invalid string length"
      else pure (.prim (.str (s.repeatUnits n.toNat)))
  | .replace => do
    let s ← requireStringThis "replace" thisArg
    let search ← toStringValue (argAt args 0)
    let repl := argAt args 1
    let functional ← isCallable repl
    let replStr ← if functional then pure (JsString.ofString "") else toStringValue repl
    match JsString.indexOf s search 0 with
    | none => pure (.prim (.str s))
    | some p => do
      pure (.prim (.str (← spliceMatches s search repl functional replStr 0 [p])))
  | .replaceAll => do
    let s ← requireStringThis "replaceAll" thisArg
    let search ← toStringValue (argAt args 0)
    let repl := argAt args 1
    let functional ← isCallable repl
    let replStr ← if functional then pure (JsString.ofString "") else toStringValue repl
    pure (.prim (.str
      (← spliceMatches s search repl functional replStr 0 (JsString.matchPositions s search))))
  | .slice => do
    let s ← requireStringThis "slice" thisArg
    let a ← relativeArg (argAt args 0) s.length
    let b ← match argAt args 1 with
      | .prim .undef => pure s.length
      | v => relativeArg v s.length
    pure (.prim (.str (JsString.slice s a b)))
  | .split => do
    let s ← requireStringThis "split" thisArg
    let limit ← match argAt args 1 with
      | .prim .undef => pure 4294967295
      | v => toUint32Value v
    let sep ← toStringValue (argAt args 0)
    if limit == 0 then newArray []
    else
      match argAt args 0 with
      | .prim .undef => newArray [.prim (.str s)]
      | _ => newArray ((JsString.splitOn s sep limit).map (fun t => Value.prim (.str t)))
  | .startsWith => do
    let s ← requireStringThis "startsWith" thisArg
    let pat ← toStringValue (argAt args 0)
    let start ← clampArg (argAt args 1) s.length
    pure (.prim (.bool (JsString.startsWith s pat start)))
  | .substring => do
    let s ← requireStringThis "substring" thisArg
    let a ← clampArg (argAt args 0) s.length
    let b ← match argAt args 1 with
      | .prim .undef => pure s.length
      | v => clampArg v s.length
    pure (.prim (.str (JsString.substring s a b)))
  | .toLocaleLowerCase => do
    pure (.prim (.str (← requireStringThis "toLocaleLowerCase" thisArg).lowerAscii))
  | .toLocaleUpperCase => do
    pure (.prim (.str (← requireStringThis "toLocaleUpperCase" thisArg).upperAscii))
  | .toLowerCase => do
    pure (.prim (.str (← requireStringThis "toLowerCase" thisArg).lowerAscii))
  | .«toString» => do pure (.prim (.str (← thisStringValue "toString" thisArg)))
  | .«toUpperCase» => do
    pure (.prim (.str (← requireStringThis "toUpperCase" thisArg).upperAscii))
  | .toWellFormed => do
    pure (.prim (.str (← requireStringThis "toWellFormed" thisArg).toWellFormed))
  | .trim => do pure (.prim (.str (← requireStringThis "trim" thisArg).trim))
  | .trimEnd => do pure (.prim (.str (← requireStringThis "trimEnd" thisArg).trimEnd))
  | .trimStart => do pure (.prim (.str (← requireStringThis "trimStart" thisArg).trimStart))
  | .valueOf => do pure (.prim (.str (← thisStringValue "valueOf" thisArg)))
  partial_fixpoint

/-- StringPad (22.1.3.17.1), which `padStart` and `padEnd` differ in one
Bool by. The early return at step 4 comes **before** the filler is
coerced, so `"abc".padStart(0, { toString() { throw } })` does not
throw. -/
def padWith (who : String) (thisArg : Value) (args : List Value) (atStart : Bool) :
    EvalM JsString := do
  let s ← requireStringThis who thisArg
  let maxLength ← toLengthValue (argAt args 0)
  if maxLength ≤ s.length then pure s
  else if JsString.maxStringLength < maxLength then
    throwJsError .rangeError "Invalid string length"
  else do
    let fill ← match argAt args 1 with
      | .prim .undef => pure (JsString.ofString " ")
      | v => toStringValue v
    pure (JsString.pad s maxLength fill atStart)
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
    | _ => some fallback
  allocObj { proto }
  partial_fixpoint


/-- Whether `p` is on `o`'s prototype chain, `o` itself not counted —
`[[HasInstance]]`'s walk. No fuel, as `getProp` has none: a cycle is a
program that does not terminate, and `Object.setPrototypeOf` refuses to
build one (10.4.7.2 step 8) for exactly that reason. -/
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
  | .sym _ => throwJsError .typeError "not a constructor"
  | .obj r => do
    let o ← readObj r
    match o.callable with
    | none => throwJsError .typeError "not a constructor"
    | some (.native (.errorCtor k)) => do
      -- The native answers the object it was handed, so the
      -- return-object rule below holds trivially and is not written out.
      -- `[[ErrorData]]` is what `Object.prototype.toString` reads.
      let fresh ← allocFromConstructor newTarget k.protoRef
      modifyObj fresh (fun o => { o with kind := .error })
      callNative (.errorCtor k) (.obj fresh) args
    | some (.native .aggregateErrorCtor) => do
      let fresh ← allocFromConstructor newTarget aggregateErrorProtoRef
      modifyObj fresh (fun o => { o with kind := .error })
      callNative .aggregateErrorCtor (.obj fresh) args
    | some (.native n) =>
      if n.constructs then constructNative n newTarget args
      else throwJsError .typeError "not a constructor"
    | some (.bound b) =>
      if b.constructs then constructBound b newTarget f args
      else throwJsError .typeError "not a constructor"
    | some (.closure c) =>
      match c.kind with
      | .arrow | .method => throwJsError .typeError "not a constructor"
      | .classCtor derived implicit => constructClass r c derived implicit newTarget args
      | .ordinary => do
        let fresh ← allocFromConstructor newTarget objectProtoRef
        match ← callFunction f (.obj fresh) args with
        | .obj result => pure (.obj result)
        | _ => pure (.obj fresh)
  partial_fixpoint

/-- `[[Construct]]` of a bound function (10.4.1.2): the target
constructs, and NewTarget is repointed at it when the bound function
itself was the NewTarget. Split out for the reason `callBound` is. -/
def constructBound (b : BoundFunction) (newTarget f : Value) (args : List Value) :
    EvalM Value :=
  construct (.obj b.target)
    (if strictEqValue newTarget f then .obj b.target else newTarget)
    (b.boundArgs ++ args)
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
      match ← superConstructor r with
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
      | _ =>
        throwJsError .typeError "Derived constructors may only return object or undefined"
  else do
    let fresh ← allocFromConstructor newTarget objectProtoRef
    initializeInstance r (.obj fresh)
    if implicit then pure (.obj fresh)
    else
      match ← runConstructor r c (some (.obj fresh)) newTarget args with
      | (.obj result, _) => pure (.obj result)
      | _ => pure (.obj fresh)
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
public one goes through `Obj.define`, so an inherited setter of the
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
    -- NamedEvaluation: a field's initializer takes the field's spelling,
    -- `#x` and all.
    let fieldName := match f.key with
      | .«public» n => n
      | .«private» n => "#" ++ n
    let v ←
      match f.value with
      | some e => evalNamed env fieldName e
      | none => pure undefValue
    match target, f.key with
    | .obj t, .«public» name => modifyObj t (fun o => o.define name (Property.ordinary v))
    | .obj t, .«private» name => do
      let k ← privateName env name
      addPrivate t name k v
    -- The target is always the object being built, so this arm is
    -- unreachable; `Value` is not a subtype.
    | _, _ => pure ()
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
def evalClass (env : Env) (d : ClassDef) (name : String) : EvalM Value := do
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
            | _ => none
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
  -- The constructor is a function object like any other: `length` —
  -- its parameter list's ExpectedArgumentCount, which an implicit
  -- constructor has none of, the 0 the spec's `constructor(...args)`
  -- also has — and `name`, each with no attribute but configurability,
  -- then `prototype` with none at all (15.7.14 step 15 makes it
  -- non-writable). A class with no heritage gets `Function.prototype` as
  -- its `[[Prototype]]`; one with a heritage gets the superclass, which
  -- is what makes a static method inherited. An anonymous class takes
  -- NamedEvaluation's name.
  let F ← allocObj
    { proto := some (ctorParent.getD functionProtoRef),
      callable := some (.closure ctor),
      properties :=
        [ ("length", Property.attribute (Value.ofNat (expectedArgumentCount params))),
          ("name", Property.attribute (.prim (.str (d.name.getD name)))),
          ("prototype", Property.constant (.obj proto)) ] }
  modifyObj proto (fun o => o.define "constructor" (Property.method (.obj F)))
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

/-- GetSuperConstructor (13.3.7.3) with its one refusal folded in: the
active function object's `[[Prototype]]`, and `none` when that is not a
constructor. `class A extends null {}` is the case that matters —
15.7.14 step 10.b gives its constructor `%Function.prototype%` as a
`[[Prototype]]`, which is callable and not constructible, so `super()`
in it refuses exactly as a null parent does. -/
def superConstructor (r : Ref) : EvalM (Option Ref) := do
  match (← readObj r).proto with
  | none => pure none
  | some parent =>
    if ← isConstructor (.obj parent) then pure (some parent) else pure none

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
    | _ => pure (none, receiver)
  partial_fixpoint

/-- The read itself, once `superBase` has the two halves of the
reference. A home object with no prototype reads through null, which is
`getProp`'s own `TypeError` rather than a message of its own. -/
def superRead (parent : Option Ref) (receiver : Value) (key : Key) : EvalM Value :=
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
  | .forInStmt left right body, _ => evalForInLoop env [] left right body
  | .forOfStmt left right body, _ => evalForOfLoop env [] left right body
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
    let v ← evalClass env cls name
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
without a parameter binds nothing, and a binding pattern binds each of
its leaves in that same scope. -/
def evalCatch (env : Env) (h : CatchClause) (e : Value) : EvalM (Option Value) := do
  let inner ← match h.param with
    | none => pure env
    | some p => do
      let inner ← allocNames env true p.boundNames
      bindPattern inner .init p e
      pure inner
  evalBlock inner h.body (some undefValue)
  partial_fixpoint

/-- InstanceofOperator (13.10.2). `GetMethod(target, @@hasInstance)`
comes first, and only a non-object right operand with no handler at all
is the `not callable` refusal. The intrinsic handler is short-circuited
**by identity**: calling `%Function.prototype[@@hasInstance]%` would run
OrdinaryHasInstance and nothing else, so a proof about an ordinary
`instanceof` pays one `getProp` and no call. -/
def instanceOf (v target : Value) : EvalM Bool := do
  match target with
  | .obj _ => do
    match ← getProp target WellKnownSymbol.hasInstance.key with
    | .obj h =>
      if h == functionHasInstanceRef then ordinaryHasInstance target v
      else if ← isCallable (.obj h) then
        pure (toBooleanPrim (← callFunction (.obj h) target [v]))
      else throwJsError .typeError "Right-hand side of 'instanceof' is not callable"
    | .prim .undef =>
      if ← isCallable target then ordinaryHasInstance target v
      else throwJsError .typeError "Right-hand side of 'instanceof' is not callable"
    | .prim .null =>
      if ← isCallable target then ordinaryHasInstance target v
      else throwJsError .typeError "Right-hand side of 'instanceof' is not callable"
    | _ => throwJsError .typeError "Right-hand side of 'instanceof' is not callable"
  | _ => throwJsError .typeError "Right-hand side of 'instanceof' is not callable"
  partial_fixpoint

/-- OrdinaryHasInstance (7.3.22): a non-callable right operand is
`false` rather than a throw — the refusal belongs to `instanceOf`'s own
step 4 — a bound function defers to its target, the `prototype` property
must be an object, and the question is then whether that object is on the
left operand's prototype chain. A primitive left operand is not an
instance of anything. -/
def ordinaryHasInstance (target v : Value) : EvalM Bool := do
  match target with
  | .obj r =>
    match (← readObj r).callable with
    | none => pure false
    | some (.bound b) => instanceOfBound v b
    | some _ =>
      match v with
      | .obj o =>
        match ← getProp target "prototype" with
        | .obj p => protoChainHas o p
        | _ =>
          throwJsError .typeError "Function has non-object prototype in instanceof check"
      | _ => pure false
  | _ => pure false
  partial_fixpoint

/-- OrdinaryHasInstance step 2: a bound right operand defers to its
target. Split out for the reason `callBound` is — the target is a heap
link — so `instanceOf` itself stays simp-able. -/
def instanceOfBound (v : Value) (b : BoundFunction) : EvalM Bool :=
  instanceOf v (.obj b.target)
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
  | .forInStmt left right body, _ => evalForInLoop env labels left right body
  | .forOfStmt left right body, _ => evalForOfLoop env labels left right body
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
      -- NamedEvaluation: `const f = () => 1;` names the arrow `f`. A
      -- pattern declarator names nothing, having no single name.
      let v ← match init with
        | some e =>
          match d.target with
          | .target (.ident n) => evalNamed env n e
          | _ => evalExpr env e
        | none => pure undefValue
      match kind with
      | .«var» => bindPattern env .«var» d.target v
      | _ => bindPattern env .init d.target v
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
      pure (inner, if kind == .«let» then declarators.flatMap (·.target.boundNames) else [])
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

/-- ForIn/OfHeadEvaluation (14.7.5.6) and the BreakableStatement around
it. A `let` or `const` head evaluates the right operand in a scope
holding one *uninitialized* cell for the name, so `for (let x in x)` is
the temporal dead zone's `ReferenceError`; every other head evaluates it
in the enclosing scope. A nullish right operand runs the body not at all
and completes `undefined`. -/
def evalForInLoop (env : Env) (labels : List String) (left : ForInLeft) (right : Expr)
    (body : Stmt) : EvalM (Option Value) := do
  let headEnv ←
    match left with
    | .decl .«var» _ => pure env
    | .decl kind p => allocNames env kind.isMutable p.boundNames
    | .target _ => pure env
    | .pattern _ => pure env
  let obj ← evalExpr headEnv right
  match obj with
  | .prim .undef => pure (some undefValue)
  | .prim .null => pure (some undefValue)
  | _ => do
    let r ← toObjectValue obj
    match ← attempt
      (evalForIn env labels left body r (← readObj r).stringKeys [] (some undefValue)) with
    | .ok v => pure v
    | .error (.«break» none v) => pure v
    | .error c => throwCompletion c
  partial_fixpoint

/-- EnumerateObjectProperties' informative algorithm (14.7.5.9) over one
object's snapshotted keys. A key is visited only if it is **still** an
own property when its turn comes and that property is enumerable — a key
the body deleted is skipped, and one the body added is not visited at
all, the list having been taken when the object was reached. A key whose
property is merely non-enumerable still shadows the prototypes', which is
why it joins `visited` either way and a deleted one does not.

This recurses on the key list, which is data; the step to the next object
is `forInNext`'s, and that is the only part a proof unfolds with `rw`. -/
def evalForIn (env : Env) (labels : List String) (left : ForInLeft) (body : Stmt)
    (r : Ref) (keys visited : List String) (acc : Option Value) : EvalM (Option Value) := do
  match keys with
  | [] => forInNext env labels left body r visited acc
  | k :: rest =>
    match (← readObj r).ownProperty k with
    | none => evalForIn env labels left body r rest visited acc
    | some p =>
      if p.enumerable then do
        let inner ← bindForIn env left (.prim (.str k))
        let v ←
          match ← attempt (evalStmt inner body acc) with
          | .ok v => pure v
          | .error (.«continue» l v) =>
            if loopContinues labels l then pure v else throwCompletion (.«continue» l v)
          | .error c => throwCompletion c
        evalForIn env labels left body r rest (k :: visited) v
      else evalForIn env labels left body r rest (k :: visited) acc
  partial_fixpoint

/-- The step to the next object on the prototype chain, with every key
already seen struck from its own. It is the one part of `for`-`in` that
recurses on the heap, so it is the one unfolded with `rw`. -/
def forInNext (env : Env) (labels : List String) (left : ForInLeft) (body : Stmt)
    (r : Ref) (visited : List String) (acc : Option Value) : EvalM (Option Value) := do
  match (← readObj r).proto with
  | none => pure acc
  | some p =>
    evalForIn env labels left body p
      ((← readObj p).stringKeys.filter (fun k => !visited.contains k)) visited acc
  partial_fixpoint

/-- ForIn/OfHeadEvaluation (14.7.5.6) with `iterate`, and the
BreakableStatement around it. The head scope is the `for`-`in`'s: a `let`
or `const` head evaluates the right operand with one *uninitialized* cell
per bound name, so `for (let x of x)` is the dead zone's
`ReferenceError`. There is no `attempt` here — `evalForOf` answers its
own `break`, because it has an iterator to close first. -/
def evalForOfLoop (env : Env) (labels : List String) (left : ForInLeft) (right : Expr)
    (body : Stmt) : EvalM (Option Value) := do
  let headEnv ←
    match left with
    | .decl .«var» _ => pure env
    | .decl kind p => allocNames env kind.isMutable p.boundNames
    | .target _ => pure env
    | .pattern _ => pure env
  let rhs ← evalExpr headEnv right
  let ir ← getIterator rhs
  evalForOf env labels left body ir (some undefValue)
  partial_fixpoint

/-- ForIn/OfBodyEvaluation (14.7.5.7) steps 6.a–6.l for `iterate`. The
binding is *inside* the `attempt` because step 6.h closes the iterator
when the binding itself fails. Exhaustion is the only exit that does not
close, and a throw from the step never reaches here — `iteratorStep`
throws for the iterator, which closes nothing.

This recurses until the iterator says stop, so it is `rw`'s and never a
simp set's. -/
def evalForOf (env : Env) (labels : List String) (left : ForInLeft) (body : Stmt)
    (ir : IteratorRecord) (acc : Option Value) : EvalM (Option Value) := do
  match ← iteratorStep ir with
  | none => pure acc
  | some v =>
    match ← attempt (do
      let inner ← bindForIn env left v
      evalStmt inner body acc) with
    | .ok v' => evalForOf env labels left body ir v'
    | .error (.«continue» l v') =>
      if loopContinues labels l then evalForOf env labels left body ir v'
      else do
        iteratorClose ir (some (.«continue» l v'))
        throwCompletion (.«continue» l v')
    | .error (.«break» none v') => do
      iteratorClose ir none
      pure v'
    | .error c => do
      iteratorClose ir (some c)
      throwCompletion c
  partial_fixpoint

/-- Bind one key or value to the head of a `for`-`in` or a `for`-`of`. A
`var`, an assignment target, and an assignment pattern write the bindings
that are already there and answer the same scope; a `let` or a `const`
gets **fresh cells per iteration**, which is
CreatePerIterationEnvironment's effect and what makes two closures the
body builds see two bindings. -/
def bindForIn (env : Env) (left : ForInLeft) (v : Value) : EvalM Env := do
  match left with
  | .decl .«var» p => do
    bindPattern env .«var» p v
    pure env
  | .decl kind p => do
    let inner ← allocNames env kind.isMutable p.boundNames
    bindPattern inner .init p v
    pure inner
  | .pattern p => do
    bindPattern env .assign p v
    pure env
  | .target (.ident name) => do
    putIdent env name v
    pure env
  | .target (.member object name) => do
    let base ← evalExpr env object
    setProp base name v
    pure env
  | .target (.index object key) => do
    let base ← evalExpr env object
    let k ← evalExpr env key
    setProp base (← toPropertyKey k) v
    pure env
  | .target (.privateMember object name) => do
    let base ← evalExpr env object
    writePrivate env base name v
    pure env
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
  | .obj _ =>
    match ← attempt (toStringValue v) with
    | .ok s => pure (some s.toStringLossy)
    | .error _ => pure none
  | _ => pure none

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
    | .array len _ =>
      (List.range len).filterMap fun i =>
        match o.getOwn (Key.str (toString i)) with
        | some (.prim (.str s)) => some s.toStringLossy
        | _ => none
    | _ => []

end Tarski
