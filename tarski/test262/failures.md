# The failure list for the PR-gated slice

Written 2026-09-15 against test262 at `419d3e0a2273ba01a3bfcbec423f2801425b8e93`
(`tarski/test262/pin.json`), from one run of

```bash
node ../dist/tarski/frontend/src/test262/cli.js --slice-file test262/slice.txt
```

Every failing test in `tarski/test262/slice.txt` is classified here — the
harness, the 27 language directories the thales emitter maps (#383), the
three built-ins directories #382 added, the two global parsers #388
added, the two class directories #384 added, the fifteen declaration
instantiation, jump, and `arguments` directories #393 added, the two
`Object` and `Function` directories #389 added, the three template and
object-literal directories #395 added, the seven `Symbol`, `JSON`, and
`*Error` directories #392 added, `test/built-ins/String`, which #391
added, and the ten iterator, `for`-`of`, spread, and array-literal
directories #394 added — and
`tarski/frontend/tests/test262-failures.test.ts` holds this file and
`tarski/test262/expected.json` together: each directory named here is a key
of that file, every directory with a positive `fail` count appears, and the
`fails` column sums to exactly that count. So a ratchet that moves a count
has to re-classify what moved.

The four classes:

- **builtin** — a built-in or an intrinsic the realm does not have yet. The
  test's own subject is evaluated correctly, or would be if the name
  resolved.
- **protocol** — a runtime construct the evaluator does not model and the
  decoder cannot see, so it reaches evaluation and answers wrongly rather
  than refusing.
- **out-of-scope** — what #376 excludes: `eval`, the `Function`
  constructor, generators, typed arrays, `Date`, and the rest.
- **bug** — a real defect, filed as its own issue. `owner` is that issue.

`owner` is the issue the row waits on. Nothing here waits on #383, on
#382, on #388, on #384, on #393, on #389, on #395, on #392, or on #391: no failure
in the slice is caused by the statements and operators #383 added, none
is a `Math`, `Number`, or `Boolean` member answering the wrong number,
**not one row is a conversion between a Number and a String answering the
wrong thing**, **none is a class evaluating wrongly**, **none is
declaration instantiation, a parameter's dead zone, a default's scope,
`arguments`, a `switch`, a label, a jump, or `do`/`while` answering
wrongly**, **not one row is a property descriptor, an own-key order, an
enumerability, a `delete`, an `in`, a `for`-`in`, or an `Object` or
`Function` member answering the wrong thing**, **none is an object
literal's members running out of order or defining the wrong thing, or a
template building the wrong string or the wrong template object**, and
**not one row is a symbol, a symbol-keyed property, a JSON text, or an
`Error`'s `cause` answering the wrong thing** — the 118 rows that waited
on #392 are gone, and no row has replaced them under that number — and
**not one row is a `String` member, a String exotic object, or a
code-unit answer — `length`, an index, an order, a surrogate pair —
answering the wrong thing**. The 207 rows that waited on #391 are gone:
the String wrapper object exists, and a string is a sequence of UTF-16
code units.

The 1,451 failures below, by owner: 915 what #376 excludes (`eval`,
`Date`, `RegExp`, `Proxy`, `Reflect`, typed arrays, the keyed
collections, explicit resource management, the `Iterator` constructor and
its helpers, `Error.prototype.stack`, `JSON.rawJSON` and the reviver's
source text, the `Function` constructor's semantics, and
`nativeFunctionMatcher.js`, which matches source text with a regular
expression), 185 the global object (#487), 150 the transcendental `Math`
members (#434), 80 the rest of `Array.prototype` and `@@species` (#390),
65 the global `isNaN` and `isFinite` (#441), 15 the Unicode character
database (#518), 13 `Math.clz32`/`imul` (#440), 10 the `@@split`,
`@@replace`, and `@@match` lookups the `String` methods skip (#523), 5
`Math.random` (#445), and 13 the seven filed defects (#436, #460, #496,
#499, #512, #516, #522).

**`test/built-ins/String` is 920 pass and 148 fail** over 41 rows, with
152 unsupported and three not run. Not one of the 148 is a `String`
member answering the wrong thing: 77 are regular expressions (#376),
which is `match`, `matchAll`, `search`, and the regex arguments to
`split` and `replace`; 15 are the
Unicode character database (#518) — the case-mapping tests and the two
`normalize` results, which are what ASCII case mapping and an identity
`normalize` cost; 15 are the rest of `Array.prototype` (#390), reached
as ToString of an array argument; 10 are the `@@split`, `@@replace`, and
`@@match` protocol lookups (#523), which the plan for this slice left to
#392 and #392, merging first, could not add to methods that did not yet
exist; 9 are `eval`; three are `Reflect.construct`; three are the global
object; and one is a non-callable `@@toPrimitive` falling through to
OrdinaryToPrimitive (#516). The 152 unsupported are 99
regular-expression literals, 21 `!=`, 11 BigInt literals, 7 the comma
operator, and 4 the `Function` constructor.

**The two `Object` and `Function` directories are 3,031 pass and 519
fail** before this slice and are 3,075 and 483 after it: the 38 rows
that waited on iterators are gone — `Object.fromEntries` is 25 pass and 0
fail against 0 and 25, `Object.groupBy` 14 and 0 against 2 and 12 — and
one `Object/keys` test that was unsupported now runs and reaches `Proxy`.
Their 483: 292 `eval`, `Date`, `RegExp`, `Proxy`, `Reflect`, and typed
arrays (#376); 143 the global object, whose `this` at top level a third
of `Object`'s older tests reach for (#487); 39 the rest of
`Array.prototype`, which the order tests reach through `map` and
`indexOf` (#390); and 9 `Math` members the library does not model, read
through `getOwnPropertyDescriptor` (#434, #445). None is a filed
defect.
**The `propertyHelper.js`-based tests run and pass**: `Math/abs` is 8 and
0, and `length.js`, `name.js`, and `prop-desc.js` under it are three of
them.

`test/harness` is 61 pass and 20 fail, against 61 and 18: two more of
`propertyHelper.js`'s own tests decode now, and both reach for the global
object. What is left is `Array.prototype` (7), the global object (8),
typed arrays (4), and `Date` (1).

**The seven directories #392 added are 330 pass, 127 fail, and 52
unsupported**: `Symbol` 68/9/19, `JSON` 114/37/14, `Error` 48/37/8,
`NativeErrors` 74/14/6, `AggregateError` 17/6/2, `SuppressedError`
0/20/2, and `ThrowTypeError` 9/4/1. Of the 132, 103 are what #376
excludes — 32 `Error.prototype.stack`, which is not in the specification
and is absent by design; 23 explicit resource management, which is the
whole of `SuppressedError` and the two `Symbol.dispose` members; 22
`Proxy`; 16 `JSON.rawJSON`, `JSON.isRawJSON`, and the reviver's `context`
argument, a stage-3 proposal; 9 `isConstructor.js`, which needs
`Reflect.construct`; and 1 `RegExp` — 11 the global object (#487), 7
`Array.prototype` and `@@species` (#390), 2 a defect #392 found and
filed (#512), and 1 `JSON.stringify` writing a lone
surrogate as U+FFFD rather than its `\u` escape, because the JSON text
is a Lean `String` (#522). **Not one is a symbol, a JSON text, or an
`Error` member answering the wrong thing.**

`%ThrowTypeError%` is extensible where 10.2.4.1 makes it frozen, which
`ThrowTypeError/extensible.js` and `frozen.js` see. It is a realm
literal's missing field rather than anything this slice wrote, so it is
filed as #512 rather than fixed here.

**Two class evaluations were wrong** when the class directories were
first scored and are not wrong now. `super[super()]` read the key before
the `this` binding, where 13.3.7.2 reads the binding first, so the
derived constructor's dead zone was not reached; that is `superBase` in
`Tarski/Eval.lean`, and `ClassesTest` pins it. The other was a bridge
limit rather than an evaluator one: tsc refuses `a?.b.#c`, which is valid
JavaScript, so four tests under `class/elements` are **harness errors**
rather than failures and appear in no row below. #472 owns them.

**The two limits #391 left are filed rather than hidden.** Case mapping
is ASCII-only and `normalize` validates its form and answers its input,
because Lean has no Unicode character database and shipping one is a
slice of its own; the sixteen case-mapping tests and the three
`normalize` results wait on #518. And a property key is still a Lean
`String`, so `JsString.toKey` is lossy at a lone surrogate and
`o["\uD800"]` and `o["\uFFFD"]` are one key; no test in the slice
exercises it, and #519 owns it.

**Three defects an earlier slice found are filed rather than fixed.**
`estree.ts` gives a `static constructor() {}` the ESTree kind of a class
constructor and drops its `static` flag (#496), which two
`grammar-static-ctor-meth-valid.js` tests reach now that a function has a
`hasOwnProperty` to call; and the bridge drops the parentheses that keep
NamedEvaluation from naming `(fn) = function () {}` (#499). The third is
older: a numeric literal that overflows to `Infinity` reaches Lean as
JSON `null` (#460).

The divergence #436 records is now observable and is now a row of its
own: `applyCoercing` runs ToPrimitive on both operands before ToNumber on
either, where 13.15.3 converts the left operand fully first for every
operator but `+`. It takes a Symbol operand to see, so the four
`order-of-evaluation` tests under `division`, `modulus`,
`multiplication`, and `subtraction` reach it for the first time in this
slice; `addition`'s passes, `+` being the one operator whose order this
matches. Fixing it is #436's, not this slice's.

**The ten directories this slice added are 591 pass, 49 fail, and 149
unsupported.** `statements/for-of` is 450 pass and 40 fail across its own
directory and its `dstr` subtree — the subtree itself is 403 and **0** —
and not one of the 40 is the loop: 18 are typed arrays, 10 the keyed
collections, 6 `eval`, 3 `Array.prototype.pop`, 2 `using` declarations,
and 1 `Proxy`. `expressions/array` is 50 pass and 0 fail,
`expressions/new` 54 and 0, `ArrayIteratorPrototype` 9 and 9 — those 9
failures typed arrays and nothing else — and the four `Array.prototype`
iterator members 28 and 0. **Every other directory's `dstr` subtree
ratcheted with them**, which is where most of the 2,456 newly passing
tests are, and the String iterator this slice added on top of #391's
wrapper cleared `String/prototype/Symbol.iterator` to 6 pass and 0 fail.

## The table

| directory                                                             | fails | class        | why                                                                                                                 | owner |
| --------------------------------------------------------------------- | ----- | ------------ | ------------------------------------------------------------------------------------------------------------------- | ----- |
| `test/built-ins/AggregateError`                                       | 1     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/AggregateError`                                       | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/AggregateError`                                       | 1     | out-of-scope | `promiseHelper.js` needs promises                                                                                   | #376  |
| `test/built-ins/AggregateError`                                       | 1     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/ArrayIteratorPrototype/next`                          | 9     | out-of-scope | typed arrays and their buffers are excluded by the epic                                                             | #376  |
| `test/built-ins/Boolean`                                              | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Boolean`                                              | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/Boolean`                                              | 1     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/Boolean/prototype/toString`                           | 1     | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Boolean/prototype/valueOf`                            | 1     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/Error`                                                | 1     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/Error`                                                | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/Error`                                                | 1     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/Error/prototype/stack`                                | 32    | out-of-scope | `Error.prototype.stack` is not in the specification and is absent by design                                         | #376  |
| `test/built-ins/Error/prototype/toString`                             | 2     | builtin      | the rest of `Array.prototype` is absent, `toString` among it                                                        | #390  |
| `test/built-ins/Function`                                             | 21    | builtin      | `Function.prototype.caller` and `arguments` are the `%ThrowTypeError%` accessors                                    | #487  |
| `test/built-ins/Function`                                             | 5     | out-of-scope | the `Function` constructor is excluded by the epic                                                                  | #376  |
| `test/built-ins/Function`                                             | 5     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/Function`                                             | 2     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Function`                                             | 1     | builtin      | the rest of `Array.prototype` is absent, `toString` among it                                                        | #390  |
| `test/built-ins/Function/internals/Construct`                         | 1     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/Function/prototype`                                   | 1     | builtin      | the rest of `Array.prototype` is absent, `toString` among it                                                        | #390  |
| `test/built-ins/Function/prototype/Symbol.hasInstance`                | 1     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/Function/prototype/apply`                             | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Function/prototype/bind`                              | 7     | builtin      | `Function.prototype.caller` and `arguments` are the `%ThrowTypeError%` accessors                                    | #487  |
| `test/built-ins/Function/prototype/bind`                              | 2     | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Function/prototype/call`                              | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Function/prototype/caller-arguments`                  | 1     | builtin      | `Function.prototype.caller` and `arguments` are the `%ThrowTypeError%` accessors                                    | #487  |
| `test/built-ins/Function/prototype/toString`                          | 2     | out-of-scope | `nativeFunctionMatcher.js` matches source text with a regular expression                                            | #376  |
| `test/built-ins/Function/prototype/toString`                          | 1     | out-of-scope | the bridge keeps no source text, and the matcher is a regular expression                                            | #376  |
| `test/built-ins/JSON`                                                 | 1     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/JSON/isRawJSON`                                       | 6     | out-of-scope | `JSON.rawJSON` and the reviver's source text are a stage-3 proposal                                                 | #376  |
| `test/built-ins/JSON/parse`                                           | 9     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/JSON/parse`                                           | 5     | out-of-scope | `JSON.rawJSON` and the reviver's source text are a stage-3 proposal                                                 | #376  |
| `test/built-ins/JSON/rawJSON`                                         | 9     | out-of-scope | `JSON.rawJSON` and the reviver's source text are a stage-3 proposal                                                 | #376  |
| `test/built-ins/JSON/stringify`                                       | 9     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/JSON/stringify`                                       | 1     | builtin      | the rest of `Array.prototype` is absent, `toString` among it                                                        | #390  |
| `test/built-ins/JSON/stringify`                                       | 1     | bug          | `JSON.stringify` quotes a string through a Lean `String`, so a lone surrogate is U+FFFD rather than its `\u` escape | #522  |
| `test/built-ins/Math`                                                 | 1     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/Math/acos`                                            | 7     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                          | #434  |
| `test/built-ins/Math/acos`                                            | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/Math/acosh`                                           | 6     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                          | #434  |
| `test/built-ins/Math/acosh`                                           | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/Math/asin`                                            | 8     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                          | #434  |
| `test/built-ins/Math/asin`                                            | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/Math/asinh`                                           | 4     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                          | #434  |
| `test/built-ins/Math/asinh`                                           | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/Math/atan`                                            | 6     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                          | #434  |
| `test/built-ins/Math/atan`                                            | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/Math/atan2`                                           | 10    | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                          | #434  |
| `test/built-ins/Math/atan2`                                           | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/Math/atanh`                                           | 4     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                          | #434  |
| `test/built-ins/Math/atanh`                                           | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/Math/cbrt`                                            | 4     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                          | #434  |
| `test/built-ins/Math/cbrt`                                            | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/Math/clz32`                                           | 9     | builtin      | `Math.clz32` and `Math.imul` need ToInt32 and ToUint32                                                              | #440  |
| `test/built-ins/Math/clz32`                                           | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/Math/cos`                                             | 8     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                          | #434  |
| `test/built-ins/Math/cos`                                             | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/Math/cosh`                                            | 4     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                          | #434  |
| `test/built-ins/Math/cosh`                                            | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/Math/exp`                                             | 8     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                          | #434  |
| `test/built-ins/Math/exp`                                             | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/Math/expm1`                                           | 4     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                          | #434  |
| `test/built-ins/Math/expm1`                                           | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/Math/f16round`                                        | 4     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                          | #434  |
| `test/built-ins/Math/f16round`                                        | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/Math/hypot`                                           | 11    | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                          | #434  |
| `test/built-ins/Math/hypot`                                           | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/Math/imul`                                            | 4     | builtin      | `Math.clz32` and `Math.imul` need ToInt32 and ToUint32                                                              | #440  |
| `test/built-ins/Math/imul`                                            | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/Math/log`                                             | 8     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                          | #434  |
| `test/built-ins/Math/log`                                             | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/Math/log10`                                           | 4     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                          | #434  |
| `test/built-ins/Math/log10`                                           | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/Math/log1p`                                           | 4     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                          | #434  |
| `test/built-ins/Math/log1p`                                           | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/Math/log2`                                            | 4     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                          | #434  |
| `test/built-ins/Math/log2`                                            | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/Math/random`                                          | 4     | builtin      | `Math.random` is absent                                                                                             | #445  |
| `test/built-ins/Math/random`                                          | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/Math/sin`                                             | 7     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                          | #434  |
| `test/built-ins/Math/sin`                                             | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/Math/sinh`                                            | 4     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                          | #434  |
| `test/built-ins/Math/sinh`                                            | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/Math/sumPrecise`                                      | 7     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                          | #434  |
| `test/built-ins/Math/sumPrecise`                                      | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/Math/tan`                                             | 8     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                          | #434  |
| `test/built-ins/Math/tan`                                             | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/Math/tanh`                                            | 4     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                          | #434  |
| `test/built-ins/Math/tanh`                                            | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/NativeErrors`                                         | 2     | builtin      | the rest of `Array.prototype` is absent, `toString` among it                                                        | #390  |
| `test/built-ins/NativeErrors/EvalError`                               | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/NativeErrors/EvalError`                               | 1     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/NativeErrors/RangeError`                              | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/NativeErrors/RangeError`                              | 1     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/NativeErrors/ReferenceError`                          | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/NativeErrors/ReferenceError`                          | 1     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/NativeErrors/SyntaxError`                             | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/NativeErrors/SyntaxError`                             | 1     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/NativeErrors/TypeError`                               | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/NativeErrors/TypeError`                               | 1     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/NativeErrors/URIError`                                | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/NativeErrors/URIError`                                | 1     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/Number`                                               | 2     | bug          | a numeric literal that overflows to `Infinity` reaches Lean as JSON `null`                                          | #460  |
| `test/built-ins/Number`                                               | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/Number`                                               | 1     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/Number/NEGATIVE_INFINITY`                             | 2     | builtin      | the global `isNaN` and `isFinite` are not in the realm                                                              | #441  |
| `test/built-ins/Number/POSITIVE_INFINITY`                             | 2     | builtin      | the global `isNaN` and `isFinite` are not in the realm                                                              | #441  |
| `test/built-ins/Number/prototype/toExponential`                       | 1     | builtin      | the rest of `Array.prototype` is absent, `toString` among it                                                        | #390  |
| `test/built-ins/Number/prototype/toPrecision`                         | 1     | builtin      | the rest of `Array.prototype` is absent, `toString` among it                                                        | #390  |
| `test/built-ins/Number/prototype/toString`                            | 1     | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Number/prototype/valueOf`                             | 1     | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Object`                                               | 2     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/Object`                                               | 1     | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Object`                                               | 1     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/Object`                                               | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/Object`                                               | 1     | builtin      | the rest of `Array.prototype` is absent, `toString` among it                                                        | #390  |
| `test/built-ins/Object/assign`                                        | 4     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/Object/create`                                        | 12    | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Object/create`                                        | 11    | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/built-ins/Object/create`                                        | 10    | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/Object/create`                                        | 2     | builtin      | the rest of `Array.prototype` is absent, `toString` among it                                                        | #390  |
| `test/built-ins/Object/defineProperties`                              | 12    | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Object/defineProperties`                              | 12    | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/built-ins/Object/defineProperties`                              | 10    | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/Object/defineProperties`                              | 1     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/Object/defineProperty`                                | 26    | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Object/defineProperty`                                | 19    | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/built-ins/Object/defineProperty`                                | 11    | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/Object/defineProperty`                                | 10    | builtin      | the rest of `Array.prototype` is absent, `toString` among it                                                        | #390  |
| `test/built-ins/Object/entries`                                       | 3     | builtin      | the rest of `Array.prototype` is absent, `toString` among it                                                        | #390  |
| `test/built-ins/Object/entries`                                       | 1     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/Object/freeze`                                        | 4     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/Object/freeze`                                        | 1     | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Object/freeze`                                        | 1     | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/built-ins/Object/getOwnPropertyDescriptor`                      | 47    | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Object/getOwnPropertyDescriptor`                      | 20    | builtin      | the rest of `Array.prototype` is absent, `toString` among it                                                        | #390  |
| `test/built-ins/Object/getOwnPropertyDescriptor`                      | 11    | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/Object/getOwnPropertyDescriptor`                      | 11    | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/built-ins/Object/getOwnPropertyDescriptor`                      | 9     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                          | #434  |
| `test/built-ins/Object/getOwnPropertyDescriptor`                      | 1     | builtin      | `Math.random` is absent                                                                                             | #445  |
| `test/built-ins/Object/getOwnPropertyDescriptors`                     | 3     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/Object/getOwnPropertyDescriptors`                     | 1     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/Object/getOwnPropertyNames`                           | 4     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/Object/getOwnPropertyNames`                           | 1     | builtin      | the rest of `Array.prototype` is absent, `toString` among it                                                        | #390  |
| `test/built-ins/Object/getOwnPropertyNames`                           | 1     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/Object/getOwnPropertySymbols`                         | 4     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/Object/getPrototypeOf`                                | 2     | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Object/getPrototypeOf`                                | 2     | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/built-ins/Object/getPrototypeOf`                                | 1     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/Object/internals/DefineOwnProperty`                   | 3     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/Object/isExtensible`                                  | 2     | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Object/isExtensible`                                  | 2     | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/built-ins/Object/isExtensible`                                  | 2     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/Object/isFrozen`                                      | 2     | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Object/isFrozen`                                      | 2     | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/built-ins/Object/isFrozen`                                      | 1     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/Object/isFrozen`                                      | 1     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/Object/isSealed`                                      | 2     | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Object/isSealed`                                      | 2     | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/built-ins/Object/isSealed`                                      | 1     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/Object/isSealed`                                      | 1     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/Object/keys`                                          | 5     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/Object/keys`                                          | 1     | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Object/preventExtensions`                             | 2     | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Object/preventExtensions`                             | 2     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/Object/preventExtensions`                             | 2     | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/built-ins/Object/prototype`                                     | 4     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/Object/prototype/__defineGetter__`                    | 10    | builtin      | the Annex B accessors on `Object.prototype` come with the global object                                             | #487  |
| `test/built-ins/Object/prototype/__defineGetter__`                    | 1     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/Object/prototype/__defineSetter__`                    | 10    | builtin      | the Annex B accessors on `Object.prototype` come with the global object                                             | #487  |
| `test/built-ins/Object/prototype/__defineSetter__`                    | 1     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/Object/prototype/__lookupGetter__`                    | 12    | builtin      | the Annex B accessors on `Object.prototype` come with the global object                                             | #487  |
| `test/built-ins/Object/prototype/__lookupGetter__`                    | 4     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/Object/prototype/__lookupSetter__`                    | 12    | builtin      | the Annex B accessors on `Object.prototype` come with the global object                                             | #487  |
| `test/built-ins/Object/prototype/__lookupSetter__`                    | 4     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/Object/prototype/__proto__`                           | 13    | builtin      | the Annex B accessors on `Object.prototype` come with the global object                                             | #487  |
| `test/built-ins/Object/prototype/__proto__`                           | 2     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/Object/prototype/hasOwnProperty`                      | 1     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/Object/prototype/isPrototypeOf`                       | 1     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/Object/prototype/toString`                            | 5     | out-of-scope | the keyed collections and promises are excluded by the epic                                                         | #376  |
| `test/built-ins/Object/prototype/toString`                            | 3     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/Object/prototype/toString`                            | 2     | out-of-scope | BigInt is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Object/prototype/toString`                            | 2     | out-of-scope | the `Iterator` constructor and its helpers are excluded by the epic                                                 | #376  |
| `test/built-ins/Object/prototype/toString`                            | 1     | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Object/seal`                                          | 14    | out-of-scope | typed arrays and their buffers are excluded by the epic                                                             | #376  |
| `test/built-ins/Object/seal`                                          | 7     | out-of-scope | the keyed collections and promises are excluded by the epic                                                         | #376  |
| `test/built-ins/Object/seal`                                          | 5     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/Object/seal`                                          | 3     | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Object/seal`                                          | 3     | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/built-ins/Object/seal`                                          | 1     | out-of-scope | the `Function` constructor is excluded by the epic                                                                  | #376  |
| `test/built-ins/Object/setPrototypeOf`                                | 1     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/Object/values`                                        | 2     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/String`                                               | 2     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/String`                                               | 2     | builtin      | the rest of `Array.prototype` is absent, `toString` among it                                                        | #390  |
| `test/built-ins/String`                                               | 2     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/String`                                               | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/String/prototype/charAt`                              | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/String/prototype/charCodeAt`                          | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/String/prototype/codePointAt`                         | 1     | builtin      | the rest of `Array.prototype` is absent, `toString` among it                                                        | #390  |
| `test/built-ins/String/prototype/indexOf`                             | 4     | builtin      | the rest of `Array.prototype` is absent, `toString` among it                                                        | #390  |
| `test/built-ins/String/prototype/indexOf`                             | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/String/prototype/indexOf`                             | 1     | bug          | a non-callable `@@toPrimitive` handler falls back to OrdinaryToPrimitive instead of throwing                        | #516  |
| `test/built-ins/String/prototype/lastIndexOf`                         | 1     | builtin      | the rest of `Array.prototype` is absent, `toString` among it                                                        | #390  |
| `test/built-ins/String/prototype/localeCompare`                       | 1     | builtin      | Lean has no Unicode character database: case mapping is ASCII-only and `normalize` answers its input                | #518  |
| `test/built-ins/String/prototype/match`                               | 27    | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/built-ins/String/prototype/match`                               | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/String/prototype/matchAll`                            | 12    | out-of-scope | `matchAll` needs `RegExp`, which is excluded by the epic                                                            | #376  |
| `test/built-ins/String/prototype/normalize`                           | 2     | builtin      | Lean has no Unicode character database: case mapping is ASCII-only and `normalize` answers its input                | #518  |
| `test/built-ins/String/prototype/normalize`                           | 1     | builtin      | the rest of `Array.prototype` is absent, `toString` among it                                                        | #390  |
| `test/built-ins/String/prototype/replace`                             | 2     | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/built-ins/String/prototype/replace`                             | 2     | builtin      | the `@@split`, `@@replace`, and `@@match` protocol lookups are absent from the `String` methods                     | #523  |
| `test/built-ins/String/prototype/replaceAll`                          | 5     | builtin      | the `@@split`, `@@replace`, and `@@match` protocol lookups are absent from the `String` methods                     | #523  |
| `test/built-ins/String/prototype/search`                              | 31    | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/built-ins/String/prototype/search`                              | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/String/prototype/split`                               | 13    | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/built-ins/String/prototype/split`                               | 3     | builtin      | the `@@split`, `@@replace`, and `@@match` protocol lookups are absent from the `String` methods                     | #523  |
| `test/built-ins/String/prototype/split`                               | 1     | builtin      | the rest of `Array.prototype` is absent, `toString` among it                                                        | #390  |
| `test/built-ins/String/prototype/split`                               | 1     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/String/prototype/substring`                           | 4     | builtin      | the rest of `Array.prototype` is absent, `toString` among it                                                        | #390  |
| `test/built-ins/String/prototype/toLocaleLowerCase`                   | 4     | builtin      | Lean has no Unicode character database: case mapping is ASCII-only and `normalize` answers its input                | #518  |
| `test/built-ins/String/prototype/toLocaleLowerCase`                   | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/String/prototype/toLocaleLowerCase`                   | 1     | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/built-ins/String/prototype/toLocaleUpperCase`                   | 2     | builtin      | Lean has no Unicode character database: case mapping is ASCII-only and `normalize` answers its input                | #518  |
| `test/built-ins/String/prototype/toLocaleUpperCase`                   | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/String/prototype/toLocaleUpperCase`                   | 1     | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/built-ins/String/prototype/toLowerCase`                         | 4     | builtin      | Lean has no Unicode character database: case mapping is ASCII-only and `normalize` answers its input                | #518  |
| `test/built-ins/String/prototype/toLowerCase`                         | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/String/prototype/toLowerCase`                         | 1     | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/built-ins/String/prototype/toUpperCase`                         | 2     | builtin      | Lean has no Unicode character database: case mapping is ASCII-only and `normalize` answers its input                | #518  |
| `test/built-ins/String/prototype/toUpperCase`                         | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/String/prototype/toUpperCase`                         | 1     | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/built-ins/String/prototype/trim`                                | 1     | builtin      | the rest of `Array.prototype` is absent, `toString` among it                                                        | #390  |
| `test/built-ins/SuppressedError`                                      | 13    | out-of-scope | explicit resource management is excluded by the epic                                                                | #376  |
| `test/built-ins/SuppressedError`                                      | 1     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/SuppressedError/prototype`                            | 6     | out-of-scope | explicit resource management is excluded by the epic                                                                | #376  |
| `test/built-ins/Symbol`                                               | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/Symbol`                                               | 1     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/Symbol/asyncDispose`                                  | 2     | out-of-scope | explicit resource management is excluded by the epic                                                                | #376  |
| `test/built-ins/Symbol/dispose`                                       | 2     | out-of-scope | explicit resource management is excluded by the epic                                                                | #376  |
| `test/built-ins/Symbol/prototype/description`                         | 1     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/Symbol/species`                                       | 1     | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/built-ins/Symbol/species`                                       | 1     | builtin      | `Symbol.species` is absent from the constructors that have one                                                      | #390  |
| `test/built-ins/ThrowTypeError`                                       | 2     | bug          | `%ThrowTypeError%` is extensible where 10.2.4.1 makes it frozen                                                     | #512  |
| `test/built-ins/ThrowTypeError`                                       | 1     | builtin      | the rest of `Array.prototype` is absent, `toString` among it                                                        | #390  |
| `test/built-ins/ThrowTypeError`                                       | 1     | builtin      | `Function.prototype.caller` and `arguments` are the `%ThrowTypeError%` accessors                                    | #487  |
| `test/built-ins/parseFloat`                                           | 2     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/parseInt`                                             | 2     | builtin      | there is no global object                                                                                           | #487  |
| `test/harness`                                                        | 7     | builtin      | the rest of `Array.prototype` is absent, `toString` among it                                                        | #390  |
| `test/harness`                                                        | 8     | builtin      | there is no global object                                                                                           | #487  |
| `test/harness`                                                        | 4     | out-of-scope | typed arrays and their buffers are excluded by the epic                                                             | #376  |
| `test/harness`                                                        | 1     | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/language/arguments-object`                                      | 2     | out-of-scope | an early-error test that reaches for `eval`                                                                         | #376  |
| `test/language/expressions/addition`                                  | 5     | builtin      | the global `isNaN` and `isFinite` are not in the realm                                                              | #441  |
| `test/language/expressions/addition`                                  | 1     | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/language/expressions/addition`                                  | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/expressions/arrow-function`                            | 1     | builtin      | the rest of `Array.prototype` is absent, `toString` among it                                                        | #390  |
| `test/language/expressions/arrow-function`                            | 1     | builtin      | `Function.prototype.caller` and `arguments` are the `%ThrowTypeError%` accessors                                    | #487  |
| `test/language/expressions/arrow-function/arrow`                      | 4     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/expressions/assignment`                                | 1     | builtin      | the rest of `Array.prototype` is absent, `toString` among it                                                        | #390  |
| `test/language/expressions/assignment`                                | 1     | protocol     | the bridge drops the parentheses that keep NamedEvaluation from naming a function                                   | #499  |
| `test/language/expressions/assignment/destructuring`                  | 2     | builtin      | the rest of `Array.prototype` is absent, `map` among it                                                             | #390  |
| `test/language/expressions/call`                                      | 8     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/expressions/call`                                      | 1     | out-of-scope | an early-error test that reaches for `eval`                                                                         | #376  |
| `test/language/expressions/class`                                     | 1     | builtin      | `Function.prototype.caller` and `arguments` are the `%ThrowTypeError%` accessors                                    | #487  |
| `test/language/expressions/class/elements`                            | 24    | out-of-scope | an early-error test that reaches for `eval`                                                                         | #376  |
| `test/language/expressions/class/elements`                            | 19    | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/expressions/class/elements`                            | 2     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/language/expressions/class/elements/syntax/valid`               | 1     | bug          | a static method named `constructor` is emitted as the class constructor                                             | #496  |
| `test/language/expressions/class/subclass-builtins`                   | 14    | out-of-scope | typed arrays and their buffers are excluded by the epic                                                             | #376  |
| `test/language/expressions/class/subclass-builtins`                   | 6     | out-of-scope | the keyed collections and promises are excluded by the epic                                                         | #376  |
| `test/language/expressions/class/subclass-builtins`                   | 1     | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/language/expressions/class/subclass-builtins`                   | 1     | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/language/expressions/class/subclass-builtins`                   | 1     | out-of-scope | the `Function` constructor is excluded by the epic                                                                  | #376  |
| `test/language/expressions/conditional`                               | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/expressions/division`                                  | 11    | builtin      | the global `isNaN` and `isFinite` are not in the realm                                                              | #441  |
| `test/language/expressions/division`                                  | 2     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/expressions/division`                                  | 1     | bug          | the left operand is not converted fully before the right one                                                        | #436  |
| `test/language/expressions/function`                                  | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/expressions/greater-than`                              | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/expressions/greater-than-or-equal`                     | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/expressions/less-than`                                 | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/expressions/less-than-or-equal`                        | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/expressions/logical-and`                               | 2     | builtin      | the global `isNaN` and `isFinite` are not in the realm                                                              | #441  |
| `test/language/expressions/logical-and`                               | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/expressions/logical-not`                               | 2     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/expressions/logical-or`                                | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/expressions/modulus`                                   | 14    | builtin      | the global `isNaN` and `isFinite` are not in the realm                                                              | #441  |
| `test/language/expressions/modulus`                                   | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/expressions/modulus`                                   | 1     | bug          | the left operand is not converted fully before the right one                                                        | #436  |
| `test/language/expressions/multiplication`                            | 10    | builtin      | the global `isNaN` and `isFinite` are not in the realm                                                              | #441  |
| `test/language/expressions/multiplication`                            | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/expressions/multiplication`                            | 1     | bug          | the left operand is not converted fully before the right one                                                        | #436  |
| `test/language/expressions/object`                                    | 8     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/expressions/object`                                    | 3     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/language/expressions/object`                                    | 1     | builtin      | the rest of `Array.prototype` is absent, `toString` among it                                                        | #390  |
| `test/language/expressions/object/dstr`                               | 3     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/language/expressions/strict-does-not-equals`                    | 2     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/expressions/strict-equals`                             | 2     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/expressions/subtraction`                               | 9     | builtin      | the global `isNaN` and `isFinite` are not in the realm                                                              | #441  |
| `test/language/expressions/subtraction`                               | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/expressions/subtraction`                               | 1     | bug          | the left operand is not converted fully before the right one                                                        | #436  |
| `test/language/expressions/tagged-template`                           | 3     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/expressions/template-literal`                          | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/expressions/unary-minus`                               | 3     | builtin      | the global `isNaN` and `isFinite` are not in the realm                                                              | #441  |
| `test/language/expressions/unary-minus`                               | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/expressions/unary-plus`                                | 6     | builtin      | the global `isNaN` and `isFinite` are not in the realm                                                              | #441  |
| `test/language/expressions/unary-plus`                                | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/function-code`                                         | 6     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/statements/break`                                      | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/statements/class`                                      | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/statements/class`                                      | 1     | builtin      | `Function.prototype.caller` and `arguments` are the `%ThrowTypeError%` accessors                                    | #487  |
| `test/language/statements/class/definition`                           | 1     | builtin      | `Function.prototype.caller` and `arguments` are the `%ThrowTypeError%` accessors                                    | #487  |
| `test/language/statements/class/elements`                             | 32    | out-of-scope | an early-error test that reaches for `eval`                                                                         | #376  |
| `test/language/statements/class/elements`                             | 22    | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/statements/class/elements`                             | 4     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/language/statements/class/elements`                             | 1     | builtin      | there is no global object                                                                                           | #487  |
| `test/language/statements/class/elements/syntax/valid`                | 1     | bug          | a static method named `constructor` is emitted as the class constructor                                             | #496  |
| `test/language/statements/class/strict-mode`                          | 1     | builtin      | `Function.prototype.caller` and `arguments` are the `%ThrowTypeError%` accessors                                    | #487  |
| `test/language/statements/class/subclass`                             | 1     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/language/statements/class/subclass`                             | 1     | out-of-scope | typed arrays and their buffers are excluded by the epic                                                             | #376  |
| `test/language/statements/class/subclass-builtins`                    | 14    | out-of-scope | typed arrays and their buffers are excluded by the epic                                                             | #376  |
| `test/language/statements/class/subclass-builtins`                    | 6     | out-of-scope | the keyed collections and promises are excluded by the epic                                                         | #376  |
| `test/language/statements/class/subclass-builtins`                    | 1     | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/language/statements/class/subclass-builtins`                    | 1     | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/language/statements/class/subclass-builtins`                    | 1     | out-of-scope | the `Function` constructor is excluded by the epic                                                                  | #376  |
| `test/language/statements/class/subclass/builtin-objects/ArrayBuffer` | 2     | out-of-scope | typed arrays and their buffers are excluded by the epic                                                             | #376  |
| `test/language/statements/class/subclass/builtin-objects/DataView`    | 2     | out-of-scope | typed arrays and their buffers are excluded by the epic                                                             | #376  |
| `test/language/statements/class/subclass/builtin-objects/Date`        | 2     | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/language/statements/class/subclass/builtin-objects/Function`    | 4     | out-of-scope | the `Function` constructor is excluded by the epic                                                                  | #376  |
| `test/language/statements/class/subclass/builtin-objects/Map`         | 2     | out-of-scope | the keyed collections and promises are excluded by the epic                                                         | #376  |
| `test/language/statements/class/subclass/builtin-objects/Promise`     | 2     | out-of-scope | the keyed collections and promises are excluded by the epic                                                         | #376  |
| `test/language/statements/class/subclass/builtin-objects/Proxy`       | 1     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/language/statements/class/subclass/builtin-objects/RegExp`      | 3     | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/language/statements/class/subclass/builtin-objects/Set`         | 2     | out-of-scope | the keyed collections and promises are excluded by the epic                                                         | #376  |
| `test/language/statements/class/subclass/builtin-objects/TypedArray`  | 2     | out-of-scope | typed arrays and their buffers are excluded by the epic                                                             | #376  |
| `test/language/statements/class/subclass/builtin-objects/WeakMap`     | 2     | out-of-scope | the keyed collections and promises are excluded by the epic                                                         | #376  |
| `test/language/statements/class/subclass/builtin-objects/WeakSet`     | 2     | out-of-scope | the keyed collections and promises are excluded by the epic                                                         | #376  |
| `test/language/statements/const`                                      | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/statements/continue`                                   | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/statements/do-while`                                   | 6     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/statements/empty`                                      | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/statements/expression`                                 | 2     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/statements/for`                                        | 7     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/statements/for-of`                                     | 18    | out-of-scope | typed arrays and their buffers are excluded by the epic                                                             | #376  |
| `test/language/statements/for-of`                                     | 10    | out-of-scope | the keyed collections are excluded by the epic                                                                      | #376  |
| `test/language/statements/for-of`                                     | 6     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/statements/for-of`                                     | 3     | builtin      | the rest of `Array.prototype` is absent, `pop` among it                                                             | #390  |
| `test/language/statements/for-of`                                     | 2     | out-of-scope | explicit resource management (`using`) is excluded by the epic                                                      | #376  |
| `test/language/statements/for-of`                                     | 1     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/language/statements/function`                                   | 4     | builtin      | `Function.prototype.caller` and `arguments` are the `%ThrowTypeError%` accessors                                    | #487  |
| `test/language/statements/function`                                   | 3     | out-of-scope | an early-error test that reaches for `eval`                                                                         | #376  |
| `test/language/statements/function`                                   | 2     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/statements/function`                                   | 2     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                          | #434  |
| `test/language/statements/function`                                   | 1     | out-of-scope | the `Function` constructor is excluded by the epic                                                                  | #376  |
| `test/language/statements/if`                                         | 9     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/statements/labeled`                                    | 2     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/statements/let`                                        | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/statements/return`                                     | 1     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                          | #434  |
| `test/language/statements/switch`                                     | 21    | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/statements/switch`                                     | 1     | builtin      | the global `isNaN` and `isFinite` are not in the realm                                                              | #441  |
| `test/language/statements/throw`                                      | 1     | builtin      | the rest of `Array.prototype` is absent                                                                             | #390  |
| `test/language/statements/try`                                        | 12    | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/statements/try`                                        | 2     | out-of-scope | an early-error test that reaches for `eval`                                                                         | #376  |
| `test/language/statements/try`                                        | 1     | builtin      | the rest of `Array.prototype` is absent                                                                             | #390  |
| `test/language/statements/variable`                                   | 7     | out-of-scope | an early-error test that reaches for `eval`                                                                         | #376  |
| `test/language/statements/variable`                                   | 6     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/statements/variable`                                   | 2     | builtin      | there is no global object                                                                                           | #487  |
| `test/language/statements/while`                                      | 7     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |

## The unsupported column

A test in the `unsupported` column is not a failure: the decoder refused
the document by name before the evaluator saw it, which is the verdict the
runner should file for a program outside the fragment. The kinds, and who
owns them:

| kind                                                                                                                                                     | owner                                                                         |
| -------------------------------------------------------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------- |
| `BinaryExpression ,`, the shifts and the bitwise forms, `AssignmentExpression >>>=`                                                                      | #376 — operators the epic does not model                                      |
| `BigIntLiteral`                                                                                                                                          | #376 — BigInt is out of scope                                                 |
| `FunctionExpression generator`, `FunctionDeclaration generator`, `FunctionExpression async`, `ArrowFunctionExpression async`, `RegularExpressionLiteral` | #376 — generators, async, and regular expressions are out of scope            |
| `ComputedPropertyName`                                                                                                                                   | #384 — a computed _class_ key; every object-literal one is in the slice       |
| `MethodDefinition private`, `ClassStaticBlockDeclaration`, `AccessorKeyword`, `AssignmentExpression super target`                                        | #473 — private methods and accessors, static blocks, and `super.x = v`        |
| `MethodDefinition generator`, `MethodDefinition async`, `Property generator`, `Property async`, `Decorator`                                              | #376 — generators, async, and decorators are out of scope                     |
| `MethodDefinition numeric key`                                                                                                                           | #384 — a numeric _class_ key; a literal's is a computed key in the slice      |
| `Parameter`                                                                                                                                              | #376 — a TypeScript parameter property, which declares and assigns a field    |
| `Function constructor`                                                                                                                                   | #376 — the constructor's semantics are `eval` by another spelling             |
| `AssignmentExpression target`, `LogicalExpression ??`, `BinaryExpression ==`, `BinaryExpression !=`                                                      | #376 — loose equality, nullish coalescing, and targets with no reference form |
| `MetaProperty`                                                                                                                                           | #486 — `new.target` as syntax                                                 |
| `WithStatement`                                                                                                                                          | #376 — `with` is not strict-mode syntax and the epic is strict mode only      |
| `$262.createRealm`, `$262.detachArrayBuffer`                                                                                                             | #376 — the host hooks are refused by name                                     |

The counts, from the same run. They are not tested — only the table above
is — but they are what names the next slice to land.

```
  MethodDefinition generator  1436
  MethodDefinition private  881
  FunctionExpression generator  540
  ComputedPropertyName  331
  FunctionDeclaration generator  300
  BinaryExpression ,  266
  MethodDefinition async  217
  Property generator  197
  Function constructor  192
  RegularExpressionLiteral  184
  BigIntLiteral  109
  $262.createRealm  58
  Property async  50
  BinaryExpression ==  34
  ClassStaticBlockDeclaration  34
  BinaryExpression !=  30
  MethodDefinition numeric key  29
  Decorator  12
  AssignmentExpression super target  7
  FunctionExpression async  6
  MetaProperty  6
  ArrowFunctionExpression async  4
  BinaryExpression &  4
  FunctionDeclaration async  4
  PropertyDefinition numeric key  4
  AssignmentExpression >>>=  3
  $262.detachArrayBuffer  2
  AccessorKeyword  2
  LogicalExpression ??  2
  AssignmentExpression &&=  1
  AssignmentExpression ??=  1
  AssignmentExpression |=  1
  AssignmentExpression ||=  1
  BinaryExpression >>  1
  BinaryExpression >>>  1
  WithStatement  1
```
