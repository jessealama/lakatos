# The failure list for the PR-gated slice

Written 2026-09-14 against test262 at `419d3e0a2273ba01a3bfcbec423f2801425b8e93`
(`tarski/test262/pin.json`), from one run of

```bash
node ../dist/tarski/frontend/src/test262/cli.js --slice-file test262/slice.txt
```

Every failing test in `tarski/test262/slice.txt` is classified here — the
harness, the 27 language directories the thales emitter maps (#383), the
three built-ins directories #382 added, the two global parsers #388
added, the two class directories #384 added, the fifteen declaration
instantiation, jump, and `arguments` directories #393 added, and the two
`Object` and `Function` directories #389 added — and
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
#382, on #388, on #384, on #393, or on #389: no failure in the slice is
caused by the statements and operators #383 added, none is a `Math`,
`Number`, or `Boolean` member answering the wrong number, **not one row
is a conversion between a Number and a String answering the wrong
thing**, **none is a class evaluating wrongly**, **none is declaration
instantiation, a parameter's dead zone, a default's scope, `arguments`, a
`switch`, a label, a jump, or `do`/`while` answering wrongly**, and
**not one row is a property descriptor, an own-key order, an
enumerability, a `delete`, an `in`, a `for`-`in`, or an `Object` or
`Function` member answering the wrong thing**.

The 1,447 failures below, by owner: 667 what #376 excludes (`eval`,
`Date`, `RegExp`, `JSON`, `Proxy`, `Reflect`, typed arrays, the keyed
collections, the `Function` constructor's semantics, and
`nativeFunctionMatcher.js`, which matches source text with a regular
expression), 189 the String wrapper (#391), 168 the global object (#487),
150 the transcendental `Math` members (#434), 118 `Symbol` (#392), 57 the
global `isNaN` and `isFinite` (#441), 51 the rest of `Array.prototype`
(#390), 24 iterators (#394), 13 `Math.clz32`/`imul` (#440), 5
`Math.random` (#445), and 5 the three filed defects (#460, #496, #499).

**The two `Object` and `Function` directories are 2,761 pass and 725
fail**, against 197 and 2,110 before this slice. Their 725 are the same
list: 320 `eval`, `Date`, `RegExp`, `JSON`, `Proxy`, `Reflect`, and typed
arrays (#376); 142 the global object, whose `this` at top level a third
of `Object`'s older tests reach for (#487); 111 the String wrapper
(#391); 80 `Symbol` (#392); 40 the rest of `Array.prototype`, which the
order tests reach through `map` and `indexOf` (#390); 22 iterators
(#394); and 10 `Math` members the library does not model, read through
`getOwnPropertyDescriptor` (#434, #445). None is a filed defect.
**The `propertyHelper.js`-based tests run and pass**: `Math/abs` is 8 and
0, and `length.js`, `name.js`, and `prop-desc.js` under it are three of
them.

`test/harness` is 49 pass and 23 fail, against 27 and 18: its
`verifyProperty` tests reach the property protocol now, and what is left
of them is `Symbol`, the global object, and `Array.prototype`.

**Two class evaluations were wrong** when the class directories were
first scored and are not wrong now. `super[super()]` read the key before
the `this` binding, where 13.3.7.2 reads the binding first, so the
derived constructor's dead zone was not reached; that is `superBase` in
`Tarski/Eval.lean`, and `ClassesTest` pins it. The other was a bridge
limit rather than an evaluator one: tsc refuses `a?.b.#c`, which is valid
JavaScript, so four tests under `class/elements` are **harness errors**
rather than failures and appear in no row below. #472 owns them.

**Three defects this slice found are filed rather than fixed.**
`estree.ts` gives a `static constructor() {}` the ESTree kind of a class
constructor and drops its `static` flag (#496), which two
`grammar-static-ctor-meth-valid.js` tests reach now that a function has a
`hasOwnProperty` to call; and the bridge drops the parentheses that keep
NamedEvaluation from naming `(fn) = function () {}` (#499). The third is
older: a numeric literal that overflows to `Infinity` reaches Lean as
JSON `null` (#460).

One divergence found while classifying is not the proximate cause of any
row and so has none: `applyCoercing` runs ToPrimitive on both operands
before ToNumber on either, where 13.15.3 converts the left operand fully
first for every operator but `+`. It is unobservable without a Symbol or a
BigInt operand, and it is filed as #436. The five `order-of-evaluation`
tests that pin it fail today for want of `Symbol`, so they are classified
against #392.

## The table

| directory                                                             | fails | class        | why                                                                               | owner |
| --------------------------------------------------------------------- | ----- | ------------ | --------------------------------------------------------------------------------- | ----- |
| `test/built-ins/Boolean`                                              | 1     | out-of-scope | `eval` is excluded by the epic                                                    | #376  |
| `test/built-ins/Boolean`                                              | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                      | #376  |
| `test/built-ins/Boolean`                                              | 1     | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/built-ins/Boolean`                                              | 1     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/built-ins/Boolean`                                              | 1     | builtin      | there is no global object                                                         | #487  |
| `test/built-ins/Boolean/prototype/toString`                           | 1     | out-of-scope | `Date` is excluded by the epic                                                    | #376  |
| `test/built-ins/Boolean/prototype/valueOf`                            | 1     | builtin      | there is no global object                                                         | #487  |
| `test/built-ins/Function`                                             | 19    | builtin      | `Function.prototype.caller` and `arguments` are the `%ThrowTypeError%` accessors  | #487  |
| `test/built-ins/Function`                                             | 5     | out-of-scope | the `Function` constructor is excluded by the epic                                | #376  |
| `test/built-ins/Function`                                             | 5     | builtin      | there is no global object                                                         | #487  |
| `test/built-ins/Function`                                             | 2     | out-of-scope | `eval` is excluded by the epic                                                    | #376  |
| `test/built-ins/Function`                                             | 1     | builtin      | the rest of `Array.prototype` is absent, `toString` among it                      | #390  |
| `test/built-ins/Function/internals/Construct`                         | 1     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                    | #376  |
| `test/built-ins/Function/prototype`                                   | 1     | builtin      | the rest of `Array.prototype` is absent, `toString` among it                      | #390  |
| `test/built-ins/Function/prototype/Symbol.hasInstance`                | 9     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/built-ins/Function/prototype/Symbol.hasInstance`                | 1     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                    | #376  |
| `test/built-ins/Function/prototype/apply`                             | 1     | out-of-scope | `eval` is excluded by the epic                                                    | #376  |
| `test/built-ins/Function/prototype/apply`                             | 1     | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/built-ins/Function/prototype/apply`                             | 1     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/built-ins/Function/prototype/bind`                              | 7     | builtin      | `Function.prototype.caller` and `arguments` are the `%ThrowTypeError%` accessors  | #487  |
| `test/built-ins/Function/prototype/bind`                              | 2     | out-of-scope | `Date` is excluded by the epic                                                    | #376  |
| `test/built-ins/Function/prototype/bind`                              | 2     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/built-ins/Function/prototype/bind`                              | 1     | out-of-scope | `JSON` is excluded by the epic                                                    | #376  |
| `test/built-ins/Function/prototype/call`                              | 1     | out-of-scope | `eval` is excluded by the epic                                                    | #376  |
| `test/built-ins/Function/prototype/call`                              | 1     | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/built-ins/Function/prototype/caller-arguments`                  | 1     | builtin      | `Function.prototype.caller` and `arguments` are the `%ThrowTypeError%` accessors  | #487  |
| `test/built-ins/Function/prototype/toString`                          | 2     | out-of-scope | `nativeFunctionMatcher.js` matches source text with a regular expression          | #376  |
| `test/built-ins/Function/prototype/toString`                          | 1     | out-of-scope | the bridge keeps no source text, and the matcher is a regular expression          | #376  |
| `test/built-ins/Math`                                                 | 1     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/built-ins/Math`                                                 | 1     | builtin      | there is no global object                                                         | #487  |
| `test/built-ins/Math/acos`                                            | 7     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent        | #434  |
| `test/built-ins/Math/acos`                                            | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                      | #376  |
| `test/built-ins/Math/acosh`                                           | 6     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent        | #434  |
| `test/built-ins/Math/acosh`                                           | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                      | #376  |
| `test/built-ins/Math/asin`                                            | 8     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent        | #434  |
| `test/built-ins/Math/asin`                                            | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                      | #376  |
| `test/built-ins/Math/asinh`                                           | 4     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent        | #434  |
| `test/built-ins/Math/asinh`                                           | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                      | #376  |
| `test/built-ins/Math/atan`                                            | 6     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent        | #434  |
| `test/built-ins/Math/atan`                                            | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                      | #376  |
| `test/built-ins/Math/atan2`                                           | 10    | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent        | #434  |
| `test/built-ins/Math/atan2`                                           | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                      | #376  |
| `test/built-ins/Math/atanh`                                           | 4     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent        | #434  |
| `test/built-ins/Math/atanh`                                           | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                      | #376  |
| `test/built-ins/Math/cbrt`                                            | 4     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent        | #434  |
| `test/built-ins/Math/cbrt`                                            | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                      | #376  |
| `test/built-ins/Math/clz32`                                           | 9     | builtin      | `Math.clz32` and `Math.imul` need ToInt32 and ToUint32                            | #440  |
| `test/built-ins/Math/clz32`                                           | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                      | #376  |
| `test/built-ins/Math/cos`                                             | 8     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent        | #434  |
| `test/built-ins/Math/cos`                                             | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                      | #376  |
| `test/built-ins/Math/cosh`                                            | 4     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent        | #434  |
| `test/built-ins/Math/cosh`                                            | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                      | #376  |
| `test/built-ins/Math/exp`                                             | 8     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent        | #434  |
| `test/built-ins/Math/exp`                                             | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                      | #376  |
| `test/built-ins/Math/expm1`                                           | 4     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent        | #434  |
| `test/built-ins/Math/expm1`                                           | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                      | #376  |
| `test/built-ins/Math/f16round`                                        | 4     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent        | #434  |
| `test/built-ins/Math/f16round`                                        | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                      | #376  |
| `test/built-ins/Math/hypot`                                           | 11    | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent        | #434  |
| `test/built-ins/Math/hypot`                                           | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                      | #376  |
| `test/built-ins/Math/imul`                                            | 4     | builtin      | `Math.clz32` and `Math.imul` need ToInt32 and ToUint32                            | #440  |
| `test/built-ins/Math/imul`                                            | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                      | #376  |
| `test/built-ins/Math/log`                                             | 8     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent        | #434  |
| `test/built-ins/Math/log`                                             | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                      | #376  |
| `test/built-ins/Math/log10`                                           | 4     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent        | #434  |
| `test/built-ins/Math/log10`                                           | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                      | #376  |
| `test/built-ins/Math/log1p`                                           | 4     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent        | #434  |
| `test/built-ins/Math/log1p`                                           | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                      | #376  |
| `test/built-ins/Math/log2`                                            | 4     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent        | #434  |
| `test/built-ins/Math/log2`                                            | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                      | #376  |
| `test/built-ins/Math/random`                                          | 4     | builtin      | `Math.random` is absent                                                           | #445  |
| `test/built-ins/Math/random`                                          | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                      | #376  |
| `test/built-ins/Math/sin`                                             | 7     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent        | #434  |
| `test/built-ins/Math/sin`                                             | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                      | #376  |
| `test/built-ins/Math/sinh`                                            | 4     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent        | #434  |
| `test/built-ins/Math/sinh`                                            | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                      | #376  |
| `test/built-ins/Math/sumPrecise`                                      | 7     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent        | #434  |
| `test/built-ins/Math/sumPrecise`                                      | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                      | #376  |
| `test/built-ins/Math/tan`                                             | 8     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent        | #434  |
| `test/built-ins/Math/tan`                                             | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                      | #376  |
| `test/built-ins/Math/tanh`                                            | 4     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent        | #434  |
| `test/built-ins/Math/tanh`                                            | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                      | #376  |
| `test/built-ins/Number`                                               | 2     | bug          | a numeric literal that overflows to `Infinity` reaches Lean as JSON `null`        | #460  |
| `test/built-ins/Number`                                               | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                      | #376  |
| `test/built-ins/Number`                                               | 1     | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/built-ins/Number`                                               | 1     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/built-ins/Number`                                               | 1     | builtin      | there is no global object                                                         | #487  |
| `test/built-ins/Number/NEGATIVE_INFINITY`                             | 2     | builtin      | the global `isNaN` and `isFinite` are not in the realm                            | #441  |
| `test/built-ins/Number/POSITIVE_INFINITY`                             | 2     | builtin      | the global `isNaN` and `isFinite` are not in the realm                            | #441  |
| `test/built-ins/Number/isFinite`                                      | 1     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/built-ins/Number/isInteger`                                     | 1     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/built-ins/Number/isNaN`                                         | 1     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/built-ins/Number/isSafeInteger`                                 | 1     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/built-ins/Number/prototype/toExponential`                       | 2     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/built-ins/Number/prototype/toExponential`                       | 1     | builtin      | there is no global object                                                         | #487  |
| `test/built-ins/Number/prototype/toFixed`                             | 1     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/built-ins/Number/prototype/toPrecision`                         | 2     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/built-ins/Number/prototype/toPrecision`                         | 1     | builtin      | the rest of `Array.prototype` is absent, `toString` among it                      | #390  |
| `test/built-ins/Number/prototype/toString`                            | 1     | out-of-scope | `Date` is excluded by the epic                                                    | #376  |
| `test/built-ins/Number/prototype/toString`                            | 1     | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/built-ins/Number/prototype/valueOf`                             | 1     | out-of-scope | `Date` is excluded by the epic                                                    | #376  |
| `test/built-ins/Object`                                               | 5     | builtin      | `Function.prototype.caller` and `arguments` are the `%ThrowTypeError%` accessors  | #487  |
| `test/built-ins/Object`                                               | 2     | builtin      | there is no global object                                                         | #487  |
| `test/built-ins/Object`                                               | 1     | out-of-scope | `Date` is excluded by the epic                                                    | #376  |
| `test/built-ins/Object`                                               | 1     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                    | #376  |
| `test/built-ins/Object`                                               | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                      | #376  |
| `test/built-ins/Object`                                               | 1     | builtin      | the rest of `Array.prototype` is absent, `toString` among it                      | #390  |
| `test/built-ins/Object`                                               | 1     | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/built-ins/Object`                                               | 1     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/built-ins/Object/assign`                                        | 5     | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/built-ins/Object/assign`                                        | 4     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/built-ins/Object/assign`                                        | 3     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                    | #376  |
| `test/built-ins/Object/create`                                        | 12    | out-of-scope | `Date` is excluded by the epic                                                    | #376  |
| `test/built-ins/Object/create`                                        | 11    | out-of-scope | `JSON` is excluded by the epic                                                    | #376  |
| `test/built-ins/Object/create`                                        | 11    | out-of-scope | regular expressions are excluded by the epic                                      | #376  |
| `test/built-ins/Object/create`                                        | 11    | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/built-ins/Object/create`                                        | 10    | builtin      | there is no global object                                                         | #487  |
| `test/built-ins/Object/create`                                        | 2     | builtin      | the rest of `Array.prototype` is absent, `toString` among it                      | #390  |
| `test/built-ins/Object/create`                                        | 1     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/built-ins/Object/defineProperties`                              | 13    | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/built-ins/Object/defineProperties`                              | 12    | out-of-scope | `Date` is excluded by the epic                                                    | #376  |
| `test/built-ins/Object/defineProperties`                              | 12    | out-of-scope | `JSON` is excluded by the epic                                                    | #376  |
| `test/built-ins/Object/defineProperties`                              | 12    | out-of-scope | regular expressions are excluded by the epic                                      | #376  |
| `test/built-ins/Object/defineProperties`                              | 10    | builtin      | there is no global object                                                         | #487  |
| `test/built-ins/Object/defineProperties`                              | 2     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/built-ins/Object/defineProperty`                                | 26    | out-of-scope | `Date` is excluded by the epic                                                    | #376  |
| `test/built-ins/Object/defineProperty`                                | 21    | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/built-ins/Object/defineProperty`                                | 19    | out-of-scope | regular expressions are excluded by the epic                                      | #376  |
| `test/built-ins/Object/defineProperty`                                | 18    | out-of-scope | `JSON` is excluded by the epic                                                    | #376  |
| `test/built-ins/Object/defineProperty`                                | 11    | builtin      | there is no global object                                                         | #487  |
| `test/built-ins/Object/defineProperty`                                | 10    | builtin      | the rest of `Array.prototype` is absent, `toString` among it                      | #390  |
| `test/built-ins/Object/defineProperty`                                | 4     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/built-ins/Object/entries`                                       | 3     | builtin      | the rest of `Array.prototype` is absent, `toString` among it                      | #390  |
| `test/built-ins/Object/entries`                                       | 2     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/built-ins/Object/entries`                                       | 1     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                    | #376  |
| `test/built-ins/Object/entries`                                       | 1     | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/built-ins/Object/freeze`                                        | 3     | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/built-ins/Object/freeze`                                        | 2     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/built-ins/Object/freeze`                                        | 1     | out-of-scope | `Date` is excluded by the epic                                                    | #376  |
| `test/built-ins/Object/freeze`                                        | 1     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                    | #376  |
| `test/built-ins/Object/freeze`                                        | 1     | out-of-scope | regular expressions are excluded by the epic                                      | #376  |
| `test/built-ins/Object/fromEntries`                                   | 11    | builtin      | `Object.fromEntries` and `groupBy` take an iterable                               | #394  |
| `test/built-ins/Object/fromEntries`                                   | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                      | #376  |
| `test/built-ins/Object/fromEntries`                                   | 1     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/built-ins/Object/getOwnPropertyDescriptor`                      | 47    | out-of-scope | `Date` is excluded by the epic                                                    | #376  |
| `test/built-ins/Object/getOwnPropertyDescriptor`                      | 26    | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/built-ins/Object/getOwnPropertyDescriptor`                      | 20    | builtin      | the rest of `Array.prototype` is absent, `toString` among it                      | #390  |
| `test/built-ins/Object/getOwnPropertyDescriptor`                      | 11    | builtin      | there is no global object                                                         | #487  |
| `test/built-ins/Object/getOwnPropertyDescriptor`                      | 9     | out-of-scope | regular expressions are excluded by the epic                                      | #376  |
| `test/built-ins/Object/getOwnPropertyDescriptor`                      | 9     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent        | #434  |
| `test/built-ins/Object/getOwnPropertyDescriptor`                      | 2     | out-of-scope | `JSON` is excluded by the epic                                                    | #376  |
| `test/built-ins/Object/getOwnPropertyDescriptor`                      | 1     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/built-ins/Object/getOwnPropertyDescriptor`                      | 1     | builtin      | `Math.random` is absent                                                           | #445  |
| `test/built-ins/Object/getOwnPropertyDescriptors`                     | 3     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/built-ins/Object/getOwnPropertyDescriptors`                     | 2     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                    | #376  |
| `test/built-ins/Object/getOwnPropertyDescriptors`                     | 1     | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/built-ins/Object/getOwnPropertyDescriptors`                     | 1     | builtin      | there is no global object                                                         | #487  |
| `test/built-ins/Object/getOwnPropertyNames`                           | 7     | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/built-ins/Object/getOwnPropertyNames`                           | 4     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/built-ins/Object/getOwnPropertyNames`                           | 1     | out-of-scope | `JSON` is excluded by the epic                                                    | #376  |
| `test/built-ins/Object/getOwnPropertyNames`                           | 1     | builtin      | the rest of `Array.prototype` is absent, `toString` among it                      | #390  |
| `test/built-ins/Object/getOwnPropertySymbols`                         | 6     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/built-ins/Object/getOwnPropertySymbols`                         | 4     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                    | #376  |
| `test/built-ins/Object/getOwnPropertySymbols`                         | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                      | #376  |
| `test/built-ins/Object/getPrototypeOf`                                | 2     | out-of-scope | `Date` is excluded by the epic                                                    | #376  |
| `test/built-ins/Object/getPrototypeOf`                                | 2     | out-of-scope | regular expressions are excluded by the epic                                      | #376  |
| `test/built-ins/Object/getPrototypeOf`                                | 2     | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/built-ins/Object/getPrototypeOf`                                | 1     | out-of-scope | `JSON` is excluded by the epic                                                    | #376  |
| `test/built-ins/Object/getPrototypeOf`                                | 1     | builtin      | there is no global object                                                         | #487  |
| `test/built-ins/Object/groupBy`                                       | 10    | builtin      | `Object.fromEntries` and `groupBy` take an iterable                               | #394  |
| `test/built-ins/Object/groupBy`                                       | 1     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/built-ins/Object/hasOwn`                                        | 4     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/built-ins/Object/internals/DefineOwnProperty`                   | 3     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                    | #376  |
| `test/built-ins/Object/is`                                            | 3     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/built-ins/Object/is`                                            | 2     | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/built-ins/Object/isExtensible`                                  | 2     | out-of-scope | `Date` is excluded by the epic                                                    | #376  |
| `test/built-ins/Object/isExtensible`                                  | 2     | out-of-scope | regular expressions are excluded by the epic                                      | #376  |
| `test/built-ins/Object/isExtensible`                                  | 2     | builtin      | there is no global object                                                         | #487  |
| `test/built-ins/Object/isExtensible`                                  | 1     | out-of-scope | `JSON` is excluded by the epic                                                    | #376  |
| `test/built-ins/Object/isExtensible`                                  | 1     | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/built-ins/Object/isFrozen`                                      | 2     | out-of-scope | `Date` is excluded by the epic                                                    | #376  |
| `test/built-ins/Object/isFrozen`                                      | 2     | out-of-scope | regular expressions are excluded by the epic                                      | #376  |
| `test/built-ins/Object/isFrozen`                                      | 2     | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/built-ins/Object/isFrozen`                                      | 1     | out-of-scope | `JSON` is excluded by the epic                                                    | #376  |
| `test/built-ins/Object/isFrozen`                                      | 1     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/built-ins/Object/isFrozen`                                      | 1     | builtin      | there is no global object                                                         | #487  |
| `test/built-ins/Object/isSealed`                                      | 2     | out-of-scope | `Date` is excluded by the epic                                                    | #376  |
| `test/built-ins/Object/isSealed`                                      | 2     | out-of-scope | regular expressions are excluded by the epic                                      | #376  |
| `test/built-ins/Object/isSealed`                                      | 1     | out-of-scope | `JSON` is excluded by the epic                                                    | #376  |
| `test/built-ins/Object/isSealed`                                      | 1     | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/built-ins/Object/isSealed`                                      | 1     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/built-ins/Object/isSealed`                                      | 1     | builtin      | there is no global object                                                         | #487  |
| `test/built-ins/Object/keys`                                          | 3     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                    | #376  |
| `test/built-ins/Object/keys`                                          | 3     | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/built-ins/Object/keys`                                          | 1     | out-of-scope | `Date` is excluded by the epic                                                    | #376  |
| `test/built-ins/Object/preventExtensions`                             | 3     | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/built-ins/Object/preventExtensions`                             | 2     | out-of-scope | `Date` is excluded by the epic                                                    | #376  |
| `test/built-ins/Object/preventExtensions`                             | 2     | out-of-scope | regular expressions are excluded by the epic                                      | #376  |
| `test/built-ins/Object/preventExtensions`                             | 1     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                    | #376  |
| `test/built-ins/Object/preventExtensions`                             | 1     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/built-ins/Object/prototype`                                     | 4     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                    | #376  |
| `test/built-ins/Object/prototype/__defineGetter__`                    | 9     | builtin      | the Annex B accessors on `Object.prototype` come with the global object           | #487  |
| `test/built-ins/Object/prototype/__defineGetter__`                    | 1     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                    | #376  |
| `test/built-ins/Object/prototype/__defineGetter__`                    | 1     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/built-ins/Object/prototype/__defineSetter__`                    | 9     | builtin      | the Annex B accessors on `Object.prototype` come with the global object           | #487  |
| `test/built-ins/Object/prototype/__defineSetter__`                    | 1     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                    | #376  |
| `test/built-ins/Object/prototype/__defineSetter__`                    | 1     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/built-ins/Object/prototype/__lookupGetter__`                    | 12    | builtin      | the Annex B accessors on `Object.prototype` come with the global object           | #487  |
| `test/built-ins/Object/prototype/__lookupGetter__`                    | 4     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                    | #376  |
| `test/built-ins/Object/prototype/__lookupSetter__`                    | 12    | builtin      | the Annex B accessors on `Object.prototype` come with the global object           | #487  |
| `test/built-ins/Object/prototype/__lookupSetter__`                    | 4     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                    | #376  |
| `test/built-ins/Object/prototype/__proto__`                           | 13    | builtin      | the Annex B accessors on `Object.prototype` come with the global object           | #487  |
| `test/built-ins/Object/prototype/__proto__`                           | 2     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                    | #376  |
| `test/built-ins/Object/prototype/hasOwnProperty`                      | 4     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/built-ins/Object/prototype/isPrototypeOf`                       | 2     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/built-ins/Object/prototype/isPrototypeOf`                       | 1     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                    | #376  |
| `test/built-ins/Object/prototype/propertyIsEnumerable`                | 4     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/built-ins/Object/prototype/propertyIsEnumerable`                | 1     | builtin      | the rest of `Array.prototype` is absent, `toString` among it                      | #390  |
| `test/built-ins/Object/prototype/toString`                            | 7     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/built-ins/Object/prototype/toString`                            | 5     | out-of-scope | the keyed collections and promises are excluded by the epic                       | #376  |
| `test/built-ins/Object/prototype/toString`                            | 3     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                    | #376  |
| `test/built-ins/Object/prototype/toString`                            | 2     | out-of-scope | BigInt is excluded by the epic                                                    | #376  |
| `test/built-ins/Object/prototype/toString`                            | 1     | out-of-scope | `Date` is excluded by the epic                                                    | #376  |
| `test/built-ins/Object/prototype/toString`                            | 1     | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/built-ins/Object/prototype/valueOf`                             | 1     | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/built-ins/Object/seal`                                          | 14    | out-of-scope | typed arrays and their buffers are excluded by the epic                           | #376  |
| `test/built-ins/Object/seal`                                          | 7     | out-of-scope | the keyed collections and promises are excluded by the epic                       | #376  |
| `test/built-ins/Object/seal`                                          | 3     | out-of-scope | `Date` is excluded by the epic                                                    | #376  |
| `test/built-ins/Object/seal`                                          | 3     | out-of-scope | regular expressions are excluded by the epic                                      | #376  |
| `test/built-ins/Object/seal`                                          | 3     | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/built-ins/Object/seal`                                          | 3     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/built-ins/Object/seal`                                          | 2     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                    | #376  |
| `test/built-ins/Object/seal`                                          | 1     | out-of-scope | the `Function` constructor is excluded by the epic                                | #376  |
| `test/built-ins/Object/seal`                                          | 1     | builtin      | `AggregateError` takes an iterable and is not in the realm                        | #394  |
| `test/built-ins/Object/setPrototypeOf`                                | 2     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/built-ins/Object/setPrototypeOf`                                | 1     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                    | #376  |
| `test/built-ins/Object/values`                                        | 2     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                    | #376  |
| `test/built-ins/Object/values`                                        | 2     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/built-ins/Object/values`                                        | 1     | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/built-ins/parseFloat`                                           | 2     | builtin      | there is no global object                                                         | #487  |
| `test/built-ins/parseFloat`                                           | 1     | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/built-ins/parseInt`                                             | 2     | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/built-ins/parseInt`                                             | 2     | builtin      | there is no global object                                                         | #487  |
| `test/harness`                                                        | 7     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/harness`                                                        | 6     | builtin      | the rest of `Array.prototype` is absent, `toString` among it                      | #390  |
| `test/harness`                                                        | 5     | builtin      | there is no global object                                                         | #487  |
| `test/harness`                                                        | 4     | out-of-scope | typed arrays and their buffers are excluded by the epic                           | #376  |
| `test/harness`                                                        | 1     | out-of-scope | `Date` is excluded by the epic                                                    | #376  |
| `test/language/arguments-object`                                      | 2     | out-of-scope | an early-error test that reaches for `eval`                                       | #376  |
| `test/language/expressions/addition`                                  | 7     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/language/expressions/addition`                                  | 5     | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/language/expressions/addition`                                  | 5     | builtin      | the global `isNaN` and `isFinite` are not in the realm                            | #441  |
| `test/language/expressions/addition`                                  | 1     | out-of-scope | `Date` is excluded by the epic                                                    | #376  |
| `test/language/expressions/addition`                                  | 1     | out-of-scope | `eval` is excluded by the epic                                                    | #376  |
| `test/language/expressions/arrow-function`                            | 1     | builtin      | the rest of `Array.prototype` is absent, `toString` among it                      | #390  |
| `test/language/expressions/arrow-function`                            | 1     | builtin      | `Function.prototype.caller` and `arguments` are the `%ThrowTypeError%` accessors  | #487  |
| `test/language/expressions/arrow-function/arrow`                      | 4     | out-of-scope | `eval` is excluded by the epic                                                    | #376  |
| `test/language/expressions/assignment`                                | 1     | builtin      | the rest of `Array.prototype` is absent, `toString` among it                      | #390  |
| `test/language/expressions/assignment`                                | 1     | protocol     | the bridge drops the parentheses that keep NamedEvaluation from naming a function | #499  |
| `test/language/expressions/call`                                      | 4     | out-of-scope | `eval` is excluded by the epic                                                    | #376  |
| `test/language/expressions/call`                                      | 1     | out-of-scope | an early-error test that reaches for `eval`                                       | #376  |
| `test/language/expressions/class`                                     | 1     | builtin      | `Function.prototype.caller` and `arguments` are the `%ThrowTypeError%` accessors  | #487  |
| `test/language/expressions/class/elements`                            | 24    | out-of-scope | an early-error test that reaches for `eval`                                       | #376  |
| `test/language/expressions/class/elements`                            | 19    | out-of-scope | `eval` is excluded by the epic                                                    | #376  |
| `test/language/expressions/class/elements`                            | 2     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                    | #376  |
| `test/language/expressions/class/elements/syntax/valid`               | 1     | bug          | a static method named `constructor` is emitted as the class constructor           | #496  |
| `test/language/expressions/class/subclass-builtins`                   | 14    | out-of-scope | typed arrays and their buffers are excluded by the epic                           | #376  |
| `test/language/expressions/class/subclass-builtins`                   | 6     | out-of-scope | the keyed collections and promises are excluded by the epic                       | #376  |
| `test/language/expressions/class/subclass-builtins`                   | 1     | out-of-scope | `Date` is excluded by the epic                                                    | #376  |
| `test/language/expressions/class/subclass-builtins`                   | 1     | out-of-scope | regular expressions are excluded by the epic                                      | #376  |
| `test/language/expressions/class/subclass-builtins`                   | 1     | out-of-scope | the `Function` constructor is excluded by the epic                                | #376  |
| `test/language/expressions/class/subclass-builtins`                   | 1     | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/language/expressions/class/subclass-builtins`                   | 1     | builtin      | `AggregateError` takes an iterable and is not in the realm                        | #394  |
| `test/language/expressions/conditional`                               | 2     | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/language/expressions/conditional`                               | 1     | out-of-scope | `eval` is excluded by the epic                                                    | #376  |
| `test/language/expressions/conditional`                               | 1     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/language/expressions/division`                                  | 9     | builtin      | the global `isNaN` and `isFinite` are not in the realm                            | #441  |
| `test/language/expressions/division`                                  | 4     | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/language/expressions/division`                                  | 2     | out-of-scope | `eval` is excluded by the epic                                                    | #376  |
| `test/language/expressions/division`                                  | 1     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/language/expressions/function`                                  | 1     | out-of-scope | `eval` is excluded by the epic                                                    | #376  |
| `test/language/expressions/greater-than`                              | 6     | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/language/expressions/greater-than`                              | 1     | out-of-scope | `eval` is excluded by the epic                                                    | #376  |
| `test/language/expressions/greater-than-or-equal`                     | 6     | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/language/expressions/greater-than-or-equal`                     | 1     | out-of-scope | `eval` is excluded by the epic                                                    | #376  |
| `test/language/expressions/less-than`                                 | 6     | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/language/expressions/less-than`                                 | 1     | out-of-scope | `eval` is excluded by the epic                                                    | #376  |
| `test/language/expressions/less-than-or-equal`                        | 6     | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/language/expressions/less-than-or-equal`                        | 1     | out-of-scope | `eval` is excluded by the epic                                                    | #376  |
| `test/language/expressions/logical-and`                               | 2     | builtin      | the global `isNaN` and `isFinite` are not in the realm                            | #441  |
| `test/language/expressions/logical-and`                               | 1     | out-of-scope | `eval` is excluded by the epic                                                    | #376  |
| `test/language/expressions/logical-and`                               | 1     | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/language/expressions/logical-and`                               | 1     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/language/expressions/logical-not`                               | 2     | out-of-scope | `eval` is excluded by the epic                                                    | #376  |
| `test/language/expressions/logical-not`                               | 1     | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/language/expressions/logical-not`                               | 1     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/language/expressions/logical-or`                                | 2     | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/language/expressions/logical-or`                                | 1     | out-of-scope | `eval` is excluded by the epic                                                    | #376  |
| `test/language/expressions/logical-or`                                | 1     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/language/expressions/modulus`                                   | 12    | builtin      | the global `isNaN` and `isFinite` are not in the realm                            | #441  |
| `test/language/expressions/modulus`                                   | 3     | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/language/expressions/modulus`                                   | 1     | out-of-scope | `eval` is excluded by the epic                                                    | #376  |
| `test/language/expressions/modulus`                                   | 1     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/language/expressions/multiplication`                            | 8     | builtin      | the global `isNaN` and `isFinite` are not in the realm                            | #441  |
| `test/language/expressions/multiplication`                            | 4     | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/language/expressions/multiplication`                            | 1     | out-of-scope | `eval` is excluded by the epic                                                    | #376  |
| `test/language/expressions/multiplication`                            | 1     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/language/expressions/strict-does-not-equals`                    | 4     | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/language/expressions/strict-does-not-equals`                    | 2     | out-of-scope | `eval` is excluded by the epic                                                    | #376  |
| `test/language/expressions/strict-equals`                             | 4     | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/language/expressions/strict-equals`                             | 2     | out-of-scope | `eval` is excluded by the epic                                                    | #376  |
| `test/language/expressions/subtraction`                               | 7     | builtin      | the global `isNaN` and `isFinite` are not in the realm                            | #441  |
| `test/language/expressions/subtraction`                               | 4     | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/language/expressions/subtraction`                               | 1     | out-of-scope | `eval` is excluded by the epic                                                    | #376  |
| `test/language/expressions/subtraction`                               | 1     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/language/expressions/unary-minus`                               | 3     | builtin      | the global `isNaN` and `isFinite` are not in the realm                            | #441  |
| `test/language/expressions/unary-minus`                               | 1     | out-of-scope | `eval` is excluded by the epic                                                    | #376  |
| `test/language/expressions/unary-plus`                                | 6     | builtin      | the global `isNaN` and `isFinite` are not in the realm                            | #441  |
| `test/language/expressions/unary-plus`                                | 1     | out-of-scope | `eval` is excluded by the epic                                                    | #376  |
| `test/language/function-code`                                         | 6     | out-of-scope | `eval` is excluded by the epic                                                    | #376  |
| `test/language/function-code`                                         | 4     | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/language/statements/break`                                      | 1     | out-of-scope | `eval` is excluded by the epic                                                    | #376  |
| `test/language/statements/class`                                      | 1     | out-of-scope | `eval` is excluded by the epic                                                    | #376  |
| `test/language/statements/class`                                      | 1     | builtin      | `Function.prototype.caller` and `arguments` are the `%ThrowTypeError%` accessors  | #487  |
| `test/language/statements/class/definition`                           | 1     | builtin      | `Function.prototype.caller` and `arguments` are the `%ThrowTypeError%` accessors  | #487  |
| `test/language/statements/class/elements`                             | 32    | out-of-scope | an early-error test that reaches for `eval`                                       | #376  |
| `test/language/statements/class/elements`                             | 22    | out-of-scope | `eval` is excluded by the epic                                                    | #376  |
| `test/language/statements/class/elements`                             | 4     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                    | #376  |
| `test/language/statements/class/elements`                             | 1     | builtin      | there is no global object                                                         | #487  |
| `test/language/statements/class/elements/syntax/valid`                | 1     | bug          | a static method named `constructor` is emitted as the class constructor           | #496  |
| `test/language/statements/class/strict-mode`                          | 1     | builtin      | `Function.prototype.caller` and `arguments` are the `%ThrowTypeError%` accessors  | #487  |
| `test/language/statements/class/subclass`                             | 2     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/language/statements/class/subclass`                             | 1     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                    | #376  |
| `test/language/statements/class/subclass`                             | 1     | out-of-scope | typed arrays and their buffers are excluded by the epic                           | #376  |
| `test/language/statements/class/subclass-builtins`                    | 14    | out-of-scope | typed arrays and their buffers are excluded by the epic                           | #376  |
| `test/language/statements/class/subclass-builtins`                    | 6     | out-of-scope | the keyed collections and promises are excluded by the epic                       | #376  |
| `test/language/statements/class/subclass-builtins`                    | 1     | out-of-scope | `Date` is excluded by the epic                                                    | #376  |
| `test/language/statements/class/subclass-builtins`                    | 1     | out-of-scope | regular expressions are excluded by the epic                                      | #376  |
| `test/language/statements/class/subclass-builtins`                    | 1     | out-of-scope | the `Function` constructor is excluded by the epic                                | #376  |
| `test/language/statements/class/subclass-builtins`                    | 1     | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/language/statements/class/subclass-builtins`                    | 1     | builtin      | `AggregateError` takes an iterable and is not in the realm                        | #394  |
| `test/language/statements/class/subclass/builtin-objects/ArrayBuffer` | 2     | out-of-scope | typed arrays and their buffers are excluded by the epic                           | #376  |
| `test/language/statements/class/subclass/builtin-objects/DataView`    | 2     | out-of-scope | typed arrays and their buffers are excluded by the epic                           | #376  |
| `test/language/statements/class/subclass/builtin-objects/Date`        | 2     | out-of-scope | `Date` is excluded by the epic                                                    | #376  |
| `test/language/statements/class/subclass/builtin-objects/Function`    | 4     | out-of-scope | the `Function` constructor is excluded by the epic                                | #376  |
| `test/language/statements/class/subclass/builtin-objects/Map`         | 2     | out-of-scope | the keyed collections and promises are excluded by the epic                       | #376  |
| `test/language/statements/class/subclass/builtin-objects/Promise`     | 2     | out-of-scope | the keyed collections and promises are excluded by the epic                       | #376  |
| `test/language/statements/class/subclass/builtin-objects/Proxy`       | 1     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                    | #376  |
| `test/language/statements/class/subclass/builtin-objects/RegExp`      | 3     | out-of-scope | regular expressions are excluded by the epic                                      | #376  |
| `test/language/statements/class/subclass/builtin-objects/Set`         | 2     | out-of-scope | the keyed collections and promises are excluded by the epic                       | #376  |
| `test/language/statements/class/subclass/builtin-objects/String`      | 3     | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/language/statements/class/subclass/builtin-objects/Symbol`      | 2     | builtin      | `Symbol` is not in the realm                                                      | #392  |
| `test/language/statements/class/subclass/builtin-objects/TypedArray`  | 2     | out-of-scope | typed arrays and their buffers are excluded by the epic                           | #376  |
| `test/language/statements/class/subclass/builtin-objects/WeakMap`     | 2     | out-of-scope | the keyed collections and promises are excluded by the epic                       | #376  |
| `test/language/statements/class/subclass/builtin-objects/WeakSet`     | 2     | out-of-scope | the keyed collections and promises are excluded by the epic                       | #376  |
| `test/language/statements/const`                                      | 1     | out-of-scope | `eval` is excluded by the epic                                                    | #376  |
| `test/language/statements/continue`                                   | 1     | out-of-scope | `eval` is excluded by the epic                                                    | #376  |
| `test/language/statements/do-while`                                   | 6     | out-of-scope | `eval` is excluded by the epic                                                    | #376  |
| `test/language/statements/empty`                                      | 1     | out-of-scope | `eval` is excluded by the epic                                                    | #376  |
| `test/language/statements/expression`                                 | 2     | out-of-scope | `eval` is excluded by the epic                                                    | #376  |
| `test/language/statements/for`                                        | 7     | out-of-scope | `eval` is excluded by the epic                                                    | #376  |
| `test/language/statements/for`                                        | 4     | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/language/statements/function`                                   | 4     | builtin      | `Function.prototype.caller` and `arguments` are the `%ThrowTypeError%` accessors  | #487  |
| `test/language/statements/function`                                   | 3     | out-of-scope | an early-error test that reaches for `eval`                                       | #376  |
| `test/language/statements/function`                                   | 2     | out-of-scope | `eval` is excluded by the epic                                                    | #376  |
| `test/language/statements/function`                                   | 2     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent        | #434  |
| `test/language/statements/function`                                   | 1     | out-of-scope | the `Function` constructor is excluded by the epic                                | #376  |
| `test/language/statements/if`                                         | 9     | out-of-scope | `eval` is excluded by the epic                                                    | #376  |
| `test/language/statements/if`                                         | 1     | builtin      | the String wrapper object and `String.prototype` are absent                       | #391  |
| `test/language/statements/labeled`                                    | 2     | out-of-scope | `eval` is excluded by the epic                                                    | #376  |
| `test/language/statements/let`                                        | 1     | out-of-scope | `eval` is excluded by the epic                                                    | #376  |
| `test/language/statements/return`                                     | 1     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent        | #434  |
| `test/language/statements/switch`                                     | 21    | out-of-scope | `eval` is excluded by the epic                                                    | #376  |
| `test/language/statements/switch`                                     | 1     | builtin      | the global `isNaN` and `isFinite` are not in the realm                            | #441  |
| `test/language/statements/throw`                                      | 1     | builtin      | the rest of `Array.prototype` is absent                                           | #390  |
| `test/language/statements/try`                                        | 12    | out-of-scope | `eval` is excluded by the epic                                                    | #376  |
| `test/language/statements/try`                                        | 2     | out-of-scope | an early-error test that reaches for `eval`                                       | #376  |
| `test/language/statements/try`                                        | 1     | builtin      | the rest of `Array.prototype` is absent                                           | #390  |
| `test/language/statements/variable`                                   | 7     | out-of-scope | an early-error test that reaches for `eval`                                       | #376  |
| `test/language/statements/variable`                                   | 6     | out-of-scope | `eval` is excluded by the epic                                                    | #376  |
| `test/language/statements/variable`                                   | 2     | builtin      | there is no global object                                                         | #487  |
| `test/language/statements/while`                                      | 7     | out-of-scope | `eval` is excluded by the epic                                                    | #376  |

## The unsupported column

A test in the `unsupported` column is not a failure: the decoder refused
the document by name before the evaluator saw it, which is the verdict the
runner should file for a program outside the fragment. The kinds, and who
owns them:

| kind                                                                                                                                                     | owner                                                                         |
| -------------------------------------------------------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------- |
| `VariableDeclarationList`, `VariableStatement`, `OmittedExpression`, `SpreadElement`, `SpreadAssignment`                                                 | #394 — binding and assignment patterns, holes, and spread                     |
| `BinaryExpression ,`, the shifts and the bitwise forms, `AssignmentExpression >>>=`                                                                      | #376 — operators the epic does not model                                      |
| `BigIntLiteral`                                                                                                                                          | #376 — BigInt is out of scope                                                 |
| `FunctionExpression generator`, `FunctionDeclaration generator`, `FunctionExpression async`, `ArrowFunctionExpression async`, `RegularExpressionLiteral` | #376 — generators, async, and regular expressions are out of scope            |
| `GetAccessor`, `SetAccessor`, `MethodDeclaration`, `ComputedPropertyName`, `Property numeric key`, `TemplateExpression`, `ShorthandPropertyAssignment`   | #395 — template literals, computed keys, shorthand, and method definitions    |
| `MethodDefinition private`, `ClassStaticBlockDeclaration`, `AccessorKeyword`, `AssignmentExpression super target`                                        | #473 — private methods and accessors, static blocks, and `super.x = v`        |
| `MethodDefinition generator`, `MethodDefinition async`, `Decorator`                                                                                      | #376 — generators, async, and decorators are out of scope                     |
| `MethodDefinition numeric key`                                                                                                                           | #395 — a numeric key needs ToPropertyKey at parse time, as a literal's does   |
| `Parameter`                                                                                                                                              | #394 — rest parameters, and a binding pattern with a default                  |
| `ArrayBindingPattern`, `ObjectBindingPattern`                                                                                                            | #394 — binding patterns                                                       |
| `NoSubstitutionTemplateLiteral`                                                                                                                          | #395 — template literals                                                      |
| `ForOfStatement`                                                                                                                                         | #394 — the one loop form left                                                 |
| `Function constructor`                                                                                                                                   | #376 — the constructor's semantics are `eval` by another spelling             |
| `AssignmentExpression target`, `LogicalExpression ??`, `BinaryExpression ==`, `BinaryExpression !=`                                                      | #376 — loose equality, nullish coalescing, and targets with no reference form |
| `MetaProperty`                                                                                                                                           | #486 — `new.target` as syntax                                                 |
| `WithStatement`                                                                                                                                          | #376 — `with` is not strict-mode syntax and the epic is strict mode only      |
| `$262.createRealm`, `$262.detachArrayBuffer`                                                                                                             | #376 — the host hooks are refused by name                                     |

The counts, from the same run. They are not tested — only the table above
is — but they are what names the next slice to land.

```
  MethodDefinition generator  1436
  Parameter  737
  MethodDefinition private  497
  ArrayBindingPattern  466
  FunctionExpression generator  377
  ComputedPropertyName  360
  ObjectBindingPattern  344
  VariableDeclarationList  226
  VariableStatement  226
  FunctionDeclaration generator  219
  MethodDefinition async  217
  BinaryExpression ,  181
  Function constructor  163
  BigIntLiteral  82
  RegularExpressionLiteral  74
  GetAccessor  53
  SpreadElement  47
  AssignmentExpression target  38
  BinaryExpression ==  32
  MethodDefinition numeric key  29
  ClassStaticBlockDeclaration  26
  MethodDeclaration  26
  ShorthandPropertyAssignment  24
  SpreadAssignment  23
  OmittedExpression  20
  SetAccessor  20
  $262.createRealm  17
  TemplateExpression  13
  NoSubstitutionTemplateLiteral  10
  Decorator  9
  Property numeric key  8
  BinaryExpression !=  7
  AssignmentExpression super target  6
  FunctionExpression async  6
  MetaProperty  6
  BinaryExpression &  4
  FunctionDeclaration async  4
  PropertyDefinition numeric key  4
  ArrowFunctionExpression async  3
  AssignmentExpression >>>=  3
  ForOfStatement  3
  AccessorKeyword  2
  $262.detachArrayBuffer  1
  BinaryExpression >>  1
  LogicalExpression ??  1
  WithStatement  1
```
