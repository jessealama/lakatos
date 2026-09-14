# The failure list for the PR-gated slice

Written 2026-09-14 against test262 at `419d3e0a2273ba01a3bfcbec423f2801425b8e93`
(`tarski/test262/pin.json`), from one run of

```bash
node ../dist/tarski/frontend/src/test262/cli.js --slice-file test262/slice.txt
```

Every failing test in `tarski/test262/slice.txt` is classified here — the
harness, the 27 language directories the thales emitter maps (#383), and
the three built-ins directories #382 added, whose rows #437 pinned
all-unsupported for this slice to ratchet — and
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

`owner` is the issue the row waits on. Nothing here waits on #383 or on
#382: no failure in the slice is caused by the statements and operators
this issue added — the `for`, `switch`, `var`, and update tests under
`tarski/Test/Tarski/` check those directly — and none is a `Math`,
`Number`, or `Boolean` member answering the wrong number.

One divergence found while classifying is not the proximate cause of any
row and so has none: `applyCoercing` runs ToPrimitive on both operands
before ToNumber on either, where 13.15.3 converts the left operand fully
first for every operator but `+`. It is unobservable without a Symbol or a
BigInt operand, and it is filed as #436. The five `order-of-evaluation`
tests that pin it fail today for want of `Symbol`, so they are classified
against #392.

## The table

| directory                                          | fails | class        | why                                                                                                                | owner |
| -------------------------------------------------- | ----- | ------------ | ------------------------------------------------------------------------------------------------------------------ | ----- |
| `test/built-ins/Boolean`                           | 2     | builtin      | `new String` needs the String wrapper object                                                                       | #391  |
| `test/built-ins/Boolean`                           | 2     | builtin      | a function has no `hasOwnProperty`: there is no `Function.prototype`                                               | #389  |
| `test/built-ins/Boolean`                           | 2     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                                     | #376  |
| `test/built-ins/Boolean`                           | 1     | builtin      | `Object.getPrototypeOf` and `isPrototypeOf` are absent                                                             | #389  |
| `test/built-ins/Boolean`                           | 1     | builtin      | `isConstructor.js` needs `Reflect.construct`                                                                       | #389  |
| `test/built-ins/Boolean`                           | 1     | builtin      | `Symbol` is not in the realm                                                                                       | #392  |
| `test/built-ins/Boolean/prototype`                 | 1     | builtin      | `Object.getPrototypeOf` and `isPrototypeOf` are absent                                                             | #389  |
| `test/built-ins/Boolean/prototype/toString`        | 1     | out-of-scope | typed arrays, `Date`, and the other library objects are excluded by the epic                                       | #376  |
| `test/built-ins/Boolean/prototype/valueOf`         | 1     | out-of-scope | typed arrays, `Date`, and the other library objects are excluded by the epic                                       | #376  |
| `test/built-ins/Math`                              | 1     | builtin      | `Object.getPrototypeOf` and `isPrototypeOf` are absent                                                             | #389  |
| `test/built-ins/Math/acos`                         | 5     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                         | #434  |
| `test/built-ins/Math/acosh`                        | 4     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                         | #434  |
| `test/built-ins/Math/asin`                         | 6     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                         | #434  |
| `test/built-ins/Math/asinh`                        | 2     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                         | #434  |
| `test/built-ins/Math/atan`                         | 4     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                         | #434  |
| `test/built-ins/Math/atan2`                        | 8     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                         | #434  |
| `test/built-ins/Math/atanh`                        | 2     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                         | #434  |
| `test/built-ins/Math/cbrt`                         | 2     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                         | #434  |
| `test/built-ins/Math/clz32`                        | 7     | builtin      | `Math.clz32` and `Math.imul` need ToInt32 and ToUint32                                                             | #440  |
| `test/built-ins/Math/cos`                          | 6     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                         | #434  |
| `test/built-ins/Math/cosh`                         | 2     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                         | #434  |
| `test/built-ins/Math/exp`                          | 6     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                         | #434  |
| `test/built-ins/Math/expm1`                        | 2     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                         | #434  |
| `test/built-ins/Math/f16round`                     | 2     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                         | #434  |
| `test/built-ins/Math/hypot`                        | 9     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                         | #434  |
| `test/built-ins/Math/imul`                         | 2     | builtin      | `Math.clz32` and `Math.imul` need ToInt32 and ToUint32                                                             | #440  |
| `test/built-ins/Math/log`                          | 6     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                         | #434  |
| `test/built-ins/Math/log10`                        | 2     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                         | #434  |
| `test/built-ins/Math/log1p`                        | 2     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                         | #434  |
| `test/built-ins/Math/log2`                         | 2     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                         | #434  |
| `test/built-ins/Math/max`                          | 1     | builtin      | `Object.prototype.toString` and `valueOf` are not on the prototype yet                                             | #389  |
| `test/built-ins/Math/max`                          | 1     | builtin      | a function has no `length`                                                                                         | #389  |
| `test/built-ins/Math/min`                          | 1     | builtin      | `Object.prototype.toString` and `valueOf` are not on the prototype yet                                             | #389  |
| `test/built-ins/Math/min`                          | 1     | builtin      | a function has no `length`                                                                                         | #389  |
| `test/built-ins/Math/random`                       | 2     | builtin      | `Math.random` is absent                                                                                            | #445  |
| `test/built-ins/Math/sin`                          | 5     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                         | #434  |
| `test/built-ins/Math/sinh`                         | 2     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                         | #434  |
| `test/built-ins/Math/sumPrecise`                   | 5     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                         | #434  |
| `test/built-ins/Math/tan`                          | 6     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                         | #434  |
| `test/built-ins/Math/tanh`                         | 2     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                         | #434  |
| `test/built-ins/Number`                            | 41    | bug          | ToNumber of a string is a placeholder that answers NaN                                                             | #388  |
| `test/built-ins/Number`                            | 7     | builtin      | a function has no `hasOwnProperty`: there is no `Function.prototype`                                               | #389  |
| `test/built-ins/Number`                            | 3     | builtin      | `Object.getPrototypeOf` and `isPrototypeOf` are absent                                                             | #389  |
| `test/built-ins/Number`                            | 2     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                                     | #376  |
| `test/built-ins/Number`                            | 1     | builtin      | `new String` needs the String wrapper object                                                                       | #391  |
| `test/built-ins/Number`                            | 1     | builtin      | `Object.prototype.toString` and `valueOf` are not on the prototype yet                                             | #389  |
| `test/built-ins/Number`                            | 1     | builtin      | `isConstructor.js` needs `Reflect.construct`                                                                       | #389  |
| `test/built-ins/Number`                            | 1     | builtin      | `Symbol` is not in the realm                                                                                       | #392  |
| `test/built-ins/Number/NEGATIVE_INFINITY`          | 1     | builtin      | the global `isNaN` and `isFinite` are not in the realm                                                             | #441  |
| `test/built-ins/Number/POSITIVE_INFINITY`          | 1     | builtin      | the global `isNaN` and `isFinite` are not in the realm                                                             | #441  |
| `test/built-ins/Number/isFinite`                   | 1     | builtin      | `Symbol` is not in the realm                                                                                       | #392  |
| `test/built-ins/Number/isInteger`                  | 1     | builtin      | `Symbol` is not in the realm                                                                                       | #392  |
| `test/built-ins/Number/isNaN`                      | 1     | builtin      | `Symbol` is not in the realm                                                                                       | #392  |
| `test/built-ins/Number/isSafeInteger`              | 1     | builtin      | `Symbol` is not in the realm                                                                                       | #392  |
| `test/built-ins/Number/parseFloat`                 | 1     | builtin      | `toFixed`, `toPrecision`, `toExponential`, `toLocaleString`, `parseInt`, and `parseFloat` are absent members       | #388  |
| `test/built-ins/Number/parseInt`                   | 1     | builtin      | `toFixed`, `toPrecision`, `toExponential`, `toLocaleString`, `parseInt`, and `parseFloat` are absent members       | #388  |
| `test/built-ins/Number/prototype`                  | 4     | builtin      | `toFixed`, `toPrecision`, `toExponential`, `toLocaleString`, `parseInt`, and `parseFloat` are absent members       | #388  |
| `test/built-ins/Number/prototype`                  | 2     | builtin      | `Object.getPrototypeOf` and `isPrototypeOf` are absent                                                             | #389  |
| `test/built-ins/Number/prototype`                  | 1     | builtin      | `Object.prototype.toString` and `valueOf` are not on the prototype yet                                             | #389  |
| `test/built-ins/Number/prototype/toExponential`    | 10    | builtin      | `toFixed`, `toPrecision`, `toExponential`, `toLocaleString`, `parseInt`, and `parseFloat` are absent members       | #388  |
| `test/built-ins/Number/prototype/toExponential`    | 1     | builtin      | `Symbol` is not in the realm                                                                                       | #392  |
| `test/built-ins/Number/prototype/toFixed`          | 9     | builtin      | `toFixed`, `toPrecision`, `toExponential`, `toLocaleString`, `parseInt`, and `parseFloat` are absent members       | #388  |
| `test/built-ins/Number/prototype/toFixed`          | 1     | builtin      | Number-to-string is the placeholder formatter                                                                      | #388  |
| `test/built-ins/Number/prototype/toFixed`          | 1     | builtin      | `Symbol` is not in the realm                                                                                       | #392  |
| `test/built-ins/Number/prototype/toLocaleString`   | 1     | builtin      | `toFixed`, `toPrecision`, `toExponential`, `toLocaleString`, `parseInt`, and `parseFloat` are absent members       | #388  |
| `test/built-ins/Number/prototype/toPrecision`      | 12    | builtin      | `toFixed`, `toPrecision`, `toExponential`, `toLocaleString`, `parseInt`, and `parseFloat` are absent members       | #388  |
| `test/built-ins/Number/prototype/toPrecision`      | 1     | builtin      | `Symbol` is not in the realm                                                                                       | #392  |
| `test/built-ins/Number/prototype/toString`         | 1     | builtin      | `String.fromCharCode` and `String.prototype.indexOf` are absent                                                    | #391  |
| `test/built-ins/Number/prototype/toString`         | 1     | out-of-scope | typed arrays, `Date`, and the other library objects are excluded by the epic                                       | #376  |
| `test/built-ins/Number/prototype/valueOf`          | 1     | out-of-scope | typed arrays, `Date`, and the other library objects are excluded by the epic                                       | #376  |
| `test/harness`                                     | 5     | out-of-scope | typed arrays, `Date`, and the other library objects are excluded by the epic                                       | #376  |
| `test/harness`                                     | 4     | builtin      | the harness's `compareArray.format` calls `Array.prototype.map`                                                    | #390  |
| `test/harness`                                     | 3     | builtin      | there is no global object, so `globalThis` and a top-level `this` are unbound                                      | #389  |
| `test/harness`                                     | 2     | builtin      | `String({})` needs `Object.prototype.toString`, and so does the harness's fallback                                 | #389  |
| `test/harness`                                     | 1     | builtin      | `String.fromCharCode` and `String.prototype.indexOf` are absent                                                    | #391  |
| `test/harness`                                     | 1     | builtin      | `Array.prototype.map` is absent, so the harness's `compareArray.format` reads `.call` off `undefined`              | #390  |
| `test/harness`                                     | 1     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                                     | #376  |
| `test/harness`                                     | 1     | out-of-scope | `getWellKnownIntrinsicObject` reaches the intrinsics through `Function`                                            | #376  |
| `test/language/expressions/addition`               | 6     | builtin      | `Symbol` is not in the realm                                                                                       | #392  |
| `test/language/expressions/addition`               | 5     | builtin      | the global `isNaN` and `isFinite` are not in the realm                                                             | #441  |
| `test/language/expressions/addition`               | 5     | builtin      | `new String` needs the String wrapper object                                                                       | #391  |
| `test/language/expressions/addition`               | 2     | builtin      | `Object.prototype.toString` and `valueOf` are not on the prototype yet                                             | #389  |
| `test/language/expressions/addition`               | 1     | builtin      | the ToNumeric step it pins needs `Symbol`; the order divergence behind it is #436                                  | #392  |
| `test/language/expressions/addition`               | 1     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                                     | #376  |
| `test/language/expressions/addition`               | 1     | out-of-scope | typed arrays, `Date`, and the other library objects are excluded by the epic                                       | #376  |
| `test/language/expressions/assignment`             | 7     | builtin      | `Object.defineProperty`, `preventExtensions`, and property attributes are absent, so `Math.PI = 20` does not throw | #389  |
| `test/language/expressions/assignment`             | 1     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                                     | #376  |
| `test/language/expressions/conditional`            | 2     | builtin      | `new String` needs the String wrapper object                                                                       | #391  |
| `test/language/expressions/conditional`            | 1     | builtin      | `Symbol` is not in the realm                                                                                       | #392  |
| `test/language/expressions/conditional`            | 1     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                                     | #376  |
| `test/language/expressions/division`               | 9     | builtin      | the global `isNaN` and `isFinite` are not in the realm                                                             | #441  |
| `test/language/expressions/division`               | 4     | bug          | ToNumber of a string is a placeholder that answers NaN                                                             | #388  |
| `test/language/expressions/division`               | 2     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                                     | #376  |
| `test/language/expressions/division`               | 1     | builtin      | the ToNumeric step it pins needs `Symbol`; the order divergence behind it is #436                                  | #392  |
| `test/language/expressions/greater-than`           | 4     | builtin      | `new String` needs the String wrapper object                                                                       | #391  |
| `test/language/expressions/greater-than`           | 1     | bug          | ToNumber of a string is a placeholder that answers NaN                                                             | #388  |
| `test/language/expressions/greater-than`           | 1     | bug          | a Lean `String` is code points, so the relational order is not UTF-16 code-unit order                              | #391  |
| `test/language/expressions/greater-than`           | 1     | builtin      | `Object.prototype.toString` and `valueOf` are not on the prototype yet                                             | #389  |
| `test/language/expressions/greater-than`           | 1     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                                     | #376  |
| `test/language/expressions/greater-than-or-equal`  | 3     | bug          | ToNumber of a string is a placeholder that answers NaN                                                             | #388  |
| `test/language/expressions/greater-than-or-equal`  | 2     | builtin      | `new String` needs the String wrapper object                                                                       | #391  |
| `test/language/expressions/greater-than-or-equal`  | 1     | bug          | a Lean `String` is code points, so the relational order is not UTF-16 code-unit order                              | #391  |
| `test/language/expressions/greater-than-or-equal`  | 1     | builtin      | `Object.prototype.toString` and `valueOf` are not on the prototype yet                                             | #389  |
| `test/language/expressions/greater-than-or-equal`  | 1     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                                     | #376  |
| `test/language/expressions/less-than`              | 4     | builtin      | `new String` needs the String wrapper object                                                                       | #391  |
| `test/language/expressions/less-than`              | 1     | bug          | ToNumber of a string is a placeholder that answers NaN                                                             | #388  |
| `test/language/expressions/less-than`              | 1     | bug          | a Lean `String` is code points, so the relational order is not UTF-16 code-unit order                              | #391  |
| `test/language/expressions/less-than`              | 1     | builtin      | `Object.prototype.toString` and `valueOf` are not on the prototype yet                                             | #389  |
| `test/language/expressions/less-than`              | 1     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                                     | #376  |
| `test/language/expressions/less-than-or-equal`     | 3     | bug          | ToNumber of a string is a placeholder that answers NaN                                                             | #388  |
| `test/language/expressions/less-than-or-equal`     | 2     | builtin      | `new String` needs the String wrapper object                                                                       | #391  |
| `test/language/expressions/less-than-or-equal`     | 1     | bug          | a Lean `String` is code points, so the relational order is not UTF-16 code-unit order                              | #391  |
| `test/language/expressions/less-than-or-equal`     | 1     | builtin      | `Object.prototype.toString` and `valueOf` are not on the prototype yet                                             | #389  |
| `test/language/expressions/less-than-or-equal`     | 1     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                                     | #376  |
| `test/language/expressions/logical-and`            | 2     | builtin      | the global `isNaN` and `isFinite` are not in the realm                                                             | #441  |
| `test/language/expressions/logical-and`            | 1     | builtin      | `new String` needs the String wrapper object                                                                       | #391  |
| `test/language/expressions/logical-and`            | 1     | builtin      | `Symbol` is not in the realm                                                                                       | #392  |
| `test/language/expressions/logical-and`            | 1     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                                     | #376  |
| `test/language/expressions/logical-not`            | 2     | builtin      | `new String` needs the String wrapper object                                                                       | #391  |
| `test/language/expressions/logical-not`            | 2     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                                     | #376  |
| `test/language/expressions/logical-not`            | 1     | builtin      | `Symbol` is not in the realm                                                                                       | #392  |
| `test/language/expressions/logical-or`             | 2     | builtin      | `new String` needs the String wrapper object                                                                       | #391  |
| `test/language/expressions/logical-or`             | 1     | builtin      | `Symbol` is not in the realm                                                                                       | #392  |
| `test/language/expressions/logical-or`             | 1     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                                     | #376  |
| `test/language/expressions/modulus`                | 12    | builtin      | the global `isNaN` and `isFinite` are not in the realm                                                             | #441  |
| `test/language/expressions/modulus`                | 3     | bug          | ToNumber of a string is a placeholder that answers NaN                                                             | #388  |
| `test/language/expressions/modulus`                | 1     | builtin      | the ToNumeric step it pins needs `Symbol`; the order divergence behind it is #436                                  | #392  |
| `test/language/expressions/modulus`                | 1     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                                     | #376  |
| `test/language/expressions/multiplication`         | 8     | builtin      | the global `isNaN` and `isFinite` are not in the realm                                                             | #441  |
| `test/language/expressions/multiplication`         | 4     | bug          | ToNumber of a string is a placeholder that answers NaN                                                             | #388  |
| `test/language/expressions/multiplication`         | 1     | builtin      | the ToNumeric step it pins needs `Symbol`; the order divergence behind it is #436                                  | #392  |
| `test/language/expressions/multiplication`         | 1     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                                     | #376  |
| `test/language/expressions/strict-does-not-equals` | 3     | builtin      | `new String` needs the String wrapper object                                                                       | #391  |
| `test/language/expressions/strict-does-not-equals` | 2     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                                     | #376  |
| `test/language/expressions/strict-does-not-equals` | 1     | builtin      | `Object(v)` on a primitive needs a wrapper object                                                                  | #391  |
| `test/language/expressions/strict-equals`          | 3     | builtin      | `new String` needs the String wrapper object                                                                       | #391  |
| `test/language/expressions/strict-equals`          | 2     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                                     | #376  |
| `test/language/expressions/strict-equals`          | 1     | builtin      | `Object(v)` on a primitive needs a wrapper object                                                                  | #391  |
| `test/language/expressions/subtraction`            | 7     | builtin      | the global `isNaN` and `isFinite` are not in the realm                                                             | #441  |
| `test/language/expressions/subtraction`            | 4     | bug          | ToNumber of a string is a placeholder that answers NaN                                                             | #388  |
| `test/language/expressions/subtraction`            | 1     | builtin      | the ToNumeric step it pins needs `Symbol`; the order divergence behind it is #436                                  | #392  |
| `test/language/expressions/subtraction`            | 1     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                                     | #376  |
| `test/language/expressions/unary-minus`            | 2     | bug          | ToNumber of a string is a placeholder that answers NaN                                                             | #388  |
| `test/language/expressions/unary-minus`            | 2     | builtin      | the global `isNaN` and `isFinite` are not in the realm                                                             | #441  |
| `test/language/expressions/unary-minus`            | 1     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                                     | #376  |
| `test/language/expressions/unary-plus`             | 5     | builtin      | the global `isNaN` and `isFinite` are not in the realm                                                             | #441  |
| `test/language/expressions/unary-plus`             | 2     | bug          | ToNumber of a string is a placeholder that answers NaN                                                             | #388  |
| `test/language/expressions/unary-plus`             | 1     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                                     | #376  |
| `test/language/statements/const`                   | 1     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                                     | #376  |
| `test/language/statements/for`                     | 7     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                                     | #376  |
| `test/language/statements/for`                     | 4     | builtin      | `new String` needs the String wrapper object                                                                       | #391  |
| `test/language/statements/if`                      | 9     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                                     | #376  |
| `test/language/statements/if`                      | 1     | builtin      | `new String` needs the String wrapper object                                                                       | #391  |
| `test/language/statements/let`                     | 1     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                                     | #376  |
| `test/language/statements/return`                  | 1     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                         | #434  |
| `test/language/statements/throw`                   | 1     | builtin      | `Array.prototype.concat` is absent                                                                                 | #390  |
| `test/language/statements/variable`                | 17    | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                                     | #376  |
| `test/language/statements/variable`                | 1     | builtin      | there is no global object, so `globalThis` and a top-level `this` are unbound                                      | #389  |
| `test/language/statements/while`                   | 7     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                                     | #376  |

## The unsupported column

A test in the `unsupported` column is not a failure: the decoder refused
the document by name before the evaluator saw it, which is the verdict the
runner should file for a program outside the fragment. The kinds, and who
owns them:

| kind                                                                                                                                                     | owner                                                                         |
| -------------------------------------------------------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------- |
| `VariableDeclarationList`, `VariableStatement`, `OmittedExpression`, `SpreadElement`, `SpreadAssignment`                                                 | #394 — binding and assignment patterns, holes, and spread                     |
| `DeleteExpression`, `BinaryExpression ,`, `BinaryExpression in`, the shifts and the bitwise forms, `AssignmentExpression >>>=`                           | #376 — operators the epic does not model                                      |
| `BigIntLiteral`                                                                                                                                          | #376 — BigInt is out of scope                                                 |
| `FunctionExpression generator`, `FunctionDeclaration generator`, `FunctionExpression async`, `ArrowFunctionExpression async`, `RegularExpressionLiteral` | #376 — generators, async, and regular expressions are out of scope            |
| `GetAccessor`, `SetAccessor`, `MethodDeclaration`, `ComputedPropertyName`, `Property numeric key`, `TemplateExpression`, `ShorthandPropertyAssignment`   | #395 — template literals, computed keys, shorthand, and method definitions    |
| `ClassDeclaration`                                                                                                                                       | #384 — classes                                                                |
| `DoStatement`, `ForInStatement`, `ForOfStatement`                                                                                                        | #393, #394 — the loop forms this issue did not take                           |
| `AssignmentExpression target`, `LogicalExpression ??`, `BinaryExpression ==`, `BinaryExpression !=`                                                      | #376 — loose equality, nullish coalescing, and targets with no reference form |
| `$262.createRealm`, `$262.detachArrayBuffer`                                                                                                             | #376 — the host hooks are refused by name                                     |

The counts, from the same run. They are not tested — only the table above
is — but they are what names the next slice to land.

```
  DeleteExpression  284
  VariableDeclarationList  214
  VariableStatement  213
  BinaryExpression ,  85
  BigIntLiteral  75
  FunctionExpression generator  69
  FunctionDeclaration generator  36
  AssignmentExpression target  28
  ShorthandPropertyAssignment  18
  GetAccessor  13
  SpreadElement  13
  OmittedExpression  12
  TemplateExpression  11
  ClassDeclaration  8
  ForInStatement  8
  BinaryExpression ==  6
  ComputedPropertyName  6
  BinaryExpression !=  5
  SetAccessor  5
  MethodDeclaration  4
  SpreadAssignment  4
  $262.createRealm  3
  BinaryExpression in  3
  FunctionExpression async  3
  BinaryExpression &  2
  ForOfStatement  2
  $262.detachArrayBuffer  1
  ArrowFunctionExpression async  1
  AssignmentExpression >>>=  1
  BinaryExpression >>  1
  DoStatement  1
  LogicalExpression ??  1
  Property numeric key  1
  RegularExpressionLiteral  1
```
