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
added, the ten iterator, `for`-`of`, spread, and array-literal
directories #394 added, and the forty-eight `Array` directories #390
added — and
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
code units. And **not one row is a member of `Array.prototype` answering
wrongly, a hole read as a value, a `length` grown or truncated by the
wrong amount, or a species allocation building the wrong thing** — the
rows that waited on #390 are gone.

Nothing waits on #394 either: `for`-`of`, spread, destructuring, and the
three iterators answer correctly. Two seams the merge of #390 and #394
left are filed rather than classified under a closed issue — #531,
`Array.from` never asking for `@@iterator`, and #532,
`%IteratorPrototype%` carrying no `@@toStringTag` — and #533 is the
destructuring evaluation order the two order tests see.

The 1,644 failures below, by owner: 1,019 what #376 excludes (`eval`,
`Date`, `RegExp`, `Proxy`, `Reflect`, typed arrays, the keyed
collections, explicit resource management, the `Iterator` constructor and
its helpers, `Error.prototype.stack`, `JSON.rawJSON` and the reviver's
source text, `Array.fromAsync`, the `Function` constructor's semantics,
and `nativeFunctionMatcher.js`, which matches source text with a regular
expression), 191 the global object (#487), 151 the transcendental `Math`
members (#434), 110 the six ES2023 `Array.prototype` members (#513), 70
the global `isNaN` and `isFinite` (#441), 18 ToLength of an infinite
`length` (#514), 16 the Unicode character database (#518), 14
`Array.from` over an iterable (#531), 13 `Math.clz32`/`imul` (#440), 10
the `@@split`, `@@replace`, and `@@match` lookups the `String` methods
skip (#523), 5 `Array.prototype[@@unscopables]` (#524), 5 `Math.random`
(#445), 2 `%IteratorPrototype%`'s `@@toStringTag` (#532), and 20 the nine
filed defects (#436, #460, #496, #499, #512, #516, #520, #522, and
#533).

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

**The ten directories #394 added are 600 pass, 46 fail, and 149
unsupported.** `statements/for-of` is 453 pass and 37 fail across its own
directory and its `dstr` subtree — the subtree itself is 403 and **0** —
and not one of the 37 is the loop: 18 are typed arrays, 10 the keyed
collections, 6 `eval`, 2 `using` declarations, and 1 `Proxy`. The three
`Array.prototype.pop` rows that were among them before #390 are gone.
`expressions/array` is 50 pass and 0 fail, `expressions/new` 54 and 0,
`ArrayIteratorPrototype` 9 and 9 — those 9 failures typed arrays and
nothing else — and the four `Array.prototype` iterator members 28 and 0.
**Every other directory's `dstr` subtree ratcheted with them**, and the
String iterator cleared `String/prototype/Symbol.iterator` to 6 pass and
0 fail.

**The forty-eight `Array` directories #390 added are 2,579 pass and 271
fail**, with 108 unsupported and 124 not run — 88 `async`
`Array.fromAsync` tests and 36 `noStrict` ones, neither of which this
epic runs. Not one of the 271 is a member of `Array.prototype` answering
the wrong thing: 110 are the six ES2023 members this slice does not write
— `findLast`, `findLastIndex`, `toReversed`, `toSorted`, `toSpliced`, and
`with`, which are #513's; 107 are what #376 excludes, `Proxy`, `Date`,
regular expressions, typed arrays, `isConstructor.js`, `eval`,
`Array.fromAsync`, and `Reflect` among them; 18 are ToLength of an
infinite `length` (#514); 14 are `Array.from` never asking for
`@@iterator` (#531); 7 are the global object (#487); 5 are
`Array.prototype[@@unscopables]` (#524); 5 are the global `isNaN`
(#441); 2 are ArraySetLength's double coercion (#520); 2 are the
`Infinity` literal (#460); and 1 is a transcendental `Math` member
(#434).

**`test/built-ins/String` is 940 pass and 132 fail** over 41 rows, with
148 unsupported and three not run. Not one of the 132 is a `String`
member answering the wrong thing: 101 are what #376 excludes, 77 of them
regular expressions; 16 are the Unicode character database (#518); 10 are
the `@@split`, `@@replace`, and `@@match` protocol lookups (#523); 3 are
the global object (#487); and 2 are a non-callable `@@toPrimitive`
falling through to OrdinaryToPrimitive (#516).

**The two `Object` and `Function` directories are 3,114 pass and 444
fail**, against 3,031 and 519 before this slice: the rows that reached
the rest of `Array.prototype` through `map` and `indexOf` are gone, and
so are the ones that waited on iterators — `Object.fromEntries` is 25
pass and 0 fail, `Object.groupBy` 14 and 0. Their 444: 289 what #376
excludes; 143 the global object, whose `this` at top level a third of
`Object`'s older tests reach for (#487); 9 `Math` members the library
does not model, read through `getOwnPropertyDescriptor` (#434); 2
`%IteratorPrototype%`'s missing `@@toStringTag` (#532); and 1
`Math.random` (#445).

**The `propertyHelper.js`-based tests run and pass**: `Math/abs` is 8 and
0, and `length.js`, `name.js`, and `prop-desc.js` under it are three of
them.

`test/harness` is 70 pass and 11 fail, against 61 and 18: `compareArray`
and `propertyHelper` reach the whole of `Array.prototype` now, and what
is left is the global object (6), typed arrays and `Date` (5).

**The seven directories #392 added are 340 pass, 122 fail, and 47
unsupported.** Of the 122, 107 are what #376 excludes —
`Error.prototype.stack`, which is not in the specification and is absent
by design; explicit resource management, which is the whole of
`SuppressedError`; `Proxy`; `JSON.rawJSON`, `JSON.isRawJSON`, and the
reviver's `context` argument; and `isConstructor.js`, which needs
`Reflect.construct` — 12 the global object (#487), 2 a defect #392 found
and filed (#512), and 1 `JSON.stringify` writing a lone surrogate as
U+FFFD rather than its `\u` escape, because the JSON text is a Lean
`String` (#522). **Not one is a symbol, a JSON text, or an `Error` member
answering the wrong thing.**

## The table

| directory                                                             | fails | class        | why                                                                                                                 | owner |
| --------------------------------------------------------------------- | ----- | ------------ | ------------------------------------------------------------------------------------------------------------------- | ----- |
| `test/built-ins/AggregateError`                                       | 1     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/AggregateError`                                       | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/AggregateError`                                       | 1     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/Array`                                                | 1     | builtin      | there is no global object, so a top-level `this` is `undefined`                                                     | #487  |
| `test/built-ins/Array`                                                | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/Array/from`                                           | 14    | builtin      | `Array.from` reads an array-like by index and does not take the iterable path                                       | #531  |
| `test/built-ins/Array/from`                                           | 2     | builtin      | there is no global object, so a top-level `this` is `undefined`                                                     | #487  |
| `test/built-ins/Array/from`                                           | 1     | out-of-scope | typed arrays and their buffers are excluded by the epic                                                             | #376  |
| `test/built-ins/Array/fromAsync`                                      | 4     | out-of-scope | `Array.fromAsync` is async and outside the epic                                                                     | #376  |
| `test/built-ins/Array/fromAsync`                                      | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/Array/isArray`                                        | 2     | out-of-scope | `Proxy` is excluded by the epic                                                                                     | #376  |
| `test/built-ins/Array/isArray`                                        | 1     | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Array/isArray`                                        | 1     | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/built-ins/Array/length`                                         | 2     | bug          | `ArraySetLength` coerces its value twice                                                                            | #520  |
| `test/built-ins/Array/length`                                         | 1     | out-of-scope | `Reflect` is excluded by the epic                                                                                   | #376  |
| `test/built-ins/Array/of`                                             | 1     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                          | #434  |
| `test/built-ins/Array/of`                                             | 1     | out-of-scope | `Proxy` is excluded by the epic                                                                                     | #376  |
| `test/built-ins/Array/prototype`                                      | 1     | builtin      | there is no global object, so a top-level `this` is `undefined`                                                     | #487  |
| `test/built-ins/Array/prototype/Symbol.unscopables`                   | 5     | builtin      | `Array.prototype[@@unscopables]` is absent                                                                          | #524  |
| `test/built-ins/Array/prototype/concat`                               | 6     | out-of-scope | `Proxy` is excluded by the epic                                                                                     | #376  |
| `test/built-ins/Array/prototype/concat`                               | 2     | out-of-scope | typed arrays and their buffers are excluded by the epic                                                             | #376  |
| `test/built-ins/Array/prototype/copyWithin`                           | 2     | out-of-scope | `Proxy` is excluded by the epic                                                                                     | #376  |
| `test/built-ins/Array/prototype/every`                                | 3     | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Array/prototype/every`                                | 3     | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/built-ins/Array/prototype/every`                                | 2     | bug          | ToLength of an infinite `length` answers 0                                                                          | #514  |
| `test/built-ins/Array/prototype/every`                                | 1     | builtin      | there is no global object, so a top-level `this` is `undefined`                                                     | #487  |
| `test/built-ins/Array/prototype/every`                                | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Array/prototype/every`                                | 1     | out-of-scope | typed arrays and their buffers are excluded by the epic                                                             | #376  |
| `test/built-ins/Array/prototype/filter`                               | 3     | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Array/prototype/filter`                               | 3     | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/built-ins/Array/prototype/filter`                               | 2     | out-of-scope | `Proxy` is excluded by the epic                                                                                     | #376  |
| `test/built-ins/Array/prototype/filter`                               | 1     | builtin      | there is no global object, so a top-level `this` is `undefined`                                                     | #487  |
| `test/built-ins/Array/prototype/filter`                               | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Array/prototype/filter`                               | 1     | out-of-scope | typed arrays and their buffers are excluded by the epic                                                             | #376  |
| `test/built-ins/Array/prototype/find`                                 | 1     | out-of-scope | typed arrays and their buffers are excluded by the epic                                                             | #376  |
| `test/built-ins/Array/prototype/findIndex`                            | 1     | out-of-scope | typed arrays and their buffers are excluded by the epic                                                             | #376  |
| `test/built-ins/Array/prototype/findLast`                             | 15    | builtin      | the ES2023 `Array.prototype` members are absent                                                                     | #513  |
| `test/built-ins/Array/prototype/findLast`                             | 1     | out-of-scope | typed arrays and their buffers are excluded by the epic                                                             | #376  |
| `test/built-ins/Array/prototype/findLast`                             | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/Array/prototype/findLastIndex`                        | 15    | builtin      | the ES2023 `Array.prototype` members are absent                                                                     | #513  |
| `test/built-ins/Array/prototype/findLastIndex`                        | 1     | out-of-scope | typed arrays and their buffers are excluded by the epic                                                             | #376  |
| `test/built-ins/Array/prototype/findLastIndex`                        | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/Array/prototype/flat`                                 | 1     | out-of-scope | `Proxy` is excluded by the epic                                                                                     | #376  |
| `test/built-ins/Array/prototype/flatMap`                              | 2     | out-of-scope | typed arrays and their buffers are excluded by the epic                                                             | #376  |
| `test/built-ins/Array/prototype/flatMap`                              | 1     | out-of-scope | `Proxy` is excluded by the epic                                                                                     | #376  |
| `test/built-ins/Array/prototype/forEach`                              | 2     | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Array/prototype/forEach`                              | 2     | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/built-ins/Array/prototype/forEach`                              | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Array/prototype/forEach`                              | 1     | out-of-scope | typed arrays and their buffers are excluded by the epic                                                             | #376  |
| `test/built-ins/Array/prototype/includes`                             | 1     | bug          | ToLength of an infinite `length` answers 0                                                                          | #514  |
| `test/built-ins/Array/prototype/includes`                             | 1     | out-of-scope | `Proxy` is excluded by the epic                                                                                     | #376  |
| `test/built-ins/Array/prototype/indexOf`                              | 2     | bug          | ToLength of an infinite `length` answers 0                                                                          | #514  |
| `test/built-ins/Array/prototype/indexOf`                              | 1     | bug          | a literal that overflows to `Infinity` reaches Lean as JSON `null`                                                  | #460  |
| `test/built-ins/Array/prototype/indexOf`                              | 1     | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Array/prototype/indexOf`                              | 1     | out-of-scope | `Proxy` is excluded by the epic                                                                                     | #376  |
| `test/built-ins/Array/prototype/indexOf`                              | 1     | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/built-ins/Array/prototype/lastIndexOf`                          | 2     | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/built-ins/Array/prototype/lastIndexOf`                          | 1     | bug          | a literal that overflows to `Infinity` reaches Lean as JSON `null`                                                  | #460  |
| `test/built-ins/Array/prototype/lastIndexOf`                          | 1     | builtin      | the global `isNaN` and `isFinite` are absent                                                                        | #441  |
| `test/built-ins/Array/prototype/lastIndexOf`                          | 1     | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Array/prototype/lastIndexOf`                          | 1     | out-of-scope | `Proxy` is excluded by the epic                                                                                     | #376  |
| `test/built-ins/Array/prototype/lastIndexOf`                          | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Array/prototype/map`                                  | 3     | out-of-scope | `Proxy` is excluded by the epic                                                                                     | #376  |
| `test/built-ins/Array/prototype/map`                                  | 2     | bug          | ToLength of an infinite `length` answers 0                                                                          | #514  |
| `test/built-ins/Array/prototype/map`                                  | 2     | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Array/prototype/map`                                  | 2     | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/built-ins/Array/prototype/map`                                  | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Array/prototype/map`                                  | 1     | out-of-scope | typed arrays and their buffers are excluded by the epic                                                             | #376  |
| `test/built-ins/Array/prototype/pop`                                  | 2     | bug          | ToLength of an infinite `length` answers 0                                                                          | #514  |
| `test/built-ins/Array/prototype/push`                                 | 3     | bug          | ToLength of an infinite `length` answers 0                                                                          | #514  |
| `test/built-ins/Array/prototype/reduce`                               | 2     | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Array/prototype/reduce`                               | 2     | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/built-ins/Array/prototype/reduce`                               | 1     | out-of-scope | typed arrays and their buffers are excluded by the epic                                                             | #376  |
| `test/built-ins/Array/prototype/reduceRight`                          | 2     | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Array/prototype/reduceRight`                          | 2     | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/built-ins/Array/prototype/reduceRight`                          | 1     | out-of-scope | typed arrays and their buffers are excluded by the epic                                                             | #376  |
| `test/built-ins/Array/prototype/reverse`                              | 1     | out-of-scope | `Proxy` is excluded by the epic                                                                                     | #376  |
| `test/built-ins/Array/prototype/slice`                                | 4     | out-of-scope | `Proxy` is excluded by the epic                                                                                     | #376  |
| `test/built-ins/Array/prototype/some`                                 | 3     | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Array/prototype/some`                                 | 3     | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/built-ins/Array/prototype/some`                                 | 2     | bug          | ToLength of an infinite `length` answers 0                                                                          | #514  |
| `test/built-ins/Array/prototype/some`                                 | 1     | builtin      | there is no global object, so a top-level `this` is `undefined`                                                     | #487  |
| `test/built-ins/Array/prototype/some`                                 | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Array/prototype/some`                                 | 1     | out-of-scope | typed arrays and their buffers are excluded by the epic                                                             | #376  |
| `test/built-ins/Array/prototype/sort`                                 | 4     | builtin      | the global `isNaN` and `isFinite` are absent                                                                        | #441  |
| `test/built-ins/Array/prototype/splice`                               | 5     | out-of-scope | `Proxy` is excluded by the epic                                                                                     | #376  |
| `test/built-ins/Array/prototype/splice`                               | 2     | bug          | ToLength of an infinite `length` answers 0                                                                          | #514  |
| `test/built-ins/Array/prototype/toReversed`                           | 15    | builtin      | the ES2023 `Array.prototype` members are absent                                                                     | #513  |
| `test/built-ins/Array/prototype/toReversed`                           | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/Array/prototype/toSorted`                             | 18    | builtin      | the ES2023 `Array.prototype` members are absent                                                                     | #513  |
| `test/built-ins/Array/prototype/toSorted`                             | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/Array/prototype/toSpliced`                            | 28    | builtin      | the ES2023 `Array.prototype` members are absent                                                                     | #513  |
| `test/built-ins/Array/prototype/toSpliced`                            | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/Array/prototype/unshift`                              | 2     | bug          | ToLength of an infinite `length` answers 0                                                                          | #514  |
| `test/built-ins/Array/prototype/with`                                 | 19    | builtin      | the ES2023 `Array.prototype` members are absent                                                                     | #513  |
| `test/built-ins/Array/prototype/with`                                 | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/ArrayIteratorPrototype/next`                          | 9     | out-of-scope | typed arrays and their buffers are excluded by the epic                                                             | #376  |
| `test/built-ins/Boolean`                                              | 1     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/Boolean`                                              | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Boolean`                                              | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/Boolean/prototype/toString`                           | 1     | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Boolean/prototype/valueOf`                            | 1     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/Error`                                                | 1     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/Error`                                                | 1     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/Error`                                                | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/Error/prototype/stack`                                | 31    | out-of-scope | `Error.prototype.stack` is not in the specification and is absent by design                                         | #376  |
| `test/built-ins/Error/prototype/toString`                             | 1     | builtin      | there is no global object, so a top-level `this` is `undefined`                                                     | #487  |
| `test/built-ins/Function`                                             | 21    | builtin      | `Function.prototype.caller` and `arguments` are the `%ThrowTypeError%` accessors                                    | #487  |
| `test/built-ins/Function`                                             | 5     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/Function`                                             | 5     | out-of-scope | the `Function` constructor is excluded by the epic                                                                  | #376  |
| `test/built-ins/Function`                                             | 2     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Function/internals/Construct`                         | 1     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
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
| `test/built-ins/NativeErrors/EvalError`                               | 1     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/NativeErrors/EvalError`                               | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/NativeErrors/RangeError`                              | 1     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/NativeErrors/RangeError`                              | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/NativeErrors/ReferenceError`                          | 1     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/NativeErrors/ReferenceError`                          | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/NativeErrors/SyntaxError`                             | 1     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/NativeErrors/SyntaxError`                             | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/NativeErrors/TypeError`                               | 1     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/NativeErrors/TypeError`                               | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/NativeErrors/URIError`                                | 1     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/NativeErrors/URIError`                                | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/Number`                                               | 2     | bug          | a numeric literal that overflows to `Infinity` reaches Lean as JSON `null`                                          | #460  |
| `test/built-ins/Number`                                               | 1     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/Number`                                               | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/Number/NEGATIVE_INFINITY`                             | 2     | builtin      | the global `isNaN` and `isFinite` are not in the realm                                                              | #441  |
| `test/built-ins/Number/POSITIVE_INFINITY`                             | 2     | builtin      | the global `isNaN` and `isFinite` are not in the realm                                                              | #441  |
| `test/built-ins/Number/prototype/toString`                            | 1     | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Number/prototype/valueOf`                             | 1     | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Object`                                               | 2     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/Object`                                               | 1     | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Object`                                               | 1     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/Object`                                               | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/Object/assign`                                        | 4     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/Object/create`                                        | 12    | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Object/create`                                        | 11    | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/built-ins/Object/create`                                        | 10    | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/Object/defineProperties`                              | 12    | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Object/defineProperties`                              | 12    | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/built-ins/Object/defineProperties`                              | 10    | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/Object/defineProperties`                              | 1     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/Object/defineProperty`                                | 26    | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Object/defineProperty`                                | 19    | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/built-ins/Object/defineProperty`                                | 11    | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/Object/entries`                                       | 1     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/Object/freeze`                                        | 4     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/Object/freeze`                                        | 1     | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Object/freeze`                                        | 1     | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/built-ins/Object/getOwnPropertyDescriptor`                      | 47    | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Object/getOwnPropertyDescriptor`                      | 11    | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/Object/getOwnPropertyDescriptor`                      | 11    | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/built-ins/Object/getOwnPropertyDescriptor`                      | 9     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                          | #434  |
| `test/built-ins/Object/getOwnPropertyDescriptor`                      | 1     | builtin      | `Math.random` is absent                                                                                             | #445  |
| `test/built-ins/Object/getOwnPropertyDescriptors`                     | 3     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/Object/getOwnPropertyDescriptors`                     | 1     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/Object/getOwnPropertyNames`                           | 4     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/Object/getOwnPropertyNames`                           | 1     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/Object/getOwnPropertySymbols`                         | 4     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/Object/getPrototypeOf`                                | 2     | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Object/getPrototypeOf`                                | 2     | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/built-ins/Object/getPrototypeOf`                                | 1     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/Object/internals/DefineOwnProperty`                   | 3     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/Object/isExtensible`                                  | 2     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/Object/isExtensible`                                  | 2     | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Object/isExtensible`                                  | 2     | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/built-ins/Object/isFrozen`                                      | 2     | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Object/isFrozen`                                      | 2     | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/built-ins/Object/isFrozen`                                      | 1     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/Object/isFrozen`                                      | 1     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/Object/isSealed`                                      | 2     | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Object/isSealed`                                      | 2     | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/built-ins/Object/isSealed`                                      | 1     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/Object/isSealed`                                      | 1     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
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
| `test/built-ins/Object/prototype/toString`                            | 8     | out-of-scope | `Date`, the keyed collections, promises, and BigInt are excluded by the epic                                        | #376  |
| `test/built-ins/Object/prototype/toString`                            | 3     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/Object/prototype/toString`                            | 2     | builtin      | `%IteratorPrototype%` has no `@@toStringTag`, so an iterator tags as `[object Object]`                              | #532  |
| `test/built-ins/Object/seal`                                          | 14    | out-of-scope | typed arrays and their buffers are excluded by the epic                                                             | #376  |
| `test/built-ins/Object/seal`                                          | 7     | out-of-scope | the keyed collections and promises are excluded by the epic                                                         | #376  |
| `test/built-ins/Object/seal`                                          | 5     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/Object/seal`                                          | 3     | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/Object/seal`                                          | 3     | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/built-ins/Object/seal`                                          | 1     | out-of-scope | the `Function` constructor is excluded by the epic                                                                  | #376  |
| `test/built-ins/Object/setPrototypeOf`                                | 1     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/Object/values`                                        | 2     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/String`                                               | 2     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/String`                                               | 2     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/String`                                               | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/String/prototype/charAt`                              | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/String/prototype/charCodeAt`                          | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/String/prototype/indexOf`                             | 2     | bug          | a non-callable `@@toPrimitive` handler falls back to OrdinaryToPrimitive instead of throwing                        | #516  |
| `test/built-ins/String/prototype/indexOf`                             | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/built-ins/String/prototype/localeCompare`                       | 1     | builtin      | Lean has no Unicode character database: case mapping is ASCII-only and `normalize` answers its input                | #518  |
| `test/built-ins/String/prototype/match`                               | 27    | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/built-ins/String/prototype/match`                               | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/String/prototype/matchAll`                            | 12    | out-of-scope | `matchAll` needs `RegExp`, which is excluded by the epic                                                            | #376  |
| `test/built-ins/String/prototype/normalize`                           | 3     | builtin      | Lean has no Unicode character database: case mapping is ASCII-only and `normalize` answers its input                | #518  |
| `test/built-ins/String/prototype/replace`                             | 2     | builtin      | the `@@split`, `@@replace`, and `@@match` protocol lookups are absent from the `String` methods                     | #523  |
| `test/built-ins/String/prototype/replace`                             | 2     | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/built-ins/String/prototype/replaceAll`                          | 5     | builtin      | the `@@split`, `@@replace`, and `@@match` protocol lookups are absent from the `String` methods                     | #523  |
| `test/built-ins/String/prototype/search`                              | 31    | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/built-ins/String/prototype/search`                              | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/String/prototype/split`                               | 13    | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/built-ins/String/prototype/split`                               | 3     | builtin      | the `@@split`, `@@replace`, and `@@match` protocol lookups are absent from the `String` methods                     | #523  |
| `test/built-ins/String/prototype/split`                               | 1     | builtin      | there is no global object                                                                                           | #487  |
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
| `test/built-ins/SuppressedError`                                      | 13    | out-of-scope | explicit resource management is excluded by the epic                                                                | #376  |
| `test/built-ins/SuppressedError`                                      | 1     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/SuppressedError/prototype`                            | 6     | out-of-scope | explicit resource management is excluded by the epic                                                                | #376  |
| `test/built-ins/Symbol`                                               | 1     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/Symbol`                                               | 1     | out-of-scope | `isConstructor.js` needs `Reflect.construct`                                                                        | #376  |
| `test/built-ins/Symbol/asyncDispose`                                  | 2     | out-of-scope | explicit resource management is excluded by the epic                                                                | #376  |
| `test/built-ins/Symbol/dispose`                                       | 2     | out-of-scope | explicit resource management is excluded by the epic                                                                | #376  |
| `test/built-ins/Symbol/prototype/description`                         | 1     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/built-ins/Symbol/species`                                       | 1     | out-of-scope | regular expressions are excluded by the epic                                                                        | #376  |
| `test/built-ins/Symbol/species`                                       | 1     | out-of-scope | the keyed collections and promises are excluded by the epic                                                         | #376  |
| `test/built-ins/ThrowTypeError`                                       | 2     | bug          | `%ThrowTypeError%` is extensible where 10.2.4.1 makes it frozen                                                     | #512  |
| `test/built-ins/ThrowTypeError`                                       | 1     | builtin      | `Function.prototype.caller` and `arguments` are the `%ThrowTypeError%` accessors                                    | #487  |
| `test/built-ins/parseFloat`                                           | 2     | builtin      | there is no global object                                                                                           | #487  |
| `test/built-ins/parseInt`                                             | 2     | builtin      | there is no global object                                                                                           | #487  |
| `test/harness`                                                        | 6     | builtin      | there is no global object                                                                                           | #487  |
| `test/harness`                                                        | 4     | out-of-scope | typed arrays and their buffers are excluded by the epic                                                             | #376  |
| `test/harness`                                                        | 1     | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/language/arguments-object`                                      | 2     | out-of-scope | an early-error test that reaches for `eval`                                                                         | #376  |
| `test/language/expressions/addition`                                  | 5     | builtin      | the global `isNaN` and `isFinite` are not in the realm                                                              | #441  |
| `test/language/expressions/addition`                                  | 1     | out-of-scope | `Date` is excluded by the epic                                                                                      | #376  |
| `test/language/expressions/addition`                                  | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/expressions/arrow-function`                            | 1     | builtin      | `Function.prototype.caller` and `arguments` are the `%ThrowTypeError%` accessors                                    | #487  |
| `test/language/expressions/arrow-function/arrow`                      | 4     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/expressions/assignment`                                | 1     | protocol     | the bridge drops the parentheses that keep NamedEvaluation from naming a function                                   | #499  |
| `test/language/expressions/assignment/destructuring`                  | 2     | bug          | a destructuring target's property reference is evaluated in the wrong order                                         | #533  |
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
| `test/language/expressions/modulus`                                   | 1     | bug          | the left operand is not converted fully before the right one                                                        | #436  |
| `test/language/expressions/modulus`                                   | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/expressions/multiplication`                            | 10    | builtin      | the global `isNaN` and `isFinite` are not in the realm                                                              | #441  |
| `test/language/expressions/multiplication`                            | 1     | bug          | the left operand is not converted fully before the right one                                                        | #436  |
| `test/language/expressions/multiplication`                            | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/expressions/object`                                    | 8     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/expressions/object`                                    | 3     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/language/expressions/object/dstr`                               | 3     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/language/expressions/strict-does-not-equals`                    | 2     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/expressions/strict-equals`                             | 2     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/expressions/subtraction`                               | 9     | builtin      | the global `isNaN` and `isFinite` are not in the realm                                                              | #441  |
| `test/language/expressions/subtraction`                               | 1     | bug          | the left operand is not converted fully before the right one                                                        | #436  |
| `test/language/expressions/subtraction`                               | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/expressions/tagged-template`                           | 3     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/expressions/template-literal`                          | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/expressions/unary-minus`                               | 3     | builtin      | the global `isNaN` and `isFinite` are not in the realm                                                              | #441  |
| `test/language/expressions/unary-minus`                               | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/expressions/unary-plus`                                | 6     | builtin      | the global `isNaN` and `isFinite` are not in the realm                                                              | #441  |
| `test/language/expressions/unary-plus`                                | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/function-code`                                         | 6     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/statements/break`                                      | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/statements/class`                                      | 1     | builtin      | `Function.prototype.caller` and `arguments` are the `%ThrowTypeError%` accessors                                    | #487  |
| `test/language/statements/class`                                      | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
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
| `test/language/statements/for-of`                                     | 2     | out-of-scope | explicit resource management (`using`) is excluded by the epic                                                      | #376  |
| `test/language/statements/for-of`                                     | 1     | out-of-scope | `Proxy` and `Reflect` are excluded by the epic                                                                      | #376  |
| `test/language/statements/function`                                   | 4     | builtin      | `Function.prototype.caller` and `arguments` are the `%ThrowTypeError%` accessors                                    | #487  |
| `test/language/statements/function`                                   | 3     | out-of-scope | an early-error test that reaches for `eval`                                                                         | #376  |
| `test/language/statements/function`                                   | 2     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                          | #434  |
| `test/language/statements/function`                                   | 2     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/statements/function`                                   | 1     | out-of-scope | the `Function` constructor is excluded by the epic                                                                  | #376  |
| `test/language/statements/if`                                         | 9     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/statements/labeled`                                    | 2     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/statements/let`                                        | 1     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/statements/return`                                     | 1     | builtin      | the transcendental `Math` members, `sumPrecise`, and `f16round` are absent                                          | #434  |
| `test/language/statements/switch`                                     | 21    | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/statements/switch`                                     | 1     | builtin      | the global `isNaN` and `isFinite` are not in the realm                                                              | #441  |
| `test/language/statements/try`                                        | 12    | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/statements/try`                                        | 2     | out-of-scope | an early-error test that reaches for `eval`                                                                         | #376  |
| `test/language/statements/variable`                                   | 7     | out-of-scope | an early-error test that reaches for `eval`                                                                         | #376  |
| `test/language/statements/variable`                                   | 6     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
| `test/language/statements/variable`                                   | 2     | builtin      | there is no global object                                                                                           | #487  |
| `test/language/statements/while`                                      | 7     | out-of-scope | `eval` is excluded by the epic                                                                                      | #376  |
