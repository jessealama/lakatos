# The failure list for the PR-gated slice

Written 2026-09-14 against test262 at `419d3e0a2273ba01a3bfcbec423f2801425b8e93`
(`tarski/test262/pin.json`), from one run of

```bash
node ../dist/tarski/frontend/src/test262/cli.js --slice-file test262/slice.txt
```

Every failing test in `tarski/test262/slice.txt` is classified here, and
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

`owner` is the issue the row waits on. Nothing here waits on #383: no
failure in the slice is caused by the statements and operators this issue
added, which is what the `for`, `switch`, `var`, and update tests under
`tarski/Test/Tarski/` check directly.

One divergence found while classifying is not the proximate cause of any
row and so has none: `applyCoercing` runs ToPrimitive on both operands
before ToNumber on either, where 13.15.3 converts the left operand fully
first for every operator but `+`. It is unobservable without a Symbol or a
BigInt operand, and it is filed as #436. The five `order-of-evaluation`
tests that pin it fail today for want of `Symbol`, so they are classified
against #392.

## The table

| directory                                          | fails | class        | why                                                                                                   | owner |
| -------------------------------------------------- | ----- | ------------ | ----------------------------------------------------------------------------------------------------- | ----- |
| `test/harness`                                     | 5     | out-of-scope | typed arrays, `Date`, and the other library objects are excluded by the epic                          | #376  |
| `test/harness`                                     | 4     | builtin      | the harness's `compareArray.format` calls `Array.prototype.map`                                       | #390  |
| `test/harness`                                     | 3     | builtin      | there is no global object, so `globalThis` is unbound                                                 | #389  |
| `test/harness`                                     | 2     | builtin      | `String({})` needs `Object.prototype.toString`, and so does the harness's fallback                    | #389  |
| `test/harness`                                     | 1     | builtin      | `Number`, `Boolean`, `Math`, and the global numeric functions are not in the realm                    | #382  |
| `test/harness`                                     | 1     | builtin      | `Array.prototype.map` is absent, so the harness's `compareArray.format` reads `.call` off `undefined` | #390  |
| `test/harness`                                     | 1     | builtin      | `String.prototype.indexOf` is absent                                                                  | #391  |
| `test/harness`                                     | 1     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                        | #376  |
| `test/harness`                                     | 1     | out-of-scope | `getWellKnownIntrinsicObject` reaches the intrinsics through `Function`                               | #376  |
| `test/language/expressions/addition`               | 18    | builtin      | `Number`, `Boolean`, `Math`, and the global numeric functions are not in the realm                    | #382  |
| `test/language/expressions/addition`               | 6     | builtin      | `Symbol` is not in the realm                                                                          | #392  |
| `test/language/expressions/addition`               | 4     | builtin      | `new String` needs the String wrapper object                                                          | #391  |
| `test/language/expressions/addition`               | 2     | builtin      | `Object.prototype.toString` and `valueOf` are not on the prototype yet                                | #389  |
| `test/language/expressions/addition`               | 1     | builtin      | the ToNumeric step it pins needs `Symbol`; the order divergence behind it is #436                     | #392  |
| `test/language/expressions/addition`               | 1     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                        | #376  |
| `test/language/expressions/addition`               | 1     | out-of-scope | typed arrays, `Date`, and the other library objects are excluded by the epic                          | #376  |
| `test/language/expressions/assignment`             | 4     | builtin      | `Object.defineProperty` and property attributes are absent                                            | #389  |
| `test/language/expressions/assignment`             | 2     | builtin      | `Math` is not in the realm                                                                            | #382  |
| `test/language/expressions/assignment`             | 2     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                        | #376  |
| `test/language/expressions/conditional`            | 5     | builtin      | `Number`, `Boolean`, `Math`, and the global numeric functions are not in the realm                    | #382  |
| `test/language/expressions/conditional`            | 2     | builtin      | `new String` needs the String wrapper object                                                          | #391  |
| `test/language/expressions/conditional`            | 1     | builtin      | `Symbol` is not in the realm                                                                          | #392  |
| `test/language/expressions/conditional`            | 1     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                        | #376  |
| `test/language/expressions/division`               | 21    | builtin      | `Number`, `Boolean`, `Math`, and the global numeric functions are not in the realm                    | #382  |
| `test/language/expressions/division`               | 3     | bug          | ToNumber of a string is a placeholder that answers NaN                                                | #388  |
| `test/language/expressions/division`               | 2     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                        | #376  |
| `test/language/expressions/division`               | 1     | builtin      | the ToNumeric step it pins needs `Symbol`; the order divergence behind it is #436                     | #392  |
| `test/language/expressions/greater-than`           | 16    | builtin      | `Number`, `Boolean`, `Math`, and the global numeric functions are not in the realm                    | #382  |
| `test/language/expressions/greater-than`           | 3     | builtin      | `new String` needs the String wrapper object                                                          | #391  |
| `test/language/expressions/greater-than`           | 1     | bug          | ToNumber of a string is a placeholder that answers NaN                                                | #388  |
| `test/language/expressions/greater-than`           | 1     | bug          | a Lean `String` is code points, so the relational order is not UTF-16 code-unit order                 | #391  |
| `test/language/expressions/greater-than`           | 1     | builtin      | `Object.prototype.toString` and `valueOf` are not on the prototype yet                                | #389  |
| `test/language/expressions/greater-than`           | 1     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                        | #376  |
| `test/language/expressions/greater-than-or-equal`  | 15    | builtin      | `Number`, `Boolean`, `Math`, and the global numeric functions are not in the realm                    | #382  |
| `test/language/expressions/greater-than-or-equal`  | 3     | bug          | ToNumber of a string is a placeholder that answers NaN                                                | #388  |
| `test/language/expressions/greater-than-or-equal`  | 2     | builtin      | `new String` needs the String wrapper object                                                          | #391  |
| `test/language/expressions/greater-than-or-equal`  | 1     | bug          | a Lean `String` is code points, so the relational order is not UTF-16 code-unit order                 | #391  |
| `test/language/expressions/greater-than-or-equal`  | 1     | builtin      | `Object.prototype.toString` and `valueOf` are not on the prototype yet                                | #389  |
| `test/language/expressions/greater-than-or-equal`  | 1     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                        | #376  |
| `test/language/expressions/less-than`              | 16    | builtin      | `Number`, `Boolean`, `Math`, and the global numeric functions are not in the realm                    | #382  |
| `test/language/expressions/less-than`              | 3     | builtin      | `new String` needs the String wrapper object                                                          | #391  |
| `test/language/expressions/less-than`              | 1     | bug          | ToNumber of a string is a placeholder that answers NaN                                                | #388  |
| `test/language/expressions/less-than`              | 1     | bug          | a Lean `String` is code points, so the relational order is not UTF-16 code-unit order                 | #391  |
| `test/language/expressions/less-than`              | 1     | builtin      | `Object.prototype.toString` and `valueOf` are not on the prototype yet                                | #389  |
| `test/language/expressions/less-than`              | 1     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                        | #376  |
| `test/language/expressions/less-than-or-equal`     | 15    | builtin      | `Number`, `Boolean`, `Math`, and the global numeric functions are not in the realm                    | #382  |
| `test/language/expressions/less-than-or-equal`     | 3     | bug          | ToNumber of a string is a placeholder that answers NaN                                                | #388  |
| `test/language/expressions/less-than-or-equal`     | 2     | builtin      | `new String` needs the String wrapper object                                                          | #391  |
| `test/language/expressions/less-than-or-equal`     | 1     | bug          | a Lean `String` is code points, so the relational order is not UTF-16 code-unit order                 | #391  |
| `test/language/expressions/less-than-or-equal`     | 1     | builtin      | `Object.prototype.toString` and `valueOf` are not on the prototype yet                                | #389  |
| `test/language/expressions/less-than-or-equal`     | 1     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                        | #376  |
| `test/language/expressions/logical-and`            | 4     | builtin      | `Number`, `Boolean`, `Math`, and the global numeric functions are not in the realm                    | #382  |
| `test/language/expressions/logical-and`            | 1     | builtin      | `new String` needs the String wrapper object                                                          | #391  |
| `test/language/expressions/logical-and`            | 1     | builtin      | `Symbol` is not in the realm                                                                          | #392  |
| `test/language/expressions/logical-and`            | 1     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                        | #376  |
| `test/language/expressions/logical-not`            | 4     | builtin      | `Number`, `Boolean`, `Math`, and the global numeric functions are not in the realm                    | #382  |
| `test/language/expressions/logical-not`            | 2     | builtin      | `new String` needs the String wrapper object                                                          | #391  |
| `test/language/expressions/logical-not`            | 2     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                        | #376  |
| `test/language/expressions/logical-not`            | 1     | builtin      | `Symbol` is not in the realm                                                                          | #392  |
| `test/language/expressions/logical-or`             | 5     | builtin      | `Number`, `Boolean`, `Math`, and the global numeric functions are not in the realm                    | #382  |
| `test/language/expressions/logical-or`             | 2     | builtin      | `new String` needs the String wrapper object                                                          | #391  |
| `test/language/expressions/logical-or`             | 1     | builtin      | `Symbol` is not in the realm                                                                          | #392  |
| `test/language/expressions/logical-or`             | 1     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                        | #376  |
| `test/language/expressions/modulus`                | 19    | builtin      | `Number`, `Boolean`, `Math`, and the global numeric functions are not in the realm                    | #382  |
| `test/language/expressions/modulus`                | 3     | bug          | ToNumber of a string is a placeholder that answers NaN                                                | #388  |
| `test/language/expressions/modulus`                | 1     | builtin      | the ToNumeric step it pins needs `Symbol`; the order divergence behind it is #436                     | #392  |
| `test/language/expressions/modulus`                | 1     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                        | #376  |
| `test/language/expressions/multiplication`         | 19    | builtin      | `Number`, `Boolean`, `Math`, and the global numeric functions are not in the realm                    | #382  |
| `test/language/expressions/multiplication`         | 4     | bug          | ToNumber of a string is a placeholder that answers NaN                                                | #388  |
| `test/language/expressions/multiplication`         | 1     | builtin      | the ToNumeric step it pins needs `Symbol`; the order divergence behind it is #436                     | #392  |
| `test/language/expressions/multiplication`         | 1     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                        | #376  |
| `test/language/expressions/strict-does-not-equals` | 5     | builtin      | `Number`, `Boolean`, `Math`, and the global numeric functions are not in the realm                    | #382  |
| `test/language/expressions/strict-does-not-equals` | 2     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                        | #376  |
| `test/language/expressions/strict-does-not-equals` | 1     | builtin      | `Object(v)` on a primitive needs a wrapper object                                                     | #391  |
| `test/language/expressions/strict-does-not-equals` | 1     | builtin      | `new String` needs the String wrapper object                                                          | #391  |
| `test/language/expressions/strict-equals`          | 5     | builtin      | `Number`, `Boolean`, `Math`, and the global numeric functions are not in the realm                    | #382  |
| `test/language/expressions/strict-equals`          | 2     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                        | #376  |
| `test/language/expressions/strict-equals`          | 1     | builtin      | `Object(v)` on a primitive needs a wrapper object                                                     | #391  |
| `test/language/expressions/strict-equals`          | 1     | builtin      | `new String` needs the String wrapper object                                                          | #391  |
| `test/language/expressions/subtraction`            | 18    | builtin      | `Number`, `Boolean`, `Math`, and the global numeric functions are not in the realm                    | #382  |
| `test/language/expressions/subtraction`            | 4     | bug          | ToNumber of a string is a placeholder that answers NaN                                                | #388  |
| `test/language/expressions/subtraction`            | 1     | builtin      | the ToNumeric step it pins needs `Symbol`; the order divergence behind it is #436                     | #392  |
| `test/language/expressions/subtraction`            | 1     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                        | #376  |
| `test/language/expressions/unary-minus`            | 5     | builtin      | `Number`, `Boolean`, `Math`, and the global numeric functions are not in the realm                    | #382  |
| `test/language/expressions/unary-minus`            | 2     | bug          | ToNumber of a string is a placeholder that answers NaN                                                | #388  |
| `test/language/expressions/unary-minus`            | 1     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                        | #376  |
| `test/language/expressions/unary-plus`             | 9     | builtin      | `Number`, `Boolean`, `Math`, and the global numeric functions are not in the realm                    | #382  |
| `test/language/expressions/unary-plus`             | 2     | bug          | ToNumber of a string is a placeholder that answers NaN                                                | #388  |
| `test/language/expressions/unary-plus`             | 1     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                        | #376  |
| `test/language/statements/const`                   | 1     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                        | #376  |
| `test/language/statements/for`                     | 7     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                        | #376  |
| `test/language/statements/for`                     | 5     | builtin      | `Number`, `Boolean`, `Math`, and the global numeric functions are not in the realm                    | #382  |
| `test/language/statements/for`                     | 4     | builtin      | `new String` needs the String wrapper object                                                          | #391  |
| `test/language/statements/if`                      | 9     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                        | #376  |
| `test/language/statements/if`                      | 1     | builtin      | `Number`, `Boolean`, `Math`, and the global numeric functions are not in the realm                    | #382  |
| `test/language/statements/let`                     | 1     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                        | #376  |
| `test/language/statements/return`                  | 1     | builtin      | `Number`, `Boolean`, `Math`, and the global numeric functions are not in the realm                    | #382  |
| `test/language/statements/throw`                   | 1     | builtin      | `Array.prototype.concat` is absent                                                                    | #390  |
| `test/language/statements/variable`                | 17    | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                        | #376  |
| `test/language/statements/variable`                | 1     | builtin      | a top-level `this` is `undefined` for want of a global object                                         | #389  |
| `test/language/statements/while`                   | 7     | out-of-scope | `eval` and the `Function` constructor are excluded by the epic                                        | #376  |

## The unsupported histogram

From the same run, for the record: what the decoder refused, by kind and by
count. It is not tested — only the table above is — but it is what names
the next slice to land.

```
  VariableDeclarationList  214
  VariableStatement  213
  DeleteExpression  106
  BinaryExpression ,  85
  BigIntLiteral  72
  FunctionExpression generator  69
  FunctionDeclaration generator  35
  AssignmentExpression target  28
  ShorthandPropertyAssignment  18
  GetAccessor  13
  SpreadElement  13
  OmittedExpression  12
  TemplateExpression  11
  ClassDeclaration  8
  ComputedPropertyName  6
  BinaryExpression !=  5
  ForInStatement  5
  SetAccessor  5
  SpreadAssignment  4
  BinaryExpression ==  3
  BinaryExpression in  3
  FunctionExpression async  3
  MethodDeclaration  3
  BinaryExpression &  2
  ForOfStatement  2
  $262.createRealm  1
  $262.detachArrayBuffer  1
  ArrowFunctionExpression async  1
  AssignmentExpression >>>=  1
  BinaryExpression >>  1
  DoStatement  1
  LogicalExpression ??  1
  Property numeric key  1
  RegularExpressionLiteral  1
```
