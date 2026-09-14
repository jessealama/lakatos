# test262 results

The evaluator run against test262 at `419d3e0a2273ba01a3bfcbec423f2801425b8e93`, over `test/language`, `test/built-ins`, `test/intl402`, with a 10-second per-test timeout. Written by `sh scripts/test262-full.sh`; not edited by hand.

## By directory

| directory                                     | tests | pass | fail | unsupported | timeout | harness-error | not-run |
| --------------------------------------------- | ----: | ---: | ---: | ----------: | ------: | ------------: | ------: |
| test/built-ins/AbstractModuleSource           |     8 |    0 |    0 |           0 |       0 |             0 |       8 |
| test/built-ins/AggregateError                 |    25 |    0 |    0 |          25 |       0 |             0 |       0 |
| test/built-ins/Array                          |  3082 |    0 |    0 |        2958 |       0 |             0 |     124 |
| test/built-ins/ArrayBuffer                    |   221 |    0 |    0 |         221 |       0 |             0 |       0 |
| test/built-ins/ArrayIteratorPrototype         |    27 |    0 |    0 |          19 |       0 |             0 |       8 |
| test/built-ins/AsyncDisposableStack           |   104 |    0 |    0 |          75 |       0 |             0 |      29 |
| test/built-ins/AsyncFromSyncIteratorPrototype |    38 |    0 |    0 |           1 |       0 |             0 |      37 |
| test/built-ins/AsyncFunction                  |    18 |    0 |    0 |          18 |       0 |             0 |       0 |
| test/built-ins/AsyncGeneratorFunction         |    23 |    0 |    0 |          17 |       0 |             0 |       6 |
| test/built-ins/AsyncGeneratorPrototype        |    48 |    0 |    0 |          13 |       0 |             0 |      35 |
| test/built-ins/AsyncIteratorPrototype         |    13 |    0 |    0 |           9 |       0 |             0 |       4 |
| test/built-ins/Atomics                        |   389 |    0 |    0 |         324 |       0 |             0 |      65 |
| test/built-ins/BigInt                         |    77 |    0 |    0 |          77 |       0 |             0 |       0 |
| test/built-ins/Boolean                        |    51 |    0 |    0 |          51 |       0 |             0 |       0 |
| test/built-ins/DataView                       |   561 |    0 |    0 |         561 |       0 |             0 |       0 |
| test/built-ins/Date                           |   594 |    0 |    0 |         594 |       0 |             0 |       0 |
| test/built-ins/DisposableStack                |    93 |    0 |    0 |          93 |       0 |             0 |       0 |
| test/built-ins/Error                          |    93 |    0 |    0 |          93 |       0 |             0 |       0 |
| test/built-ins/FinalizationRegistry           |    47 |    0 |    0 |          47 |       0 |             0 |       0 |
| test/built-ins/Function                       |   509 |    0 |    0 |         421 |       0 |             0 |      88 |
| test/built-ins/GeneratorFunction              |    23 |    0 |    0 |          23 |       0 |             0 |       0 |
| test/built-ins/GeneratorPrototype             |    61 |    0 |    0 |          61 |       0 |             0 |       0 |
| test/built-ins/Infinity                       |     6 |    0 |    0 |           4 |       0 |             0 |       2 |
| test/built-ins/Iterator                       |   654 |    0 |    0 |         654 |       0 |             0 |       0 |
| test/built-ins/JSON                           |   165 |    0 |    0 |         165 |       0 |             0 |       0 |
| test/built-ins/Map                            |   204 |    0 |    0 |         203 |       0 |             0 |       1 |
| test/built-ins/MapIteratorPrototype           |    11 |    0 |    0 |          11 |       0 |             0 |       0 |
| test/built-ins/Math                           |   327 |    0 |    0 |         327 |       0 |             0 |       0 |
| test/built-ins/NaN                            |     6 |    0 |    0 |           4 |       0 |             0 |       2 |
| test/built-ins/NativeErrors                   |    94 |    0 |    0 |          94 |       0 |             0 |       0 |
| test/built-ins/Number                         |   340 |    0 |    0 |         340 |       0 |             0 |       0 |
| test/built-ins/Object                         |  3411 |    0 |    0 |        3400 |       0 |             0 |      11 |
| test/built-ins/Promise                        |   732 |    0 |    0 |         316 |       0 |             0 |     416 |
| test/built-ins/Proxy                          |   311 |    0 |    0 |         299 |       0 |             0 |      12 |
| test/built-ins/Reflect                        |   153 |    0 |    0 |         153 |       0 |             0 |       0 |
| test/built-ins/RegExp                         |  1687 |    0 |    0 |        1686 |       0 |             0 |       1 |
| test/built-ins/RegExpStringIteratorPrototype  |    17 |    0 |    0 |          17 |       0 |             0 |       0 |
| test/built-ins/Set                            |   383 |    0 |    0 |         382 |       0 |             0 |       1 |
| test/built-ins/SetIteratorPrototype           |    11 |    0 |    0 |          11 |       0 |             0 |       0 |
| test/built-ins/ShadowRealm                    |    64 |    0 |    0 |          60 |       0 |             0 |       4 |
| test/built-ins/SharedArrayBuffer              |   104 |    0 |    0 |         104 |       0 |             0 |       0 |
| test/built-ins/String                         |  1223 |    0 |    0 |        1220 |       0 |             0 |       3 |
| test/built-ins/StringIteratorPrototype        |     7 |    0 |    0 |           7 |       0 |             0 |       0 |
| test/built-ins/SuppressedError                |    22 |    0 |    0 |          22 |       0 |             0 |       0 |
| test/built-ins/Symbol                         |    98 |    0 |    0 |          96 |       0 |             0 |       2 |
| test/built-ins/Temporal                       |  4605 |    0 |    0 |        4605 |       0 |             0 |       0 |
| test/built-ins/ThrowTypeError                 |    14 |    0 |    0 |          14 |       0 |             0 |       0 |
| test/built-ins/TypedArray                     |  1446 |    0 |    0 |        1438 |       0 |             0 |       8 |
| test/built-ins/TypedArrayConstructors         |   738 |    0 |    0 |         722 |       0 |             0 |      16 |
| test/built-ins/Uint8Array                     |    70 |    0 |    0 |          70 |       0 |             0 |       0 |
| test/built-ins/WeakMap                        |   141 |    0 |    0 |         141 |       0 |             0 |       0 |
| test/built-ins/WeakRef                        |    29 |    0 |    0 |          29 |       0 |             0 |       0 |
| test/built-ins/WeakSet                        |    85 |    0 |    0 |          85 |       0 |             0 |       0 |
| test/built-ins/decodeURI                      |    55 |    0 |    0 |          55 |       0 |             0 |       0 |
| test/built-ins/decodeURIComponent             |    56 |    0 |    0 |          56 |       0 |             0 |       0 |
| test/built-ins/encodeURI                      |    31 |    0 |    0 |          31 |       0 |             0 |       0 |
| test/built-ins/encodeURIComponent             |    31 |    0 |    0 |          31 |       0 |             0 |       0 |
| test/built-ins/eval                           |    10 |    0 |    0 |          10 |       0 |             0 |       0 |
| test/built-ins/global                         |    29 |    0 |    0 |          29 |       0 |             0 |       0 |
| test/built-ins/isFinite                       |    15 |    0 |    0 |          15 |       0 |             0 |       0 |
| test/built-ins/isNaN                          |    15 |    0 |    0 |          15 |       0 |             0 |       0 |
| test/built-ins/parseFloat                     |    54 |    0 |    0 |          54 |       0 |             0 |       0 |
| test/built-ins/parseInt                       |    55 |    0 |    0 |          55 |       0 |             0 |       0 |
| test/built-ins/undefined                      |     8 |    0 |    0 |           5 |       0 |             0 |       3 |
| test/language/arguments-object                |   262 |    0 |    0 |         145 |       0 |             0 |     117 |
| test/language/asi                             |    67 |    0 |    0 |          67 |       0 |             0 |       0 |
| test/language/block-scope                     |    43 |    0 |    0 |          43 |       0 |             0 |       0 |
| test/language/comments                        |    27 |    0 |    0 |          21 |       0 |             0 |       6 |
| test/language/computed-property-names         |    48 |    0 |    0 |          48 |       0 |             0 |       0 |
| test/language/destructuring                   |    19 |    0 |    0 |          18 |       0 |             0 |       1 |
| test/language/directive-prologue              |    51 |    0 |    0 |           0 |       0 |             0 |      51 |
| test/language/eval-code                       |   347 |    0 |    0 |         123 |       0 |             0 |     224 |
| test/language/expressions                     |  9068 |    0 |    0 |        6404 |       0 |             3 |    2661 |
| test/language/function-code                   |   217 |    0 |    0 |         108 |       0 |             0 |     109 |
| test/language/future-reserved-words           |    29 |    0 |    0 |          22 |       0 |             0 |       7 |
| test/language/global-code                     |    28 |    0 |    0 |          23 |       0 |             0 |       5 |
| test/language/identifier-resolution           |    13 |    0 |    0 |           8 |       0 |             0 |       5 |
| test/language/identifiers                     |   152 |    0 |    0 |         136 |       0 |            16 |       0 |
| test/language/import                          |   116 |    0 |    0 |           0 |       0 |             0 |     116 |
| test/language/line-terminators                |    24 |    0 |    0 |          24 |       0 |             0 |       0 |
| test/language/literals                        |   215 |    0 |    0 |         210 |       0 |             0 |       5 |
| test/language/module-code                     |   402 |    0 |    0 |           1 |       0 |             0 |     401 |
| test/language/punctuators                     |     1 |    0 |    0 |           1 |       0 |             0 |       0 |
| test/language/reserved-words                  |    14 |    0 |    0 |          14 |       0 |             0 |       0 |
| test/language/rest-parameters                 |    10 |    0 |    0 |          10 |       0 |             0 |       0 |
| test/language/source-text                     |     1 |    0 |    0 |           1 |       0 |             0 |       0 |
| test/language/statementList                   |    80 |    0 |    0 |          80 |       0 |             0 |       0 |
| test/language/statements                      |  7841 |    0 |    0 |        4958 |       0 |             3 |    2880 |
| test/language/types                           |   102 |    0 |    0 |          93 |       0 |             0 |       9 |
| test/language/white-space                     |    61 |    0 |    0 |          61 |       0 |             0 |       0 |
| total                                         | 42860 |    0 |    0 |       35355 |       0 |            22 |    7483 |

## Not run and skipped

| kind                | tests | where             |
| ------------------- | ----: | ----------------- |
| noStrict            |  1624 | not-run column    |
| raw                 |     5 | not-run column    |
| async               |  5256 | not-run column    |
| module              |   598 | not-run column    |
| budget              |     0 | not-run column    |
| parse-negative      |  4646 | outside the table |
| resolution-negative |    34 | outside the table |
| intl402             |  3357 | outside the table |

## Unsupported

| kind            | tests |
| --------------- | ----: |
| SwitchStatement | 35355 |
