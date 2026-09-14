// A harness file outside the fragment, so that an `includes` of it makes
// the test that names it unsupported rather than failed.
/*---
description: |
    A helper written with `for`-`of`, which the evaluator does not have.
defines: [kindOf]
---*/

const $fakeNeedsForOf = "fake: exit 3 unsupported: ForOfStatement";

function kindOf(x) {
  let kind = "?";
  for (const c of [x]) {
    kind = typeof c === "number" ? "n" : "?";
  }
  return kind;
}
