// A harness file outside the fragment, so that an `includes` of it makes
// the test that names it unsupported rather than failed.
/*---
description: |
    A helper written with `delete`, which the evaluator does not have.
defines: [kindOf]
---*/

const $fakeNeedsDelete = "fake: exit 3 unsupported: DeleteExpression";

function kindOf(x) {
  const seen = { n: x };
  delete seen.n;
  return typeof x === "number" ? "n" : "?";
}
