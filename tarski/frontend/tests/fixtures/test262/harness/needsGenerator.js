// A harness file outside the fragment, so that an `includes` of it makes
// the test that names it unsupported rather than failed.
/*---
description: |
    A helper written with a generator, which the evaluator does not have.
defines: [kindOf]
---*/

const $fakeNeedsGenerator = "fake: exit 3 unsupported: FunctionDeclaration generator";

function* each(x) {
  yield x;
}

function kindOf(x) {
  let kind = "?";
  for (const c of each(x)) {
    kind = typeof c === "number" ? "n" : "?";
  }
  return kind;
}
