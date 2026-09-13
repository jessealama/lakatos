// A harness file outside the fragment, so that an `includes` of it makes
// the test that names it unsupported rather than failed.
/*---
description: |
    A helper written with a `switch`, which the evaluator does not have.
defines: [kindOf]
---*/

const $fakeNeedsSwitch = "fake: exit 3 unsupported: SwitchStatement";

function kindOf(x) {
  switch (typeof x) {
    case "number":
      return "n";
    default:
      return "?";
  }
}
