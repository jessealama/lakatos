// Not the suite's own assert.js: that one opens with a `switch` and goes
// on to `var`, `for`, `Object.prototype.toString.call`, and `JSON`, none
// of which the evaluator has yet (#383, #389, #392, #393). This is the
// same surface written inside the fragment, so that the fake tree can
// exercise a real pass and a real failure end to end while the real
// suite's floor stays what it is.
/*---
description: |
    assert, assert.sameValue and assert.throws, inside the fragment.
defines: [assert]
---*/

function assert(mustBeTrue, message) {
  if (mustBeTrue === true) {
    return;
  }
  if (message === undefined) {
    message = "Expected true but got " + String(mustBeTrue);
  }
  throw new Test262Error(message);
}

assert.sameValue = function (actual, expected, message) {
  if (actual === expected) {
    return;
  }
  if (message === undefined) {
    message = "";
  }
  throw new Test262Error(
    "Expected SameValue(" + String(actual) + ", " + String(expected) + ") to be true. " + message,
  );
};

assert.throws = function (expectedErrorConstructor, func, message) {
  if (message === undefined) {
    message = "";
  }
  let threw = false;
  try {
    func();
  } catch (thrown) {
    threw = true;
    if (!(thrown instanceof expectedErrorConstructor)) {
      throw new Test262Error("Threw the wrong kind of error. " + message);
    }
  }
  if (threw === false) {
    throw new Test262Error("Expected a thrown error but none was thrown. " + message);
  }
};
