"use strict";
function f() {
  const before = typeof g; // "function": declarations hoist
  function g() {
    return arguments.length;
  }
  let r = "";
  outer: for (let i = 0; i < 3; i++) {
    switch (i) {
      case 1:
        continue outer;
      default:
        r = r + i;
    }
  }
  return before === "function" && g(1, 2, 3) === 3 && r === "02";
}
let tdz = false;
try {
  x;
} catch (e) {
  tdz = e instanceof ReferenceError;
}
let x = 1;
f() && tdz;
