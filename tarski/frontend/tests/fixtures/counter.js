"use strict";
function counter() {
  let n = 0;
  return { next: function () { n = n + 1; return n; } };
}
const c = counter();
c.next(); c.next();
const o = { a: 1 };
o.b = c.next();
typeof o.b === "number" && o.b === 3 && typeof c.next === "function";
