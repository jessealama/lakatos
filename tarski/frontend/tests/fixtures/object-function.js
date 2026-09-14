"use strict";
const o = {};
Object.defineProperty(o, "x", {
  value: 1,
  writable: false,
  enumerable: false,
  configurable: false,
});
let threw = false;
try {
  o.x = 2;
} catch (e) {
  threw = e instanceof TypeError;
}
const d = Object.getOwnPropertyDescriptor(o, "x");
function f(a, b) {
  return this.k + a + b;
}
const order = [];
const keyed = {};
keyed.b = 1;
keyed[2] = 1;
keyed.a = 1;
keyed[1] = 1;
for (const k in keyed) {
  order.push(k);
}
delete keyed.a;
threw &&
  d.writable === false &&
  Object.keys(o).length === 0 &&
  f.call({ k: 1 }, 2, 3) === 6 &&
  f.bind({ k: 10 })(1, 1) === 12 &&
  order.join() === "1,2,b,a" &&
  !("a" in keyed) &&
  Object.getOwnPropertyNames(f).join() === "length,name,prototype" &&
  Object.prototype.toString.call([]) === "[object Array]" &&
  Object.isFrozen(Object.freeze({}));
