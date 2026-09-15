"use strict";
const it = {
  [Symbol.iterator]() {
    let i = 0;
    return { next: () => ({ value: i, done: i++ >= 3 }) };
  },
};
let sum = 0;
for (const v of it) sum += v;
const [a, , ...rest] = [1, 2, 3, 4];
const { p, q: { r } = { r: 9 }, ...o } = { p: 1, s: 2 };
Math.max(...[1, 5, 2]) === 5 &&
  sum === 3 &&
  a === 1 &&
  rest.length === 2 &&
  p === 1 &&
  r === 9 &&
  o.s === 2;
