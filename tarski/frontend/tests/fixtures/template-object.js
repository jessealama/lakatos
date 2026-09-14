"use strict";
// #395's example. The tag is spelled with `arguments` rather than the
// issue's `(strs, ...vals) =>`: a rest parameter is #394's and arrives
// as an `Unsupported` parameter, so the example verbatim does not reach
// the evaluator yet.
const k = "dyn",
  v = 2;
const o = {
  v,
  [k + "1"]: 1,
  m() {
    return this.v;
  },
  get g() {
    return 3;
  },
};
const tag = function (strs) {
  return strs.raw.join("|") + (arguments.length - 1);
};
`${o.v}-${o.dyn1}` === "2-1" &&
  o.m() === 2 &&
  o.g === 3 &&
  tag`a${1}b${2}c` === "a|b|c2";
