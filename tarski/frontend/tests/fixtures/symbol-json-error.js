"use strict";
const s = Symbol("k");
const o = { [s]: 1, a: [1, { b: null }] };
JSON.stringify(o) === '{"a":[1,{"b":null}]}' &&
  JSON.parse('{"x":[1,2]}').x[1] === 2 &&
  typeof s === "symbol" &&
  s.description === "k" &&
  Symbol.for("q") === Symbol.for("q") &&
  new TypeError("m", { cause: 1 }).cause === 1;
