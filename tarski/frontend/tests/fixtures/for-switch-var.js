"use strict";
var total = 0;
const fs = [];
for (let i = 0; i < 3; i++) {
  fs.push(function () {
    return i;
  });
  switch (i % 2) {
    case 0:
      total += i;
      break;
    default:
      total -= 1;
  }
}
fs[0]() === 0 &&
  fs[2]() === 2 &&
  total === 1 &&
  typeof hoisted === "undefined" &&
  void 0 === undefined;
var hoisted;
