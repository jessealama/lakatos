"use strict";
const xs = [3, 1, 2];
xs.sort((a, b) => a - b);
const ys = xs.map((x) => x * 2).filter((x) => x > 2);
ys.length === 2 &&
  ys.indexOf(6) === 1 &&
  [1, [2, [3]]].flat(Infinity).length === 3 &&
  Array.from({ length: 2 }, (_, i) => i).join() === "0,1";
