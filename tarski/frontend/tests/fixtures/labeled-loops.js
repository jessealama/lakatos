"use strict";
let i = 0;
let hits = 0;
outer: while (i < 3) {
  i = i + 1;
  let j = 0;
  while (j < 3) {
    j = j + 1;
    if (j === 2) break outer;
    hits = hits + 1;
  }
}
hits + i * 10;
