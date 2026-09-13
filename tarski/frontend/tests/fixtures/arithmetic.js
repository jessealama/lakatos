"use strict";
const a = 7 % 3;
const b = -a + +2.5;
const c = a / 0;
!(b >= c) === (b < c);
