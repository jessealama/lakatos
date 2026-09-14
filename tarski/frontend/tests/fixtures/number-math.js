"use strict";
Math.fround(0.1) === 0.10000000149011612 && Number.isSafeInteger(2 ** 53 - 1) === true &&
  Object.is(Math.round(-0.4), -0) && Math.max(NaN, 1) !== Math.max(NaN, 1) && Number.EPSILON === 2 ** -52;
