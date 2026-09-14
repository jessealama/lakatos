"use strict";
function inv(x) { if (x === 0)
    throw new RangeError("zero"); return 1 / x; }
console.log(inv(4));
console.log(inv(0));
