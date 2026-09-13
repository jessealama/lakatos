"use strict";
function P() {}
P.prototype.k = 5;
const p = new P();
p.k === 5 && p.constructor === P && typeof P === "function";
