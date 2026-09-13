"use strict";
const xs = [1, 2];
xs.push(3);
const s = "n=" + xs.length + ":" + xs.join(",");
s === "n=3:1,2,3" && "a" < "b" && Array.isArray(xs) && Object.is(-0, -0) && !Object.is(0, -0);
