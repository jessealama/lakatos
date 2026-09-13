"use strict";
function inv(x) { if (x === 0) throw new RangeError("zero"); return 1 / x; }
let caught = "";
try { inv(0); } catch (e) { caught = e instanceof RangeError ? e.message : "wrong"; } finally { caught = caught + "!"; }
caught;
