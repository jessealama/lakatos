"use strict";
String(0.1 + 0.2) === "0.30000000000000004" && String(1e21) === "1e+21" && String(123456789012345680000) === "123456789012345680000" &&
  (255).toString(16) === "ff" && Number("0x1F") === 31 && Number("  12e-1 ") === 1.2 && Number.isNaN(Number("1_0")) && Number("") === 0;
