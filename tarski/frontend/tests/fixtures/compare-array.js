"use strict";
function isSameValue(a, b) {
  if (a === b) {
    return a !== 0 || 1 / a === 1 / b;
  }
  return a !== a && b !== b;
}
function compareArray(a, b) {
  if (b.length !== a.length) {
    return false;
  }
  let i = 0;
  while (i < a.length) {
    if (!isSameValue(b[i], a[i])) {
      return false;
    }
    i = i + 1;
  }
  return true;
}
compareArray([1, 2, 3], [1, 2, 3]) && !compareArray([1, 2], [1, 2, 3]) && !compareArray([1, 2, 3], [1, 2, 4]) && compareArray([0 / 0], [0 / 0]) && !compareArray([0], [-0]) && compareArray([], []);
