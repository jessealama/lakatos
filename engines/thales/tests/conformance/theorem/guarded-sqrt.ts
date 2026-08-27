/** @ensures{nonNeg} forall (x: number in [-10, 10]) { normalize(x) >= 0 } */
export function normalize(x: number): number {
  if (x === -Infinity || x === Infinity) {
    throw new RangeError("Cannot accept infinite coordinates");
  }
  return Math.sqrt(x * x);
}

/** @ensures{nonNeg} forall (x: number in [-10, 10]) { normalizeChecked(x) >= 0 } */
export function normalizeChecked(x: number): number {
  if (Object.is(x, NaN)) {
    throw new RangeError("Cannot accept NaN coordinates");
  }
  if (x === -Infinity || x === Infinity) {
    throw new RangeError("Cannot accept infinite coordinates");
  }
  return Math.sqrt(x * x);
}
