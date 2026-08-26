export function boom(x: number): number {
  throw new RangeError("the left arm settles it");
}

/** @ensures{leftWins} forall (x: int in [0, 4)) { pick(x) === 0 } */
export function pick(x: number): number {
  if (x === x || boom(x) === 0) {
    return 0;
  }
  return 1;
}

/** @ensures{rightSleeps} forall (x: int in [0, 4)) { pickAnd(x) === 1 } */
export function pickAnd(x: number): number {
  if (x === x + 1 && boom(x) === 0) {
    return 0;
  }
  return 1;
}
