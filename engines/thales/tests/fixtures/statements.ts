/** @ensures{floorsAtOne} forall (x: int ∈ [-5, 20)) { floorAtOne(x) >= 1 } */
export function floorAtOne(x: number): number {
  let y = x;
  if (x < 1) {
    y = 1;
  }
  return y;
}

/** @ensures{nonNegative} forall (s: int ∈ [0, 30)) { grade(s) >= 0 } */
export function grade(score: number): number {
  const bonus = 2;
  if (score < 0) {
    throw new RangeError(`negative score: ${score}`);
  } else if (score < 10) {
    return score + bonus;
  }
  let rank = 0;
  if (score < 20) {
    rank = 1;
  } else {
    rank = 2;
  }
  return rank * 100;
}

/** @ensures{atLeastOne} forall (x: int ∈ [-5, 5)) { clampUp(x) >= 1 } */
export function clampUp(x: number): number {
  if (x < 1) {
    x = 1;
  }
  return x;
}
