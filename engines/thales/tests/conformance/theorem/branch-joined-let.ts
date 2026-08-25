/** @ensures{atLeastOne} forall (x: int ∈ [-5, 20]) { floorAtOne(x) >= 1 } */
export function floorAtOne(x: number): number {
  let y = x;
  if (x < 1) {
    y = 1;
  }
  return y;
}

/** @ensures{inRange} forall (x: int ∈ [-5, 20]) { bucket(x) >= 0 } */
export function bucket(x: number): number {
  let rank = 0;
  if (x < 0) {
    return 0;
  } else if (x < 10) {
    rank = 1;
  } else {
    rank = 2;
  }
  return rank * 10;
}
