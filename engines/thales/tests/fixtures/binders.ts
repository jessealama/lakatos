/**
 * @ensures{chained} forall (x: int ∈ [0, 10)) { x >= 2 → x >= 1 → keep(x) >= 1 }
 * @ensures{guardedWitness} forall (x: int ∈ [0, 10)) { x >= 5 → keep(x) >= 6 }
 */
export function keep(x: number): number {
  if (x < 1) {
    return 1;
  }
  return x;
}

/** @ensures{negativeFloor} forall (x: int ∈ [-3, 3)) { twice(x) >= 0 } */
export function twice(x: number): number {
  return x + x;
}

/**
 * @ensures{scaled} forall (x y: number) (sf: number ∈ (0, ∞)) {
 *   x <= y → scale(x, sf) <= scale(y, sf)
 * }
 */
export function scale(value: number, factor: number): number {
  return value * factor;
}
