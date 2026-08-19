/** @ensures{hits} forall (x: int ∈ [0, 10)) { twice(x) === x + x } */
export function twice(x: number): number {
  return x + x;
}

/** @ensures{misses} forall (x: int ∈ [0, 10)) { shadow(x) !== 2 * x + 1 } */
export function shadow(x: number): number {
  return twice(x);
}
