/** @ensures{positive} forall (x: int ∈ (0, 8]) { keep(x) >= 1 } */
export function keep(x: number): number {
  return x;
}

/** @ensures{bounded} forall (x: int ∈ [0, 8]) { shift(x) <= 9 } */
export function shift(x: number): number {
  return x + 1;
}
