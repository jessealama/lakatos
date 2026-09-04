/** @ensures{atCap} forall (n: int ∈ [1, 1000]) { keep(n) >= 1 } */
export function keep(n: number): number {
  return n;
}

/** @ensures{aboveCap} forall (n: int ∈ [0, 1000]) { hold(n) >= 0 } */
export function hold(n: number): number {
  return n;
}
