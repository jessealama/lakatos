/** @ensures{growsOrEqual} forall (n: nat ∈ [0, 8)) { double(n) >= n } */
export function double(n: number): number {
  return n + n;
}
