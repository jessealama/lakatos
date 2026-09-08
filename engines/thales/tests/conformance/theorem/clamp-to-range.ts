/** @ensures{atMost} forall (n: int ∈ [-5, 10)) { clamp(n) <= 5 } */
/** @ensures{atLeast} forall (n: int ∈ [-5, 10)) { clamp(n) >= 0 } */
export function clamp(x: number): number {
  return Math.min(Math.max(x, 0), 5);
}
