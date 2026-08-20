/** @ensures{grows} forall (n: nat ∈ (-∞, 10]) { triple(n) >= n } */
export function triple(n: number): number {
  return n * 3;
}
