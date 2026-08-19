/** @ensures{monotone} forall (x: int ∈ [-5, 5]) { succ(x) > x } */
export function succ(x: number): number {
  return x + 1;
}
