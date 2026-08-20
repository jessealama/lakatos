/** @ensures{grows} forall (x: nat) { dbl(x) >= x } */
export function dbl(x: number): number {
  return x * 2;
}
