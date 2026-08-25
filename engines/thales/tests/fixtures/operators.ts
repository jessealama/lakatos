/** @ensures{belowSeven} forall (x: int ∈ [0, 20)) { rem7(x) < 7 } */
export function rem7(x: number): number {
  return x % 7;
}

/** @ensures{nonPositive} forall (x: int ∈ [0, 5)) { neg(x) <= 0 } */
export function neg(x: number): number {
  return -x;
}

/** @ensures{same} forall (x: int) { plus(x) ≡ x } */
export function plus(x: number): number {
  return +x;
}

/**
 * @ensures{grows} forall (n: nat) { bump(n) > n }
 * @ensures{hits} forall (x: int ∈ [0, 10)) { bump(x) === x + 1 }
 * @ensures{misses} forall (x: int ∈ [0, 10)) { bump(x) !== x }
 */
export function bump(x: number): number {
  return x + 1;
}

/** @ensures{shifts} forall (x: int ∈ [0, 5)) { chain(x) ≡ 2 - neg(x) } */
export function chain(x: number): number {
  return bump(neg(x)) + 1;
}
