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

/** @ensures{shifts} forall (x: int ∈ [0, 5)) { chain(x) ≡ 2 + neg(x) } */
export function chain(x: number): number {
  return bump(neg(x)) + 1;
}

/** @ensures{nonNeg} forall (x: int ∈ [-5, 5)) { magnitude(x) >= 0 } */
export function magnitude(x: number): number {
  return Math.abs(x);
}

/** @ensures{finite} forall (n: int ∈ [0, 5)) { Number.isFinite(halveSafe(n)) } */
export function halveSafe(n: number): number {
  return n / 2;
}

/** @ensures{nan} forall (n: int ∈ [0, 5)) { Number.isNaN(zeroOverZero(n)) } */
export function zeroOverZero(n: number): number {
  return (n - n) / (n - n);
}
