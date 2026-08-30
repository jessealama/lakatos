/** @ensures{mixedTagSkipped} forall (x: number) { skipMixed(x) === 1 } */
export function skipMixed(x: number): number {
  if (Object.is(Number.isFinite(x), x)) {
    return 0;
  }
  return 1;
}

/** @ensures{undefinedNeverHits} forall (x: number) { definedOnly(x) === 1 } */
export function definedOnly(x: number): number {
  if (Object.is(x, undefined)) {
    return 0;
  }
  return 1;
}

/** @ensures{boolReflexive} forall (n: int ∈ [0, 3)) { Object.is(Number.isFinite(n), Number.isFinite(n)) } */
export function probe(n: number): number {
  return n;
}

/** @ensures{mixedTagClaimed} forall (n: int ∈ [0, 3)) { Object.is(Number.isFinite(n), n) } */
export function claimMixed(n: number): number {
  return n;
}

/** @ensures{vacuousMixedGuard} forall (n: int ∈ [0, 3)) { Number.isFinite(n) ≡ n -> ident(n) === 5 } */
export function ident(n: number): number {
  return n;
}

/** @ensures{unionNeverBool} forall (x: number) { classify(x) === 0 } */
export function classify(v: number | string): number {
  if (Object.is(v, Number.isNaN(0))) {
    return 1;
  }
  return 0;
}
