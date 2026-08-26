/** @ensures{doubles} forall (n: int ∈ [0, 8)) { twice(n) === n + n } */
export function twice(n: number): number {
  return n + n;
}

export const double = (x: number): number => x * 2;

/** @ensures{viaConst} forall (n: int ∈ [0, 4)) { applyDouble(n) >= 0 } */
export function applyDouble(n: number): number {
  return double(n);
}

/** @ensures{viaFormula} forall (n: int ∈ [0, 4)) { keep(n) === double(n) } */
export function keep(n: number): number {
  return n;
}

/** @ensures{huge} forall (n: int ∈ [0, 1000000000000000000000000000000]) { lone(n) >= 0 } */
export function lone(n: number): number {
  return n;
}
