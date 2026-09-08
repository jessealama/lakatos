/** @ensures{integral} forall (n: int ∈ [0, 3)) { Number.isInteger(beyond(n)) } */
/** @ensures{notSafe} forall (n: int ∈ [0, 3)) { ¬Number.isSafeInteger(beyond(n)) } */
export function beyond(x: number): number {
  return 9007199254740992 + x * 2;
}
