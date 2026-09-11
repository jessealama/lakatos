// Two textually equal unmodeled calls are two sites; nothing identifies
// them, so their difference is not 0.
declare function probe(n: number): number;

/** @ensures{agree} forall (n: int ∈ [0, 5)) { twice(n) === 0 } */
export function twice(n: number): number {
  return probe(n) - probe(n);
}
