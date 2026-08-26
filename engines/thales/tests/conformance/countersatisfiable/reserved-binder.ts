// A binder and parameter spelled like the artifact's reserved vocabulary:
// the renderer primes them in the emitted text, and the witness must still
// report the source spelling.
/** @ensures{reachesOne} forall (pure: int ∈ [0, 5)) { double(pure) >= 1 } */
export function double(pure: number): number {
  return pure + pure;
}
