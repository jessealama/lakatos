// The conclusion is false below the guard too, so a witness that ignored
// the guard would report x = 0; the reported one must satisfy it.
/** @ensures{aboveThreshold} forall (x: int ∈ [0, 8)) { x >= 4 → floorAtOne(x) >= 5 } */
export function floorAtOne(x: number): number {
  if (x < 1) {
    return 1;
  }
  return x;
}
