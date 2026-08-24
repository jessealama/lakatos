/** @ensures{affine} forall (n: int ∈ [0, 100)) { affine(n) === 2 * n + 2 } */
export function affine(n: number): number {
  const doubled: number = 2 * n,
    shifted = doubled + 2;
  return shifted;
}
