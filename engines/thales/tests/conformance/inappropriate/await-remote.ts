declare function remote(x: number): Promise<number>;

/** @ensures{nonNegative} forall (x: int ∈ [0, 10)) { fetchTotal(x) >= 0 } */
export async function fetchTotal(x: number): Promise<number> {
  return await remote(x);
}
