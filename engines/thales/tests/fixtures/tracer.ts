declare function remote(x: number): Promise<number>;

/** @ensures{commutes} forall (a: int ∈ [0, 10)) (b: int ∈ [0, 10)) { add(a, b) ≡ add(b, a) } */
export function add(a: number, b: number): number {
  return a + b;
}

/** @ensures{nonNegative} forall (x: int ∈ [0, 10)) { fetchTotal(x) >= 0 } */
export async function fetchTotal(x: number): Promise<number> {
  return await remote(x);
}

export class Counter {
  /** @ensures{bumps} forall (n: int ∈ [0, 10)) { bump(n) > n } */
  bump(n: number): number {
    return n + 1;
  }
}
