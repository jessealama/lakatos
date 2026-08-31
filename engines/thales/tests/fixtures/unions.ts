/** @ensures{numId} forall (x: number) { Object.is(toNum(x), x) } */
export function toNum(v: number | string): number {
  if (typeof v === "number") {
    return v;
  }
  return 0;
}

/** @ensures{nullNeverHits} forall (x: number) { Object.is(nullFlag(x), 0) } */
export function nullFlag(v: number | null): number {
  if (Object.is(v, null)) {
    return 1;
  }
  return 0;
}

/** @ensures{passthrough} forall (x: int ∈ [0, 4)) { Object.is(relay(x), x) } */
export function relay(v: number | string): number {
  return toNum(v);
}

/** @ensures{localCarries} forall (x: number) { Object.is(viaLocal(x), x) } */
export function viaLocal(v: number | string): number {
  const w: number | string = v;
  if (typeof w === "number") {
    return w;
  }
  return 0;
}

/** @ensures{settles} forall (x: int ∈ [0, 4)) { settle(x) >= 0 } */
export function settle(x: number): number {
  let pending: number | undefined = undefined;
  pending = x;
  if (typeof pending === "number") {
    return pending;
  }
  return 1;
}
