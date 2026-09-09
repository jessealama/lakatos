// A local may be bound at boolean: inferred from a comparison, from a
// literal, or annotated; a bound boolean is a condition, a logical
// operand, an equality side, and a value for a union slot.

/** @ensures{named} forall (n: int ∈ [0, 10)) { clip(n) >= 0 } */
export function clip(n: number): number {
  const isSmall = n < 5;
  if (isSmall) {
    return 0;
  }
  return n;
}

/** @ensures{flag} forall (n: int ∈ [0, 10)) { flagged(n) >= 0 } */
export function flagged(n: number): number {
  let found = false;
  if (n < 5) {
    found = true;
  }
  if (found) {
    return 0;
  }
  return n;
}

/** @ensures{annotated} forall (n: int ∈ [0, 10)) { gated(n) === n } */
export function gated(n: number): number {
  const open: boolean = true;
  if (open) {
    return n;
  }
  return 0;
}

/** @ensures{strict} forall (n: int ∈ [0, 10)) { strictly(n) >= 0 } */
export function strictly(n: number): number {
  const a = n < 5;
  if (a === true) {
    return 0;
  }
  if (a !== n > 7) {
    return 1;
  }
  return n;
}

/** @ensures{sameValue} forall (n: int ∈ [0, 10)) { sameValued(n) >= 0 } */
export function sameValued(n: number): number {
  const a = n < 5;
  if (Object.is(a, false)) {
    return n;
  }
  return 0;
}

/** @ensures{logical} forall (n: int ∈ [0, 10)) { combined(n) >= 0 } */
export function combined(n: number): number {
  const a = n < 5;
  const b = !a;
  if (a && n > 1) {
    return 1;
  }
  if (b || n === 0) {
    return 2;
  }
  return n;
}

/** @ensures{slot} forall (n: int ∈ [0, 10)) { slotted(n) >= 0 } */
export function slotted(n: number): number {
  const w: boolean | undefined = n < 5;
  if (typeof w === "boolean") {
    return 1;
  }
  return 0;
}
