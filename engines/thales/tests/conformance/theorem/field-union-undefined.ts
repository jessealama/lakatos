// A field at `number | undefined` holds the tagged value; a read under a
// test for the undefined tag projects on the number path only, so the
// throwing projection is discharged and the class binder proves.
export class Reading {
  readonly value: number | undefined;

  constructor(value: number) {
    this.value = value;
  }

  /** @ensures{readsBack} forall (x: number) { Object.is(new Reading(x).get(), x) } */
  get(): number {
    return this.value === undefined ? 0 : this.value;
  }
}

/** @ensures{selfSame} forall (r: Reading) { Object.is(peek(r), r.get()) } */
export function peek(r: Reading): number {
  return r.get();
}
