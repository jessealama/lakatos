// Constructor parameters may be any generable primitive, not only number.
export class Tag {
  public readonly name: string;
  public readonly count: bigint;
  public readonly active: boolean;

  constructor(name: string, count: bigint, active: boolean) {
    if (name.length === 0) {
      throw new RangeError("name must be non-empty");
    }
    this.name = name;
    this.count = count;
    this.active = active;
  }
}

/** @ensures{selfSame} forall (t: Tag) { describe(t) === describe(t) } */
export function describe(t: Tag): string {
  return t.name;
}
