/** Constructor discards compound with depth: Anchor admits one coordinate
 * pair, so almost every drawn tuple denotes no Segment and the run is
 * reported exhausted rather than passed. */
export class Anchor {
  public readonly x: number;

  constructor(x: number) {
    if (x !== 0.123456789) {
      throw new RangeError("anchor must sit exactly on the mark");
    }
    this.x = x;
  }
}

export class Segment {
  public readonly at: number;

  constructor(a: Anchor) {
    this.at = a.x;
  }

  /** @ensures{onTheMark} ∀ (s : Segment) { 0 <= s.where() } */
  where(): number {
    return this.at;
  }
}
