// A non-exported class cannot be a binder domain: no caller outside the
// module can construct one.
class Hidden {
  public readonly v: number;

  constructor(v: number) {
    this.v = v;
  }
}

/** @ensures{selfSame} forall (h: Hidden) { peek(h) === peek(h) } */
export function peek(h: Hidden): number {
  return h.v;
}
