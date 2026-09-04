export class Flag {
  constructor(
    public readonly on: boolean,
    public readonly armed: boolean,
  ) {}
  live(): boolean {
    return this.on && this.armed;
  }
}

/** Fails at (true, false) only; the walk reaches it third, after both
 * off tuples, and renders it as the construction that reproduces it.
 *
 * @ensures{onIsLive} forall (f: Flag) { f.on → f.live() }
 */
export function isLive(f: Flag): boolean {
  return f.live();
}

export class Pair {
  constructor(
    public readonly a: Flag,
    public readonly b: Flag,
  ) {}
}

/** Fails first at a = (false, false), b = (true, true): the least tuple
 * where b is live and a is not.
 *
 * @ensures{leftLeads} forall (p: Pair) { p.b.live() → p.a.live() }
 */
export function leftLeads(p: Pair): boolean {
  return !p.b.live() || p.a.live();
}
