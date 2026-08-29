// A mutual constructor-parameter cycle is refused for the same reason a
// direct one is: neither class reaches a base case through the other.
export class Ping {
  public readonly hops: number;

  constructor(pong: Pong) {
    this.hops = pong.hops + 1;
  }
}

export class Pong {
  public readonly hops: number;

  constructor(ping: Ping) {
    this.hops = ping.hops + 1;
  }
}

/** @ensures{selfSame} forall (p: Ping) { hopsOf(p) === hopsOf(p) } */
export function hopsOf(p: Ping): number {
  return p.hops;
}
