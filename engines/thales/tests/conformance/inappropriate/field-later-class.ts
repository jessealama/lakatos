// A field typed at a class declared later is outside the model: a class
// resolves in source order, the way a parameter's type does.
export class Holder {
  readonly item: Item;

  constructor(item: Item) {
    this.item = item;
  }

  /** @ensures{peeks} forall (x: number) { Object.is(new Holder(new Item(x)).peek(), x) } */
  peek(): number {
    return this.item.v;
  }
}

export class Item {
  readonly v: number;

  constructor(v: number) {
    this.v = v;
  }
}
