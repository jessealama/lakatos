// A union-typed constructor parameter is refused: the parameter has no
// single generable domain.
export class Label {
  public readonly text: string;

  constructor(text: string | number) {
    this.text = String(text);
  }
}

/** @ensures{selfSame} forall (l: Label) { render(l) === render(l) } */
export function render(l: Label): string {
  return l.text;
}
