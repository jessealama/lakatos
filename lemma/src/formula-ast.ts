export type Formula =
  | { kind: "atom"; text: string; js: string }
  | { kind: "not"; arg: Formula }
  | { kind: "and"; left: Formula; right: Formula }
  | { kind: "or"; left: Formula; right: Formula }
  | { kind: "iff"; left: Formula; right: Formula }
  | { kind: "implication"; antecedents: Formula[]; consequent: Formula };

/** Every atom, left-to-right, in both spellings: `text` as the author
 * wrote it, `js` as it executes (equations desugared). */
export function atomsOf(f: Formula): Array<{ text: string; js: string }> {
  switch (f.kind) {
    case "atom":
      return [{ text: f.text, js: f.js }];
    case "not":
      return atomsOf(f.arg);
    case "and":
    case "or":
    case "iff":
      return [...atomsOf(f.left), ...atomsOf(f.right)];
    case "implication":
      return [...f.antecedents.flatMap(atomsOf), ...atomsOf(f.consequent)];
  }
}

/** All atom executable JS expressions (equation-desugared), left-to-right. */
export function collectAtoms(f: Formula): string[] {
  return atomsOf(f).map((a) => a.js);
}
