import type { Binder } from "./binder.js";
import type { ClassTable } from "./class-domain.js";
import { isClassDomain } from "./domains.js";
import type { RawAnnotation } from "./extract.js";
import { atomsOf, type Formula } from "./formula-ast.js";

/** One annotation as the CLI parsed it. `parsed` is absent when the
 * prefix's clamp emptied a domain: the engines contain that per
 * annotation, and there is nothing here to type. */
export interface ParsedAnnotation {
  raw: RawAnnotation;
  parsed?: { binders: Binder[]; formula: Formula };
}

/** One annotated module, as extraction and parsing left it. */
export interface ParsedFile {
  file: string;
  exports: Set<string>;
  classes: ClassTable;
  annotations: ParsedAnnotation[];
}

/** The host type a binder is bound at inside the probe (spec, "Islands"). */
export function hostType(b: Binder): string {
  if (isClassDomain(b.domain)) return b.domain.className;
  return b.domain === "int" || b.domain === "nat" ? "number" : b.domain;
}

/** Whether the pass types an annotation: it parsed, and every class binder
 * names a class the module declares. An unknown class is domain
 * resolution's to refuse, with a message that names the rule. */
export function typable(a: ParsedAnnotation, classes: ClassTable): boolean {
  if (a.parsed === undefined) return false;
  return a.parsed.binders.every(
    (b) => !isClassDomain(b.domain) || classes.has(b.domain.className),
  );
}

/** Where one atom's parenthesized `js` sits in the probe text. */
export interface AtomSpan {
  annotation: number;
  atom: number;
  start: number;
  end: number;
}

/** Where one annotation's whole probe sits in the probe text. */
export interface ProbeSpan {
  annotation: number;
  start: number;
  end: number;
}

export interface Probe {
  text: string;
  atoms: AtomSpan[];
  probes: ProbeSpan[];
}

const PROBE_HEAD = "\n// lakatos island typing probes; never written to disk\n";

/** The module's text with one probe per typable annotation appended: an
 * arrow whose parameters are the binders at their host types, its body
 * each atom under `satisfies boolean`. An expression statement binds no
 * module- or script-scope name, so two probed scripts cannot collide. */
export function buildProbe(
  original: string,
  annotations: ParsedAnnotation[],
  classes: ClassTable,
): Probe {
  let text = original + PROBE_HEAD;
  const atoms: AtomSpan[] = [];
  const probes: ProbeSpan[] = [];
  annotations.forEach((a, i) => {
    if (!typable(a, classes)) return;
    const { binders, formula } = a.parsed!;
    const params = binders
      .map((b) => `${b.varName}: ${hostType(b)}`)
      .join(", ");
    const start = text.length;
    text += `void ((${params}): void => {\n`;
    atomsOf(formula).forEach((atom, j) => {
      text += "  ";
      const s = text.length;
      text += `(${atom.js})`;
      atoms.push({ annotation: i, atom: j, start: s, end: text.length });
      text += " satisfies boolean;\n";
    });
    text += "});\n";
    probes.push({ annotation: i, start, end: text.length });
  });
  return { text, atoms, probes };
}
