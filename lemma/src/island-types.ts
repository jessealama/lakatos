import ts from "typescript";
import * as path from "node:path";
import type { Binder } from "./binder.js";
import type { ClassTable } from "./class-domain.js";
import { isClassDomain } from "./domains.js";
import type { InvalidAnnotation, RawAnnotation } from "./extract.js";
import { atomsOf, type Formula } from "./formula-ast.js";
import { annotationKey } from "./qualified-name.js";
import { type CheckedProgram, OPTION_SKEW_ERRORS } from "./typecheck.js";

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

/** Where one atom's parenthesized `js` sits in the probe text.
 * `statementEnd` closes the whole `satisfies boolean;` line: tsc anchors a
 * satisfies mismatch on the expected type, past the atom's own text. */
export interface AtomSpan {
  annotation: number;
  atom: number;
  start: number;
  end: number;
  statementEnd: number;
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
      const end = text.length;
      text += " satisfies boolean;\n";
      atoms.push({
        annotation: i,
        atom: j,
        start: s,
        end,
        statementEnd: text.length,
      });
    });
    text += "});\n";
    probes.push({ annotation: i, start, end: text.length });
  });
  return { text, atoms, probes };
}

/** What the pass found: faults in the shape extraction reports them, and
 * the identity keys of every annotation it refused. */
export interface IslandTyping {
  invalid: { file: string; invalid: InvalidAnnotation[] }[];
  refused: Set<string>;
}

// A project's noUnusedLocals/noUnusedParameters would raise these against
// the probe's own scaffolding; they say nothing about the formula.
const UNUSED_CODES = new Set([6133, 6196, 6198, 6199, 6205]);

/**
 * Type every atom of every typable annotation as host code, in its own
 * module's scope, and report each diagnostic as a fault of the annotation
 * whose atom it lands in (spec, "Islands"). Runs once per invocation, over
 * a program built on the gate's.
 */
export function typeFormulas(
  files: ParsedFile[],
  checked: CheckedProgram | undefined,
): IslandTyping {
  const result: IslandTyping = { invalid: [], refused: new Set() };
  const work = files.filter((f) =>
    f.annotations.some((a) => typable(a, f.classes)),
  );
  if (work.length === 0) return result;
  if (checked === undefined)
    throw new Error(
      "island typing needs the gate's program, which an empty program never builds",
    );
  const probes = new Map<string, { parsed: ParsedFile; probe: Probe }>();
  for (const f of work) {
    const sf = checked.program.getSourceFile(path.resolve(checked.cwd, f.file));
    if (sf === undefined)
      throw new Error(`${f.file} is not in the program the gate checked`);
    probes.set(sf.fileName, {
      parsed: f,
      probe: buildProbe(sf.text, f.annotations, f.classes),
    });
  }
  const program = probeProgram(checked, probes);
  for (const [fileName, { parsed, probe }] of probes) {
    const sf = program.getSourceFile(fileName)!;
    const faults = new Map<number, string[]>();
    const note = (annotation: number, message: string): void => {
      const list = faults.get(annotation) ?? [];
      list.push(message);
      faults.set(annotation, list);
    };
    const diagnostics = [
      ...program.getSyntacticDiagnostics(sf),
      ...program.getSemanticDiagnostics(sf),
    ]
      .filter((d) => d.category === ts.DiagnosticCategory.Error)
      .filter(
        (d) => !UNUSED_CODES.has(d.code) && !OPTION_SKEW_ERRORS.has(d.code),
      )
      .sort((a, b) => a.start! - b.start!);
    for (const d of diagnostics) {
      const at = d.start!;
      const rendered = `TS${d.code}: ${ts.flattenDiagnosticMessageText(d.messageText, " ")}`;
      const atom = probe.atoms.find(
        (s) => s.start <= at && at < s.statementEnd,
      );
      if (atom !== undefined) {
        note(
          atom.annotation,
          `in atom \`${atomText(parsed, atom)}\`: ${rendered}`,
        );
        continue;
      }
      const span = probe.probes.find((s) => s.start <= at && at < s.end);
      // The gate passed this text under these options, so a diagnostic
      // outside the probes is the pass's own bug, not the author's.
      /* v8 ignore next 4 -- the gate passed the same text; only a bug in the pass reports outside the probes */
      if (span === undefined)
        throw new Error(
          `${parsed.file}: the probe program reports ${rendered} outside the probes`,
        );
      note(span.annotation, rendered);
    }
    const invalid: InvalidAnnotation[] = [];
    for (const [i, messages] of [...faults].sort(([a], [b]) => a - b)) {
      const a = parsed.annotations[i]!.raw;
      invalid.push({
        propertyName: a.propertyName,
        functionName: a.functionName,
        ...(a.className !== undefined
          ? { className: a.className, isStatic: a.isStatic }
          : {}),
        line: a.line,
        message: `@ensures{${a.propertyName}}: ${messages.join("; ")}`,
      });
      result.refused.add(annotationKey(parsed.file, a));
    }
    if (invalid.length > 0) result.invalid.push({ file: parsed.file, invalid });
  }
  return result;
}

function atomText(parsed: ParsedFile, span: AtomSpan): string {
  const formula = parsed.annotations[span.annotation]!.parsed!.formula;
  return atomsOf(formula)[span.atom]!.text;
}

/** The gate's program with each probed file's text replaced: unchanged
 * files keep the gate's SourceFile objects, so only the probed ones are
 * parsed and checked again. */
function probeProgram(
  checked: CheckedProgram,
  probes: Map<string, { probe: Probe }>,
): ts.Program {
  const host = ts.createCompilerHost(checked.options);
  const fallback = host.getSourceFile;
  host.getSourceFile = (fileName, languageVersion, onError, shouldCreate) => {
    const p = probes.get(fileName);
    if (p !== undefined)
      return ts.createSourceFile(fileName, p.probe.text, languageVersion, true);
    return (
      checked.program.getSourceFile(fileName) ??
      fallback(fileName, languageVersion, onError, shouldCreate)
    );
  };
  const readFile = host.readFile;
  host.readFile = (fileName) =>
    probes.get(fileName)?.probe.text ?? readFile(fileName);
  return ts.createProgram({
    rootNames: checked.rootNames,
    options: checked.options,
    host,
    oldProgram: checked.program,
  });
}
