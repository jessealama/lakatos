// test262's YAML front matter, the four keys the runner reads.
//
// The block is `/*---` … `---*/`, and its contents are YAML. Nothing here
// is a YAML parser: the suite's own front matter is a small, regular
// subset — top-level keys at column 0, lists either flow (`[a.js, b.js]`)
// or block (`  - Symbol`), `negative` a two-key map, and `info`/
// `description` block scalars that are prose and are skipped whole. A
// key this file does not read is skipped by indentation along with
// everything under it, so a block scalar can say anything at all,
// including something that looks like a key.

/** The four front-matter keys that decide how a test is run. */
export interface FrontMatter {
  /** `includes`: harness files to evaluate after the preludes, in order. */
  includes: string[];
  /** `flags`: `onlyStrict`, `noStrict`, `raw`, `async`, `module`, … */
  flags: string[];
  /** `features`: carried, not used for selection. */
  features: string[];
  /** `negative`: the phase at which, and the class with which, the test must fail. */
  negative?: { phase: string; type: string };
}

/** The `/*---` … `---*\/` block's contents, or `undefined` when there is none. */
function block(source: string): string | undefined {
  const open = source.indexOf("/*---");
  if (open < 0) return undefined;
  const close = source.indexOf("---*/", open + 5);
  if (close < 0) return undefined;
  return source.slice(open + 5, close);
}

/** A list item or scalar with a trailing ` # comment` dropped. */
function uncomment(text: string): string {
  const hash = text.indexOf(" #");
  return (hash < 0 ? text : text.slice(0, hash)).trim();
}

/** A flow list, `[a.js, b.js]` or `[]`. */
function flowList(text: string): string[] {
  const inner = text.replace(/^\[/, "").replace(/\]$/, "");
  return inner
    .split(",")
    .map((item) => uncomment(item))
    .filter((item) => item.length > 0);
}

/** The lines indented under the key at `index`, up to the next column-0 key. */
function indented(lines: readonly string[], index: number): string[] {
  const out: string[] = [];
  for (const line of lines.slice(index + 1)) {
    if (line.trim().length === 0) continue;
    if (!/^\s/.test(line)) break;
    out.push(line);
  }
  return out;
}

/** A block list's items: the `  - item` lines under a key. */
function blockList(lines: readonly string[], index: number): string[] {
  const out: string[] = [];
  for (const line of indented(lines, index)) {
    const item = /^\s+-\s*(.*)$/.exec(line);
    if (!item) break;
    /* v8 ignore next -- the group is not optional, so a match has it;
       the fallback is `noUncheckedIndexedAccess` asking. */
    out.push(uncomment(item[1] ?? ""));
  }
  return out;
}

/** `negative`'s two indented entries, both required for a negative test. */
function negativeMap(
  lines: readonly string[],
  index: number,
): FrontMatter["negative"] {
  let phase: string | undefined;
  let type: string | undefined;
  for (const line of indented(lines, index)) {
    const entry = /^\s+([A-Za-z_]+):\s*(.*)$/.exec(line);
    if (!entry) continue;
    /* v8 ignore start -- neither group is optional, so a match has both;
       the fallbacks are `noUncheckedIndexedAccess` asking. */
    if (entry[1] === "phase") phase = uncomment(entry[2] ?? "");
    if (entry[1] === "type") type = uncomment(entry[2] ?? "");
    /* v8 ignore stop */
  }
  if (phase === undefined || type === undefined) return undefined;
  return { phase, type };
}

/**
 * The front matter of one test. A file with no block, or with a key
 * missing, gets the empty answer for that key: absent and empty mean the
 * same thing to every decision the runner makes.
 */
export function parseFrontMatter(source: string): FrontMatter {
  const front: FrontMatter = { includes: [], flags: [], features: [] };
  const text = block(source);
  if (text === undefined) return front;

  const lines = text.split("\n");
  for (const [index, line] of lines.entries()) {
    // Column 0, so a block scalar's indented prose is never a key.
    const key = /^([A-Za-z_]+):\s*(.*)$/.exec(line);
    if (!key) continue;
    /* v8 ignore start -- neither group is optional. */
    const name = key[1] ?? "";
    const value = uncomment(key[2] ?? "");
    /* v8 ignore stop */
    if (name === "includes" || name === "flags" || name === "features") {
      front[name] =
        value.length > 0 ? flowList(value) : blockList(lines, index);
    } else if (name === "negative") {
      const negative = negativeMap(lines, index);
      if (negative !== undefined) front.negative = negative;
    }
  }
  return front;
}
