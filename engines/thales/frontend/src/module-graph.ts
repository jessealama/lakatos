import * as fs from "node:fs";
import * as path from "node:path";

/** Reads a module's text by absolute path, or undefined when there is no
 * such file. Injectable, so a closure can be walked without a disk. */
export type ModuleReader = (file: string) => string | undefined;

export const diskReader: ModuleReader = (file) => {
  try {
    return fs.readFileSync(file, "utf8");
  } catch {
    return undefined;
  }
};

/** A specifier names the file nodeNext will emit; the TypeScript source it
 * was written as is what resolution wants, and it wins over a sibling
 * spelled the way the specifier is. */
const SOURCE_EXTENSIONS: Record<string, string[]> = {
  ".mjs": [".mts"],
  ".cjs": [".cts"],
  ".js": [".ts", ".tsx"],
};

/** The file a relative specifier names, or undefined for a bare specifier
 * (a package or a builtin) and for one that reaches no file. */
export function resolveImport(
  specifier: string,
  from: string,
  reader: ModuleReader,
): { file: string; text: string } | undefined {
  if (!/^\.\.?\//.test(specifier)) return undefined;
  const ext = path.extname(specifier);
  const stem = specifier.slice(0, specifier.length - ext.length);
  const spellings = [
    ...(SOURCE_EXTENSIONS[ext] ?? []).map((e) => stem + e),
    specifier,
  ];
  for (const spelling of spellings) {
    const file = path.resolve(path.dirname(from), spelling);
    const text = reader(file);
    if (text !== undefined) return { file, text };
  }
  return undefined;
}

/** The qualifier a dependency's names carry: its path relative to the
 * entry file, which is unique to it within the entry's artifact. */
export function moduleQualifier(entryDir: string, file: string): string {
  return path.relative(entryDir, file).split(path.sep).join("/");
}

/** A model's home: the defining module's entry-relative qualifier — empty
 * for the entry file itself — and the name it carries there. */
export interface ModelRef {
  module: string;
  name: string;
}

/** Model registries are keyed by module and name at once. NUL separates
 * them because it can occur in neither a path nor a TypeScript
 * identifier, so a module path can never collide with a class-qualified
 * member name. */
export function modelKey(ref: ModelRef): string {
  return `${ref.module}\0${ref.name}`;
}

/** How a model is named in a diagnostic: the entry's own by its source
 * spelling, a dependency's by its module, the way a reader would have to
 * name it to find the declaration. */
export function displayName(ref: ModelRef): string {
  return ref.module === "" ? ref.name : `${ref.module}::${ref.name}`;
}
