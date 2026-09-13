#!/usr/bin/env node
// The parser bridge as a command: one JavaScript file in, one ESTree
// document out. This is a development entry point — `lakatos exe` is the
// user-facing command, and it is not this package's `bin`.

import { readFileSync, writeFileSync } from "node:fs";
import { realpathSync } from "node:fs";
import { pathToFileURL } from "node:url";
import { type ParseError, parseScript } from "./estree.js";

export function main(argv: readonly string[]): number {
  const [input, output] = argv;
  if (!input || argv.length > 2) {
    console.error("usage: tarski-bridge <in.js> [out.json]");
    return 2;
  }
  let source: string;
  try {
    source = readFileSync(input, "utf8");
  } catch (e) {
    // readFileSync throws a SystemError, which is an Error.
    console.error(`tarski-bridge: ${(e as Error).message}`);
    return 2;
  }
  let document: string;
  try {
    document = `${JSON.stringify(parseScript(source, input), null, 2)}\n`;
  } catch (e) {
    // parseScript throws nothing but ParseError: a source that does not
    // parse is the one input the bridge refuses outright.
    console.error(`tarski-bridge: ${(e as ParseError).message}`);
    return 2;
  }
  if (output) {
    writeFileSync(output, document);
  } else {
    process.stdout.write(document);
  }
  return 0;
}

// npm may install this behind a symlink, and Node resolves the main
// module to its realpath while argv[1] keeps the link.
/* v8 ignore start -- true only when node runs this file, which the
   suite does out of process, where this process's counters cannot see
   it. */
if (
  process.argv[1] &&
  import.meta.url === pathToFileURL(realpathSync(process.argv[1])).href
) {
  process.exit(main(process.argv.slice(2)));
}
/* v8 ignore stop */
