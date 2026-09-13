#!/usr/bin/env node
// The shim the issue names: `node tarski/scripts/setup-test262.js`.
//
// The logic itself is the `setup` subcommand of the runner's CLI, so that
// it is under the same coverage gate as the rest of the runner; this file
// is the spelling a person types from a checkout, where npm has not
// linked the package's own bins.

let main;
try {
  ({ main } = await import("../../dist/tarski/frontend/src/test262/cli.js"));
} catch {
  console.error(
    "tarski: no dist/ — run `npm run build` from the repo root first",
  );
  process.exit(2);
}
process.exit(main(["setup", ...process.argv.slice(2)]));
