import {
  describe,
  it,
  expect,
  beforeAll,
  beforeEach,
  afterEach,
  afterAll,
  vi,
} from "vitest";
import { execFileSync, spawnSync } from "node:child_process";
import {
  cpSync,
  mkdtempSync,
  readFileSync,
  rmSync,
  writeFileSync,
} from "node:fs";
import { tmpdir } from "node:os";
import { fileURLToPath } from "node:url";
import path from "node:path";
import { main } from "../src/test262/cli.js";
import type { Expectations, Summary } from "../src/test262/report.js";

const root = fileURLToPath(new URL("../../..", import.meta.url));
const TREE = fileURLToPath(new URL("fixtures/test262", import.meta.url));
const FAKE = fileURLToPath(
  new URL("fixtures/fake-tarski.mjs", import.meta.url),
);

/** `main` with its output captured, the way a person reads it. */
function invoke(argv: readonly string[]): {
  status: number;
  stdout: string;
  stderr: string;
} {
  const stdout: string[] = [];
  const stderr: string[] = [];
  const outSpy = vi.spyOn(console, "log").mockImplementation((line: string) => {
    stdout.push(line);
  });
  const errSpy = vi
    .spyOn(console, "error")
    .mockImplementation((line: string) => {
      stderr.push(line);
    });
  try {
    return {
      status: main(argv),
      stdout: stdout.join("\n"),
      stderr: stderr.join("\n"),
    };
  } finally {
    outSpy.mockRestore();
    errSpy.mockRestore();
  }
}

// 2 s per test, not 200 ms: the fake binary is a node process, and under
// the coverage run a cold start can outlast a tight timeout, which would
// move a passing test into the timeout column.
const overTree = (...extra: string[]): readonly string[] => [
  "test",
  "--test262",
  TREE,
  "--binary",
  FAKE,
  "--timeout",
  "2000",
  ...extra,
];

// The one slice with nothing in it that diverges, for the cases that do
// not need the whole tree.
const overPass = (...extra: string[]): readonly string[] => [
  "test/pass",
  "--test262",
  TREE,
  "--binary",
  FAKE,
  ...extra,
];

// The fake tree has one directory per outcome class, so this golden is
// the whole table shape and every row of it at once.
const TABLE = [
  "directory           pass  fail  unsupported  timeout  harness-error  not-run",
  "test/fail              0     4            0        0              0        0",
  "test/harness-error     0     0            0        0              2        0",
  "test/not-run           0     0            0        0              0        4",
  "test/pass              6     0            0        0              0        0",
  "test/timeout           0     0            0        1              0        0",
  "test/unsupported       0     0            3        0              0        0",
].join("\n");

describe("tarski-test262", () => {
  const scratch = mkdtempSync(path.join(tmpdir(), "test262-cli-"));
  afterAll(() => rmSync(scratch, { recursive: true, force: true }));

  // One run of the whole tree, read by the three cases below: the timeout
  // case costs the timeout, so it is paid once.
  let tree: { status: number; stdout: string; stderr: string };
  beforeAll(() => {
    tree = invoke(overTree());
  });

  it("runs the whole fake tree and tabulates it", () => {
    expect(tree.status).toBe(0);
    expect(tree.stdout.startsWith(TABLE)).toBe(true);
  });

  it("names each not-run reason, each skip reason, and the unsupported kinds", () => {
    const { stdout } = tree;
    expect(stdout).toContain(
      "not run:\n  async  1\n  module  1\n  noStrict  1\n  raw  1",
    );
    expect(stdout).toContain(
      "skipped:\n  intl402  1\n  parse-negative  1\n  resolution-negative  1",
    );
    expect(stdout).toContain(
      "unsupported:\n  DeleteExpression  2\n  $262.evalScript  1",
    );
  });

  it("lists the failures, the harness errors, and the timeouts", () => {
    const { stdout } = tree;
    expect(stdout).toContain(
      "test/fail/assert-fails.js  Uncaught Test262Error: boom",
    );
    expect(stdout).toContain(
      "test/fail/negative-wrong-class.js  expected an uncaught TypeError, got Uncaught RangeError: r",
    );
    expect(stdout).toContain(
      "test/harness-error/missing-include.js  no harness file nope.js",
    );
    expect(stdout).toContain("timeouts:\n  test/timeout/loops.js");
  });

  it("round-trips --write through --check", () => {
    const file = path.join(scratch, "expected.json");
    expect(invoke(overPass("--write", file)).status).toBe(0);
    const checked = invoke(overPass("--check", file));
    expect(checked.status).toBe(0);
    expect(checked.stdout).toContain(`expectations match ${file}`);
  });

  it("exits 1 and names the count when --check disagrees", () => {
    const file = path.join(scratch, "edited.json");
    invoke(overPass("--write", file));
    const expected = JSON.parse(readFileSync(file, "utf8")) as Expectations;
    const row = expected.directories["test/pass"];
    if (row === undefined) throw new Error("no test/pass row was written");
    row.pass = 5;
    writeFileSync(file, `${JSON.stringify(expected, null, 2)}\n`);
    const checked = invoke(overPass("--check", file));
    expect(checked.status).toBe(1);
    expect(checked.stderr).toContain("test/pass: pass expected 5, got 6");
  });

  // The whole-suite mode: no per-test lists, a line of progress per
  // depth-three group on stderr, and the two committed files.
  describe("--summary", () => {
    let summary: { status: number; stdout: string; stderr: string };
    beforeAll(() => {
      summary = invoke(overTree("--summary"));
    });

    it("keeps the table and the counts and drops the three lists", () => {
      expect(summary.status).toBe(0);
      expect(summary.stdout.startsWith(TABLE)).toBe(true);
      expect(summary.stdout).toContain("not run:");
      expect(summary.stdout).toContain("skipped:");
      expect(summary.stdout).toContain("unsupported:");
      expect(summary.stdout).not.toContain("failures:");
      expect(summary.stdout).not.toContain("harness errors:");
      expect(summary.stdout).not.toContain("timeouts:");
    });

    // The fake tree's directories are two components deep, so each is its
    // own group; the last line has finished every test.
    it("reports progress once per group, ending at the total", () => {
      expect(summary.stderr).toBe(
        [
          "  4/23  test/fail",
          "  6/23  test/harness-error",
          "  7/23  test/intl402",
          "  11/23  test/not-run",
          "  17/23  test/pass",
          "  19/23  test/skipped",
          "  20/23  test/timeout",
          "  23/23  test/unsupported",
        ].join("\n"),
      );
    });
  });

  describe("--budget", () => {
    // Zero means the budget is spent before the first test, so every
    // planned run becomes `budget` and nothing is spawned at all. The
    // `test/timeout` row proving 0 timeouts is that witness: the fake
    // binary there diverges, and a spawned one would have cost the
    // whole per-test timeout.
    it("counts a run past the budget as not run, and spawns nothing", () => {
      const result = invoke(overTree("--budget", "0"));
      expect(result.status).toBe(0);
      expect(
        result.stdout.startsWith(
          [
            "directory           pass  fail  unsupported  timeout  harness-error  not-run",
            "test/fail              0     0            0        0              0        4",
            "test/harness-error     0     0            0        0              1        1",
            "test/not-run           0     0            0        0              0        4",
            "test/pass              0     0            0        0              0        6",
            "test/timeout           0     0            0        0              0        1",
            "test/unsupported       0     0            0        0              0        3",
          ].join("\n"),
        ),
      ).toBe(true);
      expect(result.stdout).toContain("budget  15");
    });

    it("refuses a budget that is not a non-negative integer", () => {
      for (const value of ["-1", "soon"]) {
        const result = invoke(["test", "--budget", value]);
        expect(result.status).toBe(2);
        expect(result.stderr).toContain(
          "--budget needs a non-negative integer",
        );
      }
    });
  });

  describe("--markdown and --json", () => {
    it("writes both files, labelled with what was run", () => {
      const markdown = path.join(scratch, "results.md");
      const json = path.join(scratch, "results.json");
      const result = invoke(overPass("--markdown", markdown, "--json", json));
      expect(result.status).toBe(0);
      expect(result.stdout).toContain(`wrote ${json}`);
      expect(result.stdout).toContain(`wrote ${markdown}`);
      const summary = JSON.parse(readFileSync(json, "utf8")) as Summary;
      // The fixture tree is not a repository, so there is no commit to
      // name and nothing to warn about.
      expect(summary.test262).toEqual({ commit: null });
      expect(summary.slices).toEqual(["test/pass"]);
      expect(summary.timeoutMs).toBe(10_000);
      expect(summary.totals.pass).toBe(6);
      expect(result.stderr).not.toContain("the pin is");
      const document = readFileSync(markdown, "utf8");
      expect(document.startsWith("# test262 results\n")).toBe(true);
      expect(document).toContain("| test/pass |");
    });

    it("writes either file on its own", () => {
      // Each writer is its own flag: the script asks for both, and a
      // person reading the table by hand asks for one.
      const markdown = path.join(scratch, "alone.md");
      const result = invoke(overPass("--markdown", markdown));
      expect(result.status).toBe(0);
      expect(result.stdout).toContain(`wrote ${markdown}`);
      expect(result.stdout).not.toContain(".json");
      expect(
        readFileSync(markdown, "utf8").startsWith("# test262 results\n"),
      ).toBe(true);
    });

    it("labels the table with the checkout's HEAD and warns off the pin", () => {
      const copy = path.join(
        mkdtempSync(path.join(tmpdir(), "test262-copy-")),
        "tree",
      );
      try {
        cpSync(TREE, copy, { recursive: true });
        const git = (...args: string[]): void => {
          execFileSync("git", args, { cwd: copy, stdio: "pipe" });
        };
        git("init", "--quiet");
        git("config", "user.email", "test@example.com");
        git("config", "user.name", "Test");
        git("add", ".");
        git("commit", "--quiet", "-m", "one");
        const head = execFileSync("git", ["-C", copy, "rev-parse", "HEAD"], {
          encoding: "utf8",
        }).trim();
        const json = path.join(scratch, "labelled.json");
        const result = invoke([
          "test/pass",
          "--test262",
          copy,
          "--binary",
          FAKE,
          "--json",
          json,
        ]);
        expect(result.status).toBe(0);
        const summary = JSON.parse(readFileSync(json, "utf8")) as Summary;
        expect(summary.test262.commit).toBe(head);
        const pin = JSON.parse(
          readFileSync(
            path.join(root, "tarski", "test262", "pin.json"),
            "utf8",
          ),
        ) as { commit: string };
        expect(result.stderr).toContain(
          `test262 checkout is at ${head}, the pin is ${pin.commit}`,
        );
      } finally {
        rmSync(path.dirname(copy), { recursive: true, force: true });
      }
    });
  });

  describe("--slice-file", () => {
    it("reads the slices out of a file, comments and blanks skipped", () => {
      const file = path.join(scratch, "slice.txt");
      writeFileSync(
        file,
        "# what this slice is\n\ntest/pass\n  test/fail  \n\n# trailing note\n",
      );
      const fromFile = invoke([
        "--slice-file",
        file,
        "--test262",
        TREE,
        "--binary",
        FAKE,
      ]);
      const fromArguments = invoke([
        "test/pass",
        "test/fail",
        "--test262",
        TREE,
        "--binary",
        FAKE,
      ]);
      expect(fromFile.status).toBe(0);
      expect(fromFile.stdout).toBe(fromArguments.stdout);
    });

    it("appends to the slices named as bare arguments", () => {
      const file = path.join(scratch, "one.txt");
      writeFileSync(file, "test/fail\n");
      const result = invoke([
        "test/pass",
        "--slice-file",
        file,
        "--test262",
        TREE,
        "--binary",
        FAKE,
      ]);
      expect(result.status).toBe(0);
      expect(result.stdout).toContain("test/pass");
      expect(result.stdout).toContain("test/fail");
    });

    it("exits 2 when the file is not there", () => {
      const missing = path.join(scratch, "nowhere.txt");
      const result = invoke(["--slice-file", missing, "--test262", TREE]);
      expect(result.status).toBe(2);
      expect(result.stderr).toContain(`cannot read ${missing}`);
    });

    it("exits 2 when the flag has no value", () => {
      const result = invoke(["--slice-file"]);
      expect(result.status).toBe(2);
      expect(result.stderr).toContain("--slice-file needs a value");
    });

    it("counts an empty file as no slices at all", () => {
      const file = path.join(scratch, "empty.txt");
      writeFileSync(file, "# nothing here yet\n");
      const result = invoke(["--slice-file", file, "--test262", TREE]);
      expect(result.status).toBe(2);
      expect(result.stderr).toContain("at least one slice is needed");
    });
  });

  describe("usage", () => {
    it("needs at least one slice", () => {
      const result = invoke(["--test262", TREE]);
      expect(result.status).toBe(2);
      expect(result.stderr).toContain("at least one slice is needed");
    });

    it("refuses an unknown flag", () => {
      const result = invoke([...overPass(), "--nope", "x"]);
      expect(result.status).toBe(2);
      expect(result.stderr).toContain("unknown flag --nope");
    });

    it("refuses a flag with no value", () => {
      const result = invoke(["test", "--test262"]);
      expect(result.status).toBe(2);
      expect(result.stderr).toContain("--test262 needs a value");
    });

    it("refuses a timeout that is not a positive integer", () => {
      const result = invoke(["test", "--timeout", "soon"]);
      expect(result.status).toBe(2);
      expect(result.stderr).toContain("--timeout needs a positive integer");
    });

    // The default paths: LAKATOS_TEST262 for the checkout, and
    // `.lake/build/bin/tarski` for the binary. Lean is not installed in
    // every job that runs this suite, so the binary may or may not be
    // there; either answer exercises the arm.
    it("falls back to the default checkout and binary", () => {
      const previous = process.env.LAKATOS_TEST262;
      process.env.LAKATOS_TEST262 = TREE;
      try {
        expect(invoke(["test/pass", "--binary", FAKE]).status).toBe(0);
        expect([0, 2]).toContain(invoke(["test/pass"]).status);
      } finally {
        if (previous === undefined) delete process.env.LAKATOS_TEST262;
        else process.env.LAKATOS_TEST262 = previous;
      }
    });

    it("names setup when the checkout is not there", () => {
      const result = invoke([
        "test",
        "--test262",
        path.join(scratch, "nothing"),
      ]);
      expect(result.status).toBe(2);
      expect(result.stderr).toContain("no test262 checkout at");
      expect(result.stderr).toContain("setup-test262.js");
    });

    it("names lake build when the binary is not there", () => {
      const result = invoke([
        "test",
        "--test262",
        TREE,
        "--binary",
        path.join(scratch, "nope"),
      ]);
      expect(result.status).toBe(2);
      expect(result.stderr).toContain("no evaluator at");
      expect(result.stderr).toContain("lake build tarski");
    });

    it("refuses arguments after setup", () => {
      const result = invoke(["setup", "extra"]);
      expect(result.status).toBe(2);
      expect(result.stderr).toContain("usage: tarski-test262 setup");
    });
  });

  // `setup` reads the committed pin and provisions LAKATOS_TEST262 when
  // it is set; the scratch repository stands in for tc39/test262.
  describe("setup", () => {
    const previous = process.env.LAKATOS_TEST262;
    let origin: string;
    let target: string;

    beforeEach(() => {
      origin = mkdtempSync(path.join(tmpdir(), "test262-origin-"));
      target = path.join(
        mkdtempSync(path.join(tmpdir(), "test262-target-")),
        "checkout",
      );
      const git = (...args: string[]): void => {
        execFileSync("git", args, { cwd: origin, stdio: "pipe" });
      };
      git("init", "--quiet");
      git("config", "user.email", "test@example.com");
      git("config", "user.name", "Test");
      writeFileSync(path.join(origin, "README.md"), "one\n");
      git("add", ".");
      git("commit", "--quiet", "-m", "one");
      process.env.LAKATOS_TEST262 = target;
    });

    afterEach(() => {
      if (previous === undefined) delete process.env.LAKATOS_TEST262;
      else process.env.LAKATOS_TEST262 = previous;
      rmSync(origin, { recursive: true, force: true });
      rmSync(path.dirname(target), { recursive: true, force: true });
    });

    it("fetches the pinned commit into LAKATOS_TEST262", () => {
      const commit = execFileSync("git", ["-C", origin, "rev-parse", "HEAD"], {
        encoding: "utf8",
      }).trim();
      const pin = path.join(scratch, "pin.json");
      writeFileSync(
        pin,
        `${JSON.stringify({ repository: origin, commit }, null, 2)}\n`,
      );
      const result = invoke(["setup", "--pin", pin]);
      expect(result.status).toBe(0);
      expect(result.stdout).toContain(commit);
      expect(
        execFileSync("git", ["-C", target, "rev-parse", "HEAD"], {
          encoding: "utf8",
        }).trim(),
      ).toBe(commit);
    });

    it("is a no-op on a second call", () => {
      const commit = execFileSync("git", ["-C", origin, "rev-parse", "HEAD"], {
        encoding: "utf8",
      }).trim();
      const pin = path.join(scratch, "pin.json");
      writeFileSync(
        pin,
        `${JSON.stringify({ repository: origin, commit }, null, 2)}\n`,
      );
      invoke(["setup", "--pin", pin]);
      const again = invoke(["setup", "--pin", pin]);
      expect(again.status).toBe(0);
      expect(again.stdout).toBe(`test262 already at ${commit}`);
    });

    it("refuses --pin with no value", () => {
      const result = invoke(["setup", "--pin"]);
      expect(result.status).toBe(2);
      expect(result.stderr).toContain("usage: tarski-test262 setup");
    });
  });
});

// The built file, run the way a person runs it, as `bridge-cli.test.ts`
// does for the parser bridge. The build is the suite-wide globalSetup's.
describe("dist/tarski/frontend/src/test262/cli.js", () => {
  const cli = path.join(
    root,
    "dist",
    "tarski",
    "frontend",
    "src",
    "test262",
    "cli.js",
  );

  it("starts with a shebang", () => {
    expect(readFileSync(cli, "utf8").startsWith("#!/usr/bin/env node\n")).toBe(
      true,
    );
  });

  it("runs main under node", () => {
    const result = spawnSync(
      process.execPath,
      [cli, "test/pass", "--test262", TREE, "--binary", FAKE],
      { encoding: "utf8" },
    );
    expect(result.status).toBe(0);
    expect(result.stdout).toContain(
      "test/pass     6     0            0        0              0        0",
    );
  });

  it("exits 2 on a usage error", () => {
    const result = spawnSync(process.execPath, [cli], { encoding: "utf8" });
    expect(result.status).toBe(2);
    expect(result.stderr).toContain("at least one slice is needed");
  });
});

describe("the committed files", () => {
  const read = (name: string): string =>
    readFileSync(path.join(root, "tarski", "test262", name), "utf8");

  it("pins a 40-hex-digit commit", () => {
    const pin = JSON.parse(read("pin.json")) as {
      repository: string;
      commit: string;
    };
    expect(pin.commit).toMatch(/^[0-9a-f]{40}$/);
    expect(pin.repository).toContain("test262");
  });

  it("holds the harness slice's counts in the shape --check reads", () => {
    const expectations = JSON.parse(read("expected.json")) as Expectations;
    const harness = expectations.directories["test/harness"];
    if (harness === undefined) throw new Error("no test/harness row");
    for (const field of [
      "pass",
      "fail",
      "unsupported",
      "timeout",
      "harnessError",
    ] as const) {
      expect(Number.isInteger(harness[field])).toBe(true);
    }
    for (const reason of [
      "noStrict",
      "raw",
      "async",
      "module",
      "budget",
    ] as const) {
      expect(Number.isInteger(harness.notRun[reason])).toBe(true);
    }
    // No literal here any more: the harness row moves with every slice of
    // syntax that lands, and `--check` is what pins its value. What this
    // asks is that the row is the shape `--check` reads.
    expect(harness.pass + harness.fail + harness.unsupported).toBeGreaterThan(
      0,
    );
  });

  it("names only slices the expectations file has rows for", () => {
    const slices = readFileSync(
      path.join(root, "tarski", "test262", "slice.txt"),
      "utf8",
    )
      .split("\n")
      .map((line) => line.trim())
      .filter((line) => line.length > 0 && !line.startsWith("#"));
    expect(slices.length).toBeGreaterThan(0);
    const expectations = JSON.parse(
      readFileSync(
        path.join(root, "tarski", "test262", "expected.json"),
        "utf8",
      ),
    ) as Expectations;
    const directories = Object.keys(expectations.directories);
    // A slice is a directory; its tests are tabulated under it or under a
    // subdirectory of it, so a slice with no row at all is one that was
    // added to the file and never run.
    for (const slice of slices) {
      expect({
        slice,
        covered: directories.some(
          (d) => d === slice || d.startsWith(`${slice}/`),
        ),
      }).toEqual({ slice, covered: true });
    }
  });

  // The scheduled run's output, committed from a local run of
  // `scripts/test262-full.sh`. What holds the table to the pin is this:
  // the runner itself only warns when a checkout is somewhere else.
  it("holds a results table run at the pin over the script's slices", () => {
    const pin = JSON.parse(read("pin.json")) as { commit: string };
    const summary = JSON.parse(read("results.json")) as Summary;
    expect(summary.test262).toEqual({ commit: pin.commit });
    expect(summary.slices).toEqual([
      "test/language",
      "test/built-ins",
      "test/intl402",
    ]);
    expect(Object.keys(summary.skipped).sort()).toEqual([
      "intl402",
      "parse-negative",
      "resolution-negative",
    ]);
    // `intl402` is run so its count lands among the excluded kinds, and
    // is skipped, so it has no row of its own.
    expect(summary.skipped.intl402).toBeGreaterThan(0);
    expect(Object.keys(summary.directories)).not.toContain("test/intl402");
    expect(summary.totals.unsupported).toBeGreaterThan(0);
  });

  it("holds a results document naming that same commit", () => {
    const pin = JSON.parse(read("pin.json")) as { commit: string };
    const document = read("results.md");
    expect(document.startsWith("# test262 results\n")).toBe(true);
    expect(document).toContain(pin.commit);
    expect(document).toContain("## Not run and skipped");
  });
});
