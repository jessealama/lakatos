import {
  describe,
  it,
  expect,
  beforeEach,
  afterEach,
  afterAll,
  vi,
} from "vitest";
import { execFileSync, spawnSync } from "node:child_process";
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { fileURLToPath } from "node:url";
import path from "node:path";
import { main } from "../src/test262/cli.js";
import type { Expectations } from "../src/test262/report.js";

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

const overTree = (...extra: string[]): readonly string[] => [
  "test",
  "--test262",
  TREE,
  "--binary",
  FAKE,
  "--timeout",
  "200",
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

  it("runs the whole fake tree and tabulates it", () => {
    const result = invoke(overTree());
    expect(result.status).toBe(0);
    expect(result.stdout.startsWith(TABLE)).toBe(true);
  });

  it("names each not-run reason, each skip reason, and the unsupported kinds", () => {
    const { stdout } = invoke(overTree());
    expect(stdout).toContain(
      "not run:\n  async  1\n  module  1\n  noStrict  1\n  raw  1",
    );
    expect(stdout).toContain(
      "skipped:\n  intl402  1\n  parse-negative  1\n  resolution-negative  1",
    );
    expect(stdout).toContain(
      "unsupported:\n  SwitchStatement  2\n  $262.evalScript  1",
    );
  });

  it("lists the failures, the harness errors, and the timeouts", () => {
    const { stdout } = invoke(overTree());
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
    expect(invoke(overTree("--write", file)).status).toBe(0);
    const checked = invoke(overTree("--check", file));
    expect(checked.status).toBe(0);
    expect(checked.stdout).toContain(`expectations match ${file}`);
  });

  it("exits 1 and names the count when --check disagrees", () => {
    const file = path.join(scratch, "edited.json");
    invoke(overTree("--write", file));
    const expected = JSON.parse(readFileSync(file, "utf8")) as Expectations;
    const row = expected.directories["test/pass"];
    if (row === undefined) throw new Error("no test/pass row was written");
    row.pass = 5;
    writeFileSync(file, `${JSON.stringify(expected, null, 2)}\n`);
    const checked = invoke(overTree("--check", file));
    expect(checked.status).toBe(1);
    expect(checked.stderr).toContain("test/pass: pass expected 5, got 6");
  });

  describe("usage", () => {
    it("needs at least one slice", () => {
      const result = invoke(["--test262", TREE]);
      expect(result.status).toBe(2);
      expect(result.stderr).toContain("at least one slice is needed");
    });

    it("refuses an unknown flag", () => {
      const result = invoke([...overTree(), "--nope", "x"]);
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
  it("pins a 40-hex-digit commit", () => {
    const pin = JSON.parse(
      readFileSync(path.join(root, "tarski", "test262", "pin.json"), "utf8"),
    ) as { repository: string; commit: string };
    expect(pin.commit).toMatch(/^[0-9a-f]{40}$/);
    expect(pin.repository).toContain("test262");
  });

  it("holds the harness slice's counts in the shape --check reads", () => {
    const expectations = JSON.parse(
      readFileSync(
        path.join(root, "tarski", "test262", "expected.json"),
        "utf8",
      ),
    ) as Expectations;
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
    for (const reason of ["noStrict", "raw", "async", "module"] as const) {
      expect(Number.isInteger(harness.notRun[reason])).toBe(true);
    }
    // The floor as measured at the pin: `assert.js` opens with a `switch`,
    // so every non-async test in the slice is refused at it.
    expect(harness).toEqual({
      pass: 0,
      fail: 0,
      unsupported: 99,
      timeout: 0,
      harnessError: 0,
      notRun: { noStrict: 0, raw: 0, async: 17, module: 0 },
    });
  });
});
