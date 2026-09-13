import { describe, it, expect, beforeEach, afterEach } from "vitest";
import { execFileSync } from "node:child_process";
import {
  existsSync,
  mkdirSync,
  mkdtempSync,
  readFileSync,
  rmSync,
  writeFileSync,
} from "node:fs";
import { tmpdir } from "node:os";
import { fileURLToPath } from "node:url";
import path from "node:path";
import { setupTest262 } from "../src/test262/setup.js";

const root = fileURLToPath(new URL("../../..", import.meta.url));

// A scratch repository with two commits stands in for tc39/test262, so
// the fetch-by-SHA path is exercised without the network. The pin names
// the *older* commit, which is what shows the fetch is by SHA and not a
// clone of a branch tip.
describe("setupTest262", () => {
  let origin: string;
  let older: string;
  let newer: string;
  let target: string;
  let log: string[];

  const git = (cwd: string, ...args: string[]): string =>
    execFileSync("git", args, { cwd, encoding: "utf8", stdio: "pipe" });

  const head = (dir: string): string => git(dir, "rev-parse", "HEAD").trim();

  beforeEach(() => {
    origin = mkdtempSync(path.join(tmpdir(), "test262-origin-"));
    target = path.join(
      mkdtempSync(path.join(tmpdir(), "test262-target-")),
      "checkout",
    );
    log = [];
    git(origin, "init", "--quiet");
    git(origin, "config", "user.email", "test@example.com");
    git(origin, "config", "user.name", "Test");
    writeFileSync(path.join(origin, "README.md"), "one\n");
    git(origin, "add", ".");
    git(origin, "commit", "--quiet", "-m", "one");
    older = head(origin);
    writeFileSync(path.join(origin, "README.md"), "two\n");
    git(origin, "add", ".");
    git(origin, "commit", "--quiet", "-m", "two");
    newer = head(origin);
  });

  afterEach(() => {
    rmSync(origin, { recursive: true, force: true });
    rmSync(path.dirname(target), { recursive: true, force: true });
  });

  const setup = (commit: string): void => {
    setupTest262(target, { repository: origin, commit }, (line) =>
      log.push(line),
    );
  };

  it("checks out the pinned commit into a fresh directory", () => {
    setup(older);
    expect(head(target)).toBe(older);
    expect(readFileSync(path.join(target, "README.md"), "utf8")).toBe("one\n");
    expect(log.at(-1)).toContain(older);
  });

  it("fetches at depth 1 and makes no submodule", () => {
    setup(older);
    expect(git(target, "rev-list", "--count", "HEAD").trim()).toBe("1");
    expect(existsSync(path.join(target, ".gitmodules"))).toBe(false);
  });

  it("is a no-op when the checkout is already at the pin", () => {
    setup(older);
    log = [];
    setup(older);
    expect(log).toEqual([`test262 already at ${older}`]);
  });

  // An interrupted fetch leaves a directory with a `.git` and no HEAD.
  it("re-fetches into a repository that has no HEAD", () => {
    mkdirSync(target, { recursive: true });
    git(target, "init", "--quiet");
    setup(older);
    expect(head(target)).toBe(older);
  });

  it("moves a checkout at the wrong commit to the pin", () => {
    setup(newer);
    expect(head(target)).toBe(newer);
    setup(older);
    expect(head(target)).toBe(older);
  });

  it("re-points a remote that moved", () => {
    setup(older);
    git(
      target,
      "remote",
      "set-url",
      "origin",
      "https://example.invalid/nope.git",
    );
    setup(newer);
    expect(head(target)).toBe(newer);
  });
});

describe("tarski/test262/pin.json", () => {
  const pin = JSON.parse(
    readFileSync(path.join(root, "tarski", "test262", "pin.json"), "utf8"),
  ) as { repository: string; commit: string; date: string };

  it("names a 40-hex-digit commit", () => {
    expect(pin.commit).toMatch(/^[0-9a-f]{40}$/);
  });

  it("names the upstream suite", () => {
    expect(pin.repository).toBe("https://github.com/tc39/test262.git");
  });
});
