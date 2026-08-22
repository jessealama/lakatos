import { describe, expect, test } from 'vitest';
import {
  transcribe,
  transcribeFile,
  transcribeSource,
} from '../src/transcribe.js';

describe('mappable function declarations', () => {
  test('a number-typed function becomes a ts_def with its source as comments', () => {
    const src = [
      'function add(a: number, b: number): number {',
      '  return a + b;',
      '}',
      '',
    ].join('\n');

    expect(transcribeSource(src, 'add.ts')).toBe(
      [
        'import ThalesDsl',
        '',
        '-- function add(a: number, b: number): number {',
        '--   return a + b;',
        '-- }',
        'ts_def "add" := ts.fn(ts.param["a"](ts.number), ts.param["b"](ts.number)) : ts.number {',
        '  ts.return(ts.binop["+"](ts.id["a"], ts.id["b"]))',
        '}',
        '',
      ].join('\n'),
    );
  });
});

test('a blank line inside a declaration becomes a bare comment marker', () => {
  const src = 'function f(a: number): number {\n\n  return a;\n}';
  expect(transcribeSource(src, 't.ts').split('\n')).toContain('--');
});

/** The emitted ts_def body lines (between the ts_def header and `}`). */
function bodyOf(src: string, file = 't.ts'): string[] {
  const lines = transcribeSource(src, file).split('\n');
  const start = lines.findIndex((l) => l.startsWith('ts_def '));
  const end = lines.indexOf('}', start);
  expect(start).toBeGreaterThan(-1);
  expect(end).toBeGreaterThan(start);
  return lines.slice(start + 1, end).map((l) => l.trim());
}

describe('expression kinds', () => {
  test('integer literals become ts.num', () => {
    expect(bodyOf('function one(): number { return 42; }')).toEqual([
      'ts.return(ts.num[42])',
    ]);
  });

  test('negated integer literals become negative ts.num', () => {
    expect(bodyOf('function neg(): number { return -7; }')).toEqual([
      'ts.return(ts.num[-7])',
    ]);
  });

  test('calls with identifier callees become ts.call', () => {
    expect(
      bodyOf('function twice(a: number): number { return add(a, a); }'),
    ).toEqual(['ts.return(ts.call["add"](ts.id["a"], ts.id["a"]))']);
  });

  test('parenthesized expressions are unwrapped', () => {
    expect(bodyOf('function p(a: number): number { return (a); }')).toEqual([
      'ts.return(ts.id["a"])',
    ]);
  });
});

describe('opaque fallbacks', () => {
  test('an unmapped expression becomes an opaque node at its 1-based position', () => {
    const src = [
      'function f(x: number): number {',
      '  return await remote(x);',
      '}',
    ].join('\n');
    expect(bodyOf(src)).toEqual([
      'ts.return(ts.opaque["AwaitExpression"](2, 10))',
    ]);
  });

  test('a non-integer numeric literal becomes an opaque node', () => {
    expect(bodyOf('function h(): number { return 0.5; }')).toEqual([
      'ts.return(ts.opaque["NumericLiteral"](1, 31))',
    ]);
  });

  test('a call through a property access becomes an opaque node', () => {
    expect(
      bodyOf('function m(a: number): number { return Math.abs(a); }'),
    ).toEqual(['ts.return(ts.opaque["CallExpression"](1, 40))']);
  });

  test('an unmapped statement becomes an opaque node, later statements still map', () => {
    const src = [
      'function spin(n: number): number {',
      '  while (true) {}',
      '  return n;',
      '}',
    ].join('\n');
    expect(bodyOf(src)).toEqual([
      'ts.opaque["WhileStatement"](2, 3)',
      'ts.return(ts.id["n"])',
    ]);
  });

  test('a bare return becomes an opaque statement', () => {
    expect(bodyOf('function v(): number { return; }')).toEqual([
      'ts.opaque["ReturnStatement"](1, 24)',
    ]);
  });
});

/** All emitted ts_def lines, in order. */
function defsOf(src: string, file = 't.ts'): string[] {
  return transcribeSource(src, file)
    .split('\n')
    .filter((l) => l.startsWith('ts_def '));
}

describe('unmappable declarations', () => {
  test('a non-number parameter type makes the declaration an opaque ts_def naming it', () => {
    expect(defsOf('function greet(s: string): number { return 1; }')).toEqual([
      'ts_def "greet" := ts.opaque["StringKeyword"](1, 19)',
    ]);
  });

  test('a missing return type makes the declaration opaque at the function itself', () => {
    expect(defsOf('function f(a: number) { return a; }')).toEqual([
      'ts_def "f" := ts.opaque["FunctionDeclaration"](1, 1)',
    ]);
  });

  test('an async function is opaque at its modifier', () => {
    expect(defsOf('async function f(a: number): number { return a; }')).toEqual(
      ['ts_def "f" := ts.opaque["AsyncKeyword"](1, 1)'],
    );
  });

  test('a generator function is opaque', () => {
    expect(defsOf('function* gen(a: number): number { return a; }')).toEqual([
      'ts_def "gen" := ts.opaque["AsteriskToken"](1, 9)',
    ]);
  });

  test('an exported function still maps normally', () => {
    expect(
      defsOf('export function id(a: number): number { return a; }'),
    ).toEqual(['ts_def "id" := ts.fn(ts.param["a"](ts.number)) : ts.number {']);
  });

  test('variable declarators are opaque ts_defs, one per name', () => {
    expect(
      defsOf('const inc = (a: number): number => a + 1, LIMIT = 10;'),
    ).toEqual([
      'ts_def "inc" := ts.opaque["VariableStatement"](1, 7)',
      'ts_def "LIMIT" := ts.opaque["VariableStatement"](1, 43)',
    ]);
  });

  test('a class emits an opaque ts_def for itself and each named member', () => {
    const src = [
      'class Point {',
      '  norm(): number { return 0; }',
      '  static origin(): Point { return new Point(); }',
      '}',
    ].join('\n');
    expect(defsOf(src)).toEqual([
      'ts_def "Point" := ts.opaque["ClassDeclaration"](1, 7)',
      'ts_def "Point#norm" := ts.opaque["ClassDeclaration"](2, 3)',
      'ts_def "Point.origin" := ts.opaque["ClassDeclaration"](3, 10)',
    ]);
  });

  test('enums, interfaces, and type aliases are opaque ts_defs by name', () => {
    const src = [
      'enum Color { Red }',
      'interface Shape { area(): number; }',
      'type Id = number;',
    ].join('\n');
    expect(defsOf(src)).toEqual([
      'ts_def "Color" := ts.opaque["EnumDeclaration"](1, 6)',
      'ts_def "Shape" := ts.opaque["InterfaceDeclaration"](2, 11)',
      'ts_def "Id" := ts.opaque["TypeAliasDeclaration"](3, 6)',
    ]);
  });

  test('import bindings are opaque ts_defs, one per bound name', () => {
    const src = 'import dflt, { g, h as k } from "./x";';
    expect(defsOf(src)).toEqual([
      'ts_def "dflt" := ts.opaque["ImportDeclaration"](1, 8)',
      'ts_def "g" := ts.opaque["ImportDeclaration"](1, 16)',
      'ts_def "k" := ts.opaque["ImportDeclaration"](1, 24)',
    ]);
  });

  test('signature variants each block at the offending node', () => {
    expect(
      defsOf('function f({ a }: { a: number }): number { return 1; }'),
    ).toEqual(['ts_def "f" := ts.opaque["ObjectBindingPattern"](1, 12)']);
    expect(
      defsOf('function f(...rest: number[]): number { return 1; }'),
    ).toEqual(['ts_def "f" := ts.opaque["DotDotDotToken"](1, 12)']);
    expect(defsOf('function f(a?: number): number { return 1; }')).toEqual([
      'ts_def "f" := ts.opaque["Parameter"](1, 12)',
    ]);
    expect(defsOf('function f(a: number = 3): number { return a; }')).toEqual([
      'ts_def "f" := ts.opaque["Parameter"](1, 12)',
    ]);
    expect(defsOf('function f(a): number { return a; }')).toEqual([
      'ts_def "f" := ts.opaque["Parameter"](1, 12)',
    ]);
    expect(defsOf('function f(a: number): string { return "x"; }')).toEqual([
      'ts_def "f" := ts.opaque["StringKeyword"](1, 24)',
    ]);
    expect(defsOf('declare function f(a: number): number;')).toEqual([
      'ts_def "f" := ts.opaque["DeclareKeyword"](1, 1)',
    ]);
    expect(defsOf('function f(a: number): number;')).toEqual([
      'ts_def "f" := ts.opaque["FunctionDeclaration"](1, 1)',
    ]);
  });

  test('destructuring declarators bind every identifier in the pattern', () => {
    expect(defsOf('const { x, y } = pos, [p, q] = pair;')).toEqual([
      'ts_def "x" := ts.opaque["VariableStatement"](1, 9)',
      'ts_def "y" := ts.opaque["VariableStatement"](1, 12)',
      'ts_def "p" := ts.opaque["VariableStatement"](1, 24)',
      'ts_def "q" := ts.opaque["VariableStatement"](1, 27)',
    ]);
  });

  test('an anonymous class yields no ts_defs', () => {
    expect(
      defsOf('export default class { m(): number { return 1; } }'),
    ).toEqual([]);
  });

  test('non-identifier class member names are skipped', () => {
    const src = ['class C { ["computed"](): number { return 1; } }'].join('\n');
    expect(defsOf(src)).toEqual([
      'ts_def "C" := ts.opaque["ClassDeclaration"](1, 7)',
    ]);
  });

  test('a namespace import binds its alias; a bare import binds nothing', () => {
    expect(defsOf('import * as ns from "./x";')).toEqual([
      'ts_def "ns" := ts.opaque["ImportDeclaration"](1, 13)',
    ]);
    expect(defsOf('import "./side-effect";')).toEqual([]);
  });

  test('nameless top-level constructs appear as source comments only', () => {
    const out = transcribeSource('console.log("hi");\n', 't.ts');
    expect(out).toContain('-- console.log("hi");');
    expect(out).not.toContain('ts_def');
  });
});

const ADD = [
  '/** @ensures{commutes} forall (a: int ∈ [0, 10)) (b: int ∈ [0, 10)) { add(a, b) ≡ add(b, a) } */',
  'export function add(a: number, b: number): number {',
  '  return a + b;',
  '}',
].join('\n');

/** The lines of the #thales_prove section for `src`, one entry per line. */
function provesOf(src: string, file = 't.ts'): string[] {
  const lines = transcribeSource(src, file).split('\n');
  const start = lines.findIndex((l) => l.startsWith('#thales_prove'));
  return start === -1 ? [] : lines.slice(start).filter((l) => l !== '');
}

describe('annotations', () => {
  test('an equation over bounded int binders becomes a structured ts.eq property', () => {
    expect(provesOf(ADD, 'add.ts')).toEqual([
      '#thales_prove "add.ts" "add" "commutes" :=',
      '  ts.forall(ts.binder["a"](ts.int, ts.range(0, 10)), ts.binder["b"](ts.int, ts.range(0, 10))) {',
      '    ts.eq(ts.call["add"](ts.id["a"], ts.id["b"]), ts.call["add"](ts.id["b"], ts.id["a"]))',
      '  }',
    ]);
  });

  test('the formula appears as a comment above its #thales_prove', () => {
    const out = transcribeSource(ADD, 'add.ts');
    expect(out).toContain(
      '-- @ensures{commutes} forall (a: int ∈ [0, 10)) (b: int ∈ [0, 10)) { add(a, b) ≡ add(b, a) }',
    );
  });

  test('a boolean atom becomes ts.istrue', () => {
    const src = [
      '/** @ensures{grows} forall (a: int ∈ [-5, 5)) { add1(a) > a } */',
      'function add1(a: number): number { return a + 1; }',
    ].join('\n');
    expect(provesOf(src)).toEqual([
      '#thales_prove "t.ts" "add1" "grows" :=',
      '  ts.forall(ts.binder["a"](ts.int, ts.range(-5, 5))) {',
      '    ts.istrue(ts.binop[">"](ts.call["add1"](ts.id["a"]), ts.id["a"]))',
      '  }',
    ]);
  });

  test('open-min and closed-max endpoints normalize to the half-open range', () => {
    const src = [
      '/** @ensures{p} forall (a: int ∈ (0, 10]) { f(a) > 0 } */',
      'function f(a: number): number { return a; }',
    ].join('\n');
    expect(provesOf(src)[1]).toBe(
      '  ts.forall(ts.binder["a"](ts.int, ts.range(1, 11))) {',
    );
  });

  test('a negative nat lower bound floors at 0', () => {
    const src = [
      '/** @ensures{p} forall (k: nat ∈ (-2, 5]) { f(k) >= 0 } */',
      'function f(k: number): number { return k; }',
    ].join('\n');
    expect(provesOf(src)[1]).toBe(
      '  ts.forall(ts.binder["k"](ts.int, ts.range(0, 6))) {',
    );
  });

  test('an unbounded int binder lowers to ts.binder[..](ts.int)', () => {
    const src = [
      '/** @ensures{p} forall (x: int) { f(x) === x + x } */',
      'export function f(x: number): number { return x * 2; }',
    ].join('\n');
    const out = transcribeSource(src, 'f.ts');
    expect(out).toContain('ts.binder["x"](ts.int)');
    expect(out).toContain('#thales_prove "f.ts" "f" "p" :=');
  });

  test('transcribes a number binder as bounds, not a range', () => {
    const src = [
      '/** @ensures{id} forall (a: number ∈ (0, 1]) { f(a) ≡ a } */',
      'export function f(a: number): number { return a; }',
    ].join('\n');
    const out = transcribeSource(src, 'n.ts');
    expect(out).toContain('ts.binder["a"](ts.number');
    expect(out).toContain('ts.lower["<"](ts.fnum[0])');
    expect(out).toContain('ts.upper["<="](ts.fnum[1])');
  });

  /** An interval always guards both sides: an ∞ endpoint bounds against the
   * literal infinity, strictly when open (excluding that infinity and NaN)
   * and non-strictly when closed (excluding only NaN, which no comparison
   * admits). Only a binder with no interval at all leaves the whole Float
   * line — NaN included — matching the refuter's bare fc.double(). */
  describe('a number binder with infinite endpoints', () => {
    const loweringOf = (binder: string) => {
      const src = [
        `/** @ensures{id} forall (${binder}) { f(a) ≡ a } */`,
        'export function f(a: number): number { return a; }',
      ].join('\n');
      return transcribeSource(src, 'u.ts');
    };

    test('no interval at all carries no bounds', () => {
      expect(loweringOf('a: number')).toContain('ts.binder["a"](ts.number)');
    });

    test('an open ∞ side bounds strictly against that infinity', () => {
      expect(loweringOf('a: number ∈ [0, ∞)')).toContain(
        'ts.binder["a"](ts.number, ts.lower["<="](ts.fnum[0]), ts.upper["<"](ts.fnum[Infinity]))',
      );
      expect(loweringOf('a: number ∈ (-∞, 1]')).toContain(
        'ts.binder["a"](ts.number, ts.lower["<"](ts.fnum[-Infinity]), ts.upper["<="](ts.fnum[1]))',
      );
    });

    test('(0, ∞) is the epic shape: strict on both sides', () => {
      expect(loweringOf('a: number ∈ (0, ∞)')).toContain(
        'ts.binder["a"](ts.number, ts.lower["<"](ts.fnum[0]), ts.upper["<"](ts.fnum[Infinity]))',
      );
    });

    test('(-∞, ∞) bounds strictly against both infinities', () => {
      expect(loweringOf('a: number ∈ (-∞, ∞)')).toContain(
        'ts.binder["a"](ts.number, ts.lower["<"](ts.fnum[-Infinity]), ts.upper["<"](ts.fnum[Infinity]))',
      );
    });

    test('a closed ∞ side bounds non-strictly, excluding only NaN', () => {
      expect(loweringOf('a: number ∈ [-∞, ∞]')).toContain(
        'ts.binder["a"](ts.number, ts.lower["<="](ts.fnum[-Infinity]), ts.upper["<="](ts.fnum[Infinity]))',
      );
      expect(loweringOf('a: number ∈ (-∞, ∞]')).toContain(
        'ts.binder["a"](ts.number, ts.lower["<"](ts.fnum[-Infinity]), ts.upper["<="](ts.fnum[Infinity]))',
      );
    });
  });

  /** IEEE comparison cannot separate -0 from 0, so an open bound at the zero
   * the interval still admits has to relax: the prover's domain must stay a
   * superset of the refuter's, never a subset. */
  describe('a number bound at a signed zero', () => {
    const boundsOf = (interval: string) => {
      const src = [
        `/** @ensures{id} forall (a: number ∈ ${interval}) { f(a) ≡ a } */`,
        'export function f(a: number): number { return a; }',
      ].join('\n');
      return transcribeSource(src, 'z.ts');
    };

    test('an open lower bound at -0 relaxes, since 0 is in the domain', () => {
      expect(boundsOf('(-0, 1]')).toContain('ts.lower["<="](ts.fnum[-0])');
    });

    test('an open upper bound at 0 relaxes, since -0 is in the domain', () => {
      expect(boundsOf('[-1, 0)')).toContain('ts.upper["<="](ts.fnum[0])');
    });

    test('an open lower bound at 0 stays strict: it excludes both zeros', () => {
      expect(boundsOf('(0, 1]')).toContain('ts.lower["<"](ts.fnum[0])');
    });

    test('an open upper bound at -0 stays strict: it excludes both zeros', () => {
      expect(boundsOf('[-1, -0)')).toContain('ts.upper["<"](ts.fnum[-0])');
    });

    test('a closed bound at either zero is unaffected', () => {
      expect(boundsOf('[-0, 1]')).toContain('ts.lower["<="](ts.fnum[-0])');
      expect(boundsOf('[-1, 0]')).toContain('ts.upper["<="](ts.fnum[0])');
    });
  });

  test('an unbounded nat binder lowers to ts.binder[..](ts.nat)', () => {
    const src = [
      '/** @ensures{p} forall (x: nat) { f(x) >= x } */',
      'export function f(x: number): number { return x * 2; }',
    ].join('\n');
    expect(transcribeSource(src, 'f.ts')).toContain('ts.binder["x"](ts.nat)');
  });

  test('int ∈ [0, ∞) lowers exactly as the nat domain it denotes', () => {
    const withRange = [
      '/** @ensures{p} forall (x: int ∈ [0, ∞)) { f(x) >= 0 } */',
      'export function f(x: number): number { return x * 2; }',
    ].join('\n');
    const bareNat = [
      '/** @ensures{p} forall (x: nat) { f(x) >= 0 } */',
      'export function f(x: number): number { return x * 2; }',
    ].join('\n');
    expect(provesOf(withRange, 'f.ts')).toEqual(provesOf(bareNat, 'f.ts'));
    expect(provesOf(withRange, 'f.ts')[1]).toBe(
      '  ts.forall(ts.binder["x"](ts.nat)) {',
    );
  });

  test('an open lower endpoint below 0 on int is the nat domain too', () => {
    const src = [
      '/** @ensures{p} forall (x: int ∈ (-1, ∞)) { f(x) >= 0 } */',
      'export function f(x: number): number { return x * 2; }',
    ].join('\n');
    expect(provesOf(src)[1]).toBe('  ts.forall(ts.binder["x"](ts.nat)) {');
  });

  test('nat ∈ (-∞, 10] elaborates as the bounded domain it denotes', () => {
    const src = [
      '/** @ensures{p} forall (x: nat ∈ (-∞, 10]) { f(x) >= 0 } */',
      'export function f(x: number): number { return x * 2; }',
    ].join('\n');
    expect(provesOf(src)[1]).toBe(
      '  ts.forall(ts.binder["x"](ts.int, ts.range(0, 11))) {',
    );
  });

  test('a doubly unbounded int range is the whole int domain', () => {
    const src = [
      '/** @ensures{p} forall (x: int ∈ (-∞, ∞)) { f(x) >= 0 } */',
      'export function f(x: number): number { return x * 2; }',
    ].join('\n');
    expect(provesOf(src)[1]).toBe('  ts.forall(ts.binder["x"](ts.int)) {');
  });

  test('an int range unbounded above with a nonzero floor stays bare', () => {
    const src = [
      '/** @ensures{p} forall (x: int ∈ [5, ∞)) { f(x) >= 0 } */',
      'export function f(x: number): number { return x * 2; }',
    ].join('\n');
    expect(provesOf(src, 'f.ts')).toEqual(['#thales_prove "f.ts" "f" "p"']);
  });

  test('an int range unbounded below is never clamped to the safe range', () => {
    const src = [
      '/** @ensures{p} forall (x: int ∈ (-∞, 3]) { f(x) >= 0 } */',
      'export function f(x: number): number { return x * 2; }',
    ].join('\n');
    const out = transcribeSource(src, 'f.ts');
    expect(out).not.toContain('ts.range');
    expect(provesOf(src, 'f.ts')).toEqual(['#thales_prove "f.ts" "f" "p"']);
  });

  describe('guard-chain implications structure as nested ts.imp', () => {
    test('a single guard wraps the conclusion', () => {
      const src = [
        '/** @ensures{mono} forall (x: int ∈ [0, 10)) (y: int ∈ [0, 10)) { x <= y → f(x) <= f(y) } */',
        'function f(a: number): number { return a; }',
      ].join('\n');
      expect(provesOf(src)).toEqual([
        '#thales_prove "t.ts" "f" "mono" :=',
        '  ts.forall(ts.binder["x"](ts.int, ts.range(0, 10)), ts.binder["y"](ts.int, ts.range(0, 10))) {',
        '    ts.imp(ts.binop["<="](ts.id["x"], ts.id["y"])) { ts.istrue(ts.binop["<="](ts.call["f"](ts.id["x"]), ts.call["f"](ts.id["y"]))) }',
        '  }',
      ]);
    });

    test('a two-guard chain nests right, in guard order', () => {
      const src = [
        '/** @ensures{p} forall (x: int ∈ [0, 10)) { x >= 1 → x >= 2 → f(x) >= 2 } */',
        'function f(a: number): number { return a; }',
      ].join('\n');
      expect(provesOf(src)).toEqual([
        '#thales_prove "t.ts" "f" "p" :=',
        '  ts.forall(ts.binder["x"](ts.int, ts.range(0, 10))) {',
        '    ts.imp(ts.binop[">="](ts.id["x"], ts.num[1])) { ts.imp(ts.binop[">="](ts.id["x"], ts.num[2])) { ts.istrue(ts.binop[">="](ts.call["f"](ts.id["x"]), ts.num[2])) } }',
        '  }',
      ]);
    });

    test('an equation conclusion keeps its ts.eq shape under the guard', () => {
      const src = [
        '/** @ensures{p} forall (x: int ∈ [0, 10)) { x >= 1 → f(x) ≡ x } */',
        'function f(a: number): number { return a; }',
      ].join('\n');
      expect(provesOf(src)).toEqual([
        '#thales_prove "t.ts" "f" "p" :=',
        '  ts.forall(ts.binder["x"](ts.int, ts.range(0, 10))) {',
        '    ts.imp(ts.binop[">="](ts.id["x"], ts.num[1])) { ts.eq(ts.call["f"](ts.id["x"]), ts.id["x"]) }',
        '  }',
      ]);
    });

    test('an antecedent that is not valid JavaScript falls back to the bare form', () => {
      const src = [
        '/** @ensures{p} forall (x: int ∈ [0, 10)) { x is wonderful → f(x) >= 0 } */',
        'function f(a: number): number { return a; }',
      ].join('\n');
      expect(provesOf(src)).toEqual(['#thales_prove "t.ts" "f" "p"']);
    });

    test('an equation antecedent falls back to the bare form', () => {
      // `x ≡ 0` desugars to Object.is, which has no boolean-expression
      // node in the DSL; emitting it opaquely would misreport an in-spec
      // formula as Inappropriate, so the property stays NotTried.
      const src = [
        '/** @ensures{p} forall (x: int ∈ [0, 10)) { x ≡ 0 → f(x) ≡ 0 } */',
        'function f(a: number): number { return a; }',
      ].join('\n');
      expect(provesOf(src)).toEqual(['#thales_prove "t.ts" "f" "p"']);
    });

    test('a negated-equation antecedent falls back to the bare form', () => {
      const src = [
        '/** @ensures{p} forall (x: int ∈ [0, 10)) { x ≢ 0 → f(x) ≡ x } */',
        'function f(a: number): number { return a; }',
      ].join('\n');
      expect(provesOf(src)).toEqual(['#thales_prove "t.ts" "f" "p"']);
    });

    test('a connective antecedent falls back to the bare form', () => {
      const src = [
        '/** @ensures{p} forall (x: int ∈ [0, 10)) { x >= 1 ∧ x >= 2 → f(x) >= 2 } */',
        'function f(a: number): number { return a; }',
      ].join('\n');
      expect(provesOf(src)).toEqual(['#thales_prove "t.ts" "f" "p"']);
    });

    test('a connective conclusion falls back to the bare form', () => {
      const src = [
        '/** @ensures{p} forall (x: int ∈ [0, 10)) { x >= 1 → f(x) >= 0 ∨ f(x) < 0 } */',
        'function f(a: number): number { return a; }',
      ].join('\n');
      expect(provesOf(src)).toEqual(['#thales_prove "t.ts" "f" "p"']);
    });
  });

  test('a connective body falls back to the bare NotTried form', () => {
    const src = [
      '/** @ensures{p} forall (a: int ∈ [0, 5)) { f(a) >= 0 ∧ f(a) < 9 } */',
      'function f(a: number): number { return a; }',
    ].join('\n');
    expect(provesOf(src)).toEqual(['#thales_prove "t.ts" "f" "p"']);
  });

  test('non-integer range endpoints fall back to the bare form', () => {
    const src = [
      '/** @ensures{p} forall (a: int ∈ [1e2, 200)) { f(a) >= 0 } */',
      'function f(a: number): number { return a; }',
    ].join('\n');
    expect(provesOf(src)).toEqual(['#thales_prove "t.ts" "f" "p"']);
  });

  test('a two-argument call that is not Object.is stays a boolean island', () => {
    const src = [
      '/** @ensures{p} forall (a: int ∈ [0, 5)) { agree(a, a) } */',
      'function agree(a: number, b: number): number { return a; }',
    ].join('\n');
    expect(provesOf(src)[2]).toBe(
      '    ts.istrue(ts.call["agree"](ts.id["a"], ts.id["a"]))',
    );
  });

  test('Object.is lookalikes are not treated as equations', () => {
    const src = [
      '/**',
      ' * @ensures{p} forall (a: int ∈ [0, 5)) { Objects.is(a, a) }',
      ' * @ensures{q} forall (a: int ∈ [0, 5)) { Object.equals(a, a) }',
      ' */',
      'function f(a: number): number { return a; }',
    ].join('\n');
    const proves = provesOf(src);
    expect(proves.filter((l) => l.includes('ts.eq('))).toEqual([]);
    expect(proves.filter((l) => l.includes('ts.istrue(ts.opaque')).length).toBe(
      2,
    );
  });

  test('an atom that is not valid JavaScript falls back to the bare form', () => {
    const src = [
      '/** @ensures{p} forall (a: int ∈ [0, 5)) { f(a) is wonderful } */',
      'function f(a: number): number { return a; }',
    ].join('\n');
    expect(provesOf(src)).toEqual(['#thales_prove "t.ts" "f" "p"']);
  });

  test('a domain the DSL has no binder shape for falls back to the bare form', () => {
    const src = [
      '/** @ensures{p} forall (x: bigint ∈ [0, 10]) { f(x) >= 0 } */',
      'function f(x: number): number { return x; }',
    ].join('\n');
    expect(provesOf(src)).toEqual(['#thales_prove "t.ts" "f" "p"']);
  });

  test('a half-bounded range the DSL has no shape for falls back to the bare form', () => {
    const src = [
      '/** @ensures{p} forall (a: int ∈ [3, ∞)) { f(a) >= 0 } */',
      'function f(a: number): number { return a; }',
    ].join('\n');
    expect(provesOf(src)).toEqual(['#thales_prove "t.ts" "f" "p"']);
  });

  test('a formula the Lemma parser rejects still emits the bare form', () => {
    const src = [
      '/** @ensures{p} whenever the moon is full { f(a) ≡ a } */',
      'function f(a: number): number { return a; }',
    ].join('\n');
    expect(provesOf(src)).toEqual(['#thales_prove "t.ts" "f" "p"']);
  });

  test('class-method annotations carry the qualified name', () => {
    const src = [
      'export class Point {',
      '  /** @ensures{p} forall (a: int ∈ [0, 5)) { norm(a) >= 0 } */',
      '  norm(a: number): number { return a; }',
      '}',
    ].join('\n');
    expect(provesOf(src)[0]).toBe('#thales_prove "t.ts" "Point#norm" "p" :=');
  });

  test('all ts_defs precede all #thales_prove commands', () => {
    const src = [
      ADD,
      '',
      '/** @ensures{q} forall (x: int ∈ [0, 5)) { sq(x) >= 0 } */',
      'function sq(x: number): number { return x * x; }',
    ].join('\n');
    const lines = transcribeSource(src, 'two.ts').split('\n');
    const lastDef = lines.reduce(
      (acc, l, i) => (l.startsWith('ts_def') ? i : acc),
      -1,
    );
    const firstProve = lines.findIndex((l) => l.startsWith('#thales_prove'));
    expect(lastDef).toBeGreaterThan(-1);
    expect(firstProve).toBeGreaterThan(lastDef);
  });
});

describe('clamped ranges', () => {
  const HUGE = '1000000000000000000000000000000';

  test('an endpoint beyond the safe range yields no prove command and an untried record', () => {
    const src = [
      `/** @ensures{p} forall (a: int ∈ [0, ${HUGE}]) { f(a) >= 0 } */`,
      'function f(a: number): number { return a; }',
    ].join('\n');
    const { lean, untried } = transcribe(src, 't.ts');
    expect(lean).not.toContain('#thales_prove');
    expect(untried).toEqual([
      {
        annotation: expect.objectContaining({
          functionName: 'f',
          propertyName: 'p',
        }),
        kind: 'unsupported-range',
        reason: `endpoint ${HUGE} exceeds the safe integer range (±9007199254740991)`,
      },
    ]);
  });

  test('a huge negative lower endpoint is the one named', () => {
    const src = [
      `/** @ensures{p} forall (a: int ∈ [-${HUGE}, 5]) { f(a) >= 0 } */`,
      'function f(a: number): number { return a; }',
    ].join('\n');
    const { untried } = transcribe(src, 't.ts');
    expect(untried[0]!.reason).toBe(
      `endpoint -${HUGE} exceeds the safe integer range (±9007199254740991)`,
    );
  });

  test('both clamped endpoints are named together', () => {
    const src = [
      `/** @ensures{p} forall (a: int ∈ [-${HUGE}, ${HUGE}]) { f(a) >= 0 } */`,
      'function f(a: number): number { return a; }',
    ].join('\n');
    const { untried } = transcribe(src, 't.ts');
    expect(untried[0]!.reason).toBe(
      `endpoints -${HUGE} and ${HUGE} exceed the safe integer range (±9007199254740991)`,
    );
  });

  test('an interval empty after the clamp is unsupported-range, naming both endpoints', () => {
    const src = [
      `/** @ensures{p} forall (a: int ∈ [${HUGE}, ${HUGE}0]) { f(a) >= 0 } */`,
      'function f(a: number): number { return a; }',
    ].join('\n');
    const { lean, untried } = transcribe(src, 't.ts');
    expect(lean).not.toContain('#thales_prove');
    expect(untried).toEqual([
      {
        annotation: expect.objectContaining({
          functionName: 'f',
          propertyName: 'p',
        }),
        kind: 'unsupported-range',
        reason: `endpoints ${HUGE} and ${HUGE}0 exceed the safe integer range (±9007199254740991)`,
      },
    ]);
  });

  test('a nat interval unbounded below is bounded by the floor, so its huge ceiling clamps', () => {
    const src = [
      `/** @ensures{p} forall (a: nat ∈ (-∞, ${HUGE}]) { f(a) >= 0 } */`,
      'function f(a: number): number { return a; }',
    ].join('\n');
    const { lean, untried } = transcribe(src, 't.ts');
    expect(lean).not.toContain('#thales_prove');
    expect(untried).toEqual([
      {
        annotation: expect.objectContaining({
          functionName: 'f',
          propertyName: 'p',
        }),
        kind: 'unsupported-range',
        reason: `endpoint ${HUGE} exceeds the safe integer range (±9007199254740991)`,
      },
    ]);
  });

  test('an int interval unbounded below is bare, never clamp-reported', () => {
    const src = [
      `/** @ensures{p} forall (a: int ∈ (-∞, ${HUGE}]) { f(a) >= 0 } */`,
      'function f(a: number): number { return a; }',
    ].join('\n');
    const { lean, untried } = transcribe(src, 't.ts');
    expect(untried).toEqual([]);
    expect(lean).toContain('#thales_prove "t.ts" "f" "p"');
  });

  test('an interval genuinely empty within the safe range keeps its bare command', () => {
    const src = [
      '/** @ensures{p} forall (a: int ∈ [5, 3]) { f(a) >= 0 } */',
      'function f(a: number): number { return a; }',
    ].join('\n');
    const { lean, untried } = transcribe(src, 't.ts');
    expect(untried).toEqual([]);
    expect(lean).toContain('#thales_prove "t.ts" "f" "p"');
  });

  test('the artifact records the untried annotation as a comment', () => {
    const src = [
      `/** @ensures{p} forall (a: int ∈ [0, ${HUGE}]) { f(a) >= 0 } */`,
      'function f(a: number): number { return a; }',
    ].join('\n');
    const { lean } = transcribe(src, 't.ts');
    expect(lean).toMatch(
      /^-- not tried @ensures\{p\} on f: endpoint 1000000000000000000000000000000 exceeds the safe integer range/m,
    );
  });

  test('other annotations in the same file still transcribe', () => {
    const src = [
      `/** @ensures{big} forall (a: int ∈ [0, ${HUGE}]) { f(a) >= 0 } */`,
      'function f(a: number): number { return a; }',
      '',
      '/** @ensures{small} forall (x: int ∈ [0, 5)) { g(x) >= 0 } */',
      'function g(x: number): number { return x; }',
    ].join('\n');
    const { lean, untried } = transcribe(src, 't.ts');
    expect(lean).toContain('#thales_prove "t.ts" "g" "small" :=');
    expect(lean).not.toContain('#thales_prove "t.ts" "f" "big"');
    expect(untried).toHaveLength(1);
  });

  test('an in-range annotation produces no untried records', () => {
    expect(transcribe(ADD, 'add.ts').untried).toEqual([]);
  });

  test('a clamped range alongside an unmappable binder degrades to bare, either order', () => {
    for (const binders of [
      `(a: int ∈ [0, ${HUGE}]) (s: string)`,
      `(s: string) (a: int ∈ [0, ${HUGE}])`,
    ]) {
      const src = [
        `/** @ensures{p} forall ${binders} { f(a) >= 0 } */`,
        'function f(a: number): number { return a; }',
      ].join('\n');
      const { lean, untried } = transcribe(src, 't.ts');
      expect(untried).toEqual([]);
      expect(lean).toContain('#thales_prove "t.ts" "f" "p"');
    }
  });

  test('a clamped range with an unstructurable body degrades to bare', () => {
    const src = [
      `/** @ensures{p} forall (a: int ∈ [0, ${HUGE}]) { f(a) >= 0 ∧ f(a) < 9 } */`,
      'function f(a: number): number { return a; }',
    ].join('\n');
    const { lean, untried } = transcribe(src, 't.ts');
    expect(untried).toEqual([]);
    expect(lean).toContain('#thales_prove "t.ts" "f" "p"');
  });

  test('clamped endpoints across two binders are named together', () => {
    const src = [
      `/** @ensures{p} forall (a: int ∈ [-${HUGE}, 5]) (b: int ∈ [0, ${HUGE}]) { f(a) >= b } */`,
      'function f(a: number): number { return a; }',
    ].join('\n');
    const { untried } = transcribe(src, 't.ts');
    expect(untried[0]!.reason).toBe(
      `endpoints -${HUGE} and ${HUGE} exceed the safe integer range (±9007199254740991)`,
    );
  });
});

describe('the tracer fixture', () => {
  test('transcribeFile reads the fixture and covers all three verdict paths', () => {
    const out = transcribeFile('engines/thales/tests/fixtures/tracer.ts');
    expect(out).toContain(
      'ts_def "add" := ts.fn(ts.param["a"](ts.number), ts.param["b"](ts.number)) : ts.number {',
    );
    expect(out).toContain('ts.opaque["AwaitExpression"]');
    expect(out).toContain(
      'ts_def "Counter#bump" := ts.opaque["ClassDeclaration"]',
    );
    expect(out).toContain(
      '#thales_prove "engines/thales/tests/fixtures/tracer.ts" "add" "commutes" :=',
    );
    expect(out).toContain(
      '#thales_prove "engines/thales/tests/fixtures/tracer.ts" "Counter#bump" "bumps" :=',
    );
  });
});

describe('invalid annotations', () => {
  const hidden = [
    'class Hidden {',
    '  /** @ensures{p} forall (x: int ∈ [0, 5)) { id(x) === x } */',
    '  static id(x: number): number { return x; }',
    '}',
    '',
    '/** @ensures{q} forall (x: int ∈ [0, 5)) { ok(x) === x } */',
    'export function ok(x: number): number { return x; }',
    '',
  ].join('\n');

  test('skipped annotations become comments, not prove commands', () => {
    const lean = transcribeSource(hidden, 'hidden.ts');
    expect(lean).toMatch(
      /^-- skipped @ensures\{p\} on Hidden\.id: hidden\.ts:2: /m,
    );
    expect(lean).not.toContain('#thales_prove "hidden.ts" "Hidden.id"');
    expect(lean).toContain('#thales_prove "hidden.ts" "ok" "q"');
  });

  test('files with only valid annotations gain no skipped block', () => {
    const src =
      '/** @ensures{q} forall (x: int ∈ [0, 5)) { f(x) === x } */\nexport function f(x: number): number { return x; }\n';
    expect(transcribeSource(src, 'f.ts')).not.toContain('-- skipped');
  });

  test('transcribe returns the annotations and invalid entries', () => {
    const t = transcribe(hidden, 'hidden.ts');
    expect(t.annotations.map((a) => a.propertyName)).toEqual(['q']);
    expect(t.invalid.map((i) => i.propertyName)).toEqual(['p']);
    expect(t.lean).toBe(transcribeSource(hidden, 'hidden.ts'));
  });
});
