import { describe, expect, test } from 'vitest';
import { transcribeFile, transcribeSource } from '../src/transcribe.js';

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

  test('a non-integer domain falls back to the bare form', () => {
    const src = [
      '/** @ensures{p} forall (x: number ∈ [0, 1]) { f(x) >= 0 } */',
      'function f(x: number): number { return x; }',
    ].join('\n');
    expect(provesOf(src)).toEqual(['#thales_prove "t.ts" "f" "p"']);
  });

  test('an unbounded range falls back to the bare form', () => {
    const src = [
      '/** @ensures{p} forall (a: int ∈ [0, ∞)) { f(a) >= 0 } */',
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
