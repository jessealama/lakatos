import { describe, expect, test } from 'vitest';
import * as fs from 'node:fs';
import { schemaValidator } from '../../../../tests/helpers/schema-validator.js';
import { emitModule } from '../src/emission.js';

const FIXTURE = 'engines/thales/tests/fixtures/tracer.ts';
const read = () => fs.readFileSync(FIXTURE, 'utf8');

const expectValidEmission = schemaValidator(
  new URL('../../../../schemas/thales-emission.schema.json', import.meta.url),
  'emission',
);

describe('emitModule on the tracer fixture', () => {
  test('maps add with its body IR', () => {
    const { emission } = emitModule(read(), FIXTURE);
    expect(emission.file).toBe(FIXTURE);
    expect(emission.declarations).toEqual([
      {
        kind: 'function',
        name: 'add',
        params: ['a', 'b'],
        source: expect.stringContaining('export function add'),
        body: [
          {
            kind: 'return',
            expr: {
              kind: 'binop',
              op: '+',
              left: { kind: 'id', name: 'a' },
              right: { kind: 'id', name: 'b' },
            },
          },
        ],
      },
    ]);
  });

  test('structures the commutes obligation', () => {
    const { emission } = emitModule(read(), FIXTURE);
    expect(emission.obligations).toEqual([
      {
        function: 'add',
        property: 'commutes',
        formula:
          'forall (a: int ∈ [0, 10)) (b: int ∈ [0, 10)) { add(a, b) ≡ add(b, a) }',
        payload: {
          kind: 'structured',
          binders: [
            { name: 'a', lo: '0', hi: '10' },
            { name: 'b', lo: '0', hi: '10' },
          ],
          conclusion: {
            kind: 'eq',
            left: {
              kind: 'call',
              callee: 'add',
              args: [
                { kind: 'id', name: 'a' },
                { kind: 'id', name: 'b' },
              ],
            },
            right: {
              kind: 'call',
              callee: 'add',
              args: [
                { kind: 'id', name: 'b' },
                { kind: 'id', name: 'a' },
              ],
            },
          },
        },
      },
    ]);
  });

  test('classifies the two degraded annotations with old-pipeline reasons', () => {
    const { classified } = emitModule(read(), FIXTURE);
    expect(
      classified.map((c) => [c.annotation.propertyName, c.szs, c.reason]),
    ).toEqual([
      [
        'nonNegative',
        'Inappropriate',
        "'fetchTotal' could not be modeled: unmapped TypeScript construct 'AwaitExpression' at 8:10",
      ],
      [
        'bumps',
        'Inappropriate',
        "'Counter#bump' could not be modeled: unmapped TypeScript construct 'ClassDeclaration' at 13:3",
      ],
    ]);
  });

  test('the emission validates against the schema', () => {
    expectValidEmission(emitModule(read(), FIXTURE).emission);
  });

  test('the pinned tracer emission fixture is exactly what the frontend emits', () => {
    const pinned = JSON.parse(
      fs.readFileSync(
        'engines/thales/tests/fixtures/tracer.emission.json',
        'utf8',
      ),
    );
    expect(emitModule(read(), FIXTURE).emission).toEqual(pinned);
  });

  test('extraction results ride along', () => {
    const { annotations, invalid } = emitModule(read(), FIXTURE);
    expect(annotations.map((a) => a.propertyName)).toEqual([
      'commutes',
      'nonNegative',
      'bumps',
    ]);
    expect(invalid).toEqual([]);
  });
});

/** The classification for one annotated declaration. */
function classifiedOf(decl: string, fn = 'f'): string | undefined {
  const src = `/** @ensures{p} forall (x: int ∈ [0, 5)) { ${fn}(x) ≡ x } */\n${decl}\n`;
  return emitModule(src, 't.ts').classified[0]?.reason;
}

/** The payload of one obligation on a mappable identity function. */
function payloadOf(formula: string) {
  const src = `/** @ensures{p} ${formula} */\nexport function f(x: number): number {\n  return x;\n}\n`;
  const { emission, classified } = emitModule(src, 't.ts');
  expect(classified).toEqual([]);
  return emission.obligations[0]!.payload;
}

describe('signature and body blockers', () => {
  test.each([
    [
      'an async function',
      'async function f(x: number): number { return x; }',
      undefined,
    ],
    ['a generator', 'function* f(x: number): number { return x; }', undefined],
    [
      'a destructured parameter',
      'function f({ x }: { x: number }): number { return 1; }',
      'ObjectBindingPattern',
    ],
    [
      'a rest parameter',
      'function f(...x: number[]): number { return 1; }',
      'DotDotDotToken',
    ],
    [
      'an optional parameter',
      'function f(x?: number): number { return 1; }',
      undefined,
    ],
    ['an untyped parameter', 'function f(x): number { return 1; }', undefined],
    [
      'a non-number parameter type',
      'function f(x: string): number { return 1; }',
      'StringKeyword',
    ],
    [
      'a bodiless overload signature',
      'function f(x: number): number;',
      undefined,
    ],
    [
      'a non-number return type',
      'function f(x: number): string { return "x"; }',
      'StringKeyword',
    ],
    [
      'a declaration statement in the body',
      'function f(x: number): number { const y = 1; return y; }',
      'VariableStatement',
    ],
    [
      'a bare return',
      'function f(x: number): number { return; }',
      'ReturnStatement',
    ],
    [
      'an unemittable operator',
      'function f(x: number): number { return x ** 2; }',
      'BinaryExpression',
    ],
    [
      'a blocker in the left operand',
      'function f(x: number): number { return (await g()) + x; }',
      'AwaitExpression',
    ],
    [
      'a blocker in the right operand',
      'function f(x: number): number { return x + (await g()); }',
      'AwaitExpression',
    ],
    [
      'a blocker in a call argument',
      'function f(x: number): number { return f(await g()); }',
      'AwaitExpression',
    ],
  ])('%s classifies its annotation', (_label, decl, construct) => {
    const reason = classifiedOf(decl);
    expect(reason).toMatch(
      /'f' could not be modeled: unmapped TypeScript construct/,
    );
    if (construct !== undefined) expect(reason).toContain(`'${construct}'`);
  });

  test('a static class member classifies under its dotted name', () => {
    const src = [
      'export class Box {',
      '  /** @ensures{p} forall (x: int ∈ [0, 5)) { make(x) ≡ x } */',
      '  static make(x: number): number {',
      '    return x;',
      '  }',
      '}',
      '',
    ].join('\n');
    const { classified } = emitModule(src, 't.ts');
    expect(classified[0]!.reason).toMatch(
      /'Box\.make' could not be modeled: unmapped TypeScript construct 'ClassDeclaration'/,
    );
  });

  test('nameless and computed-name declarations bind no blocker', () => {
    const src = [
      'export default function (x: number): number { return x; }',
      'export default class {}',
      'class C { ["m"](x: number): number { return x; } }',
      'interface I { x: number; }',
      '',
    ].join('\n');
    const { emission, classified } = emitModule(src, 't.ts');
    expect(emission.declarations).toEqual([]);
    expect(classified).toEqual([]);
  });
});

describe('obligation payload degradations', () => {
  test.each([
    ['an unbounded int binder', 'forall (x: int) { f(x) ≡ x }'],
    ['a half-bounded range', 'forall (x: int ∈ (-∞, 10]) { f(x) ≡ x }'],
    [
      'a range past the safe integers',
      'forall (x: int ∈ [0, 99999999999999999999)) { f(x) ≡ x }',
    ],
    [
      'an implication body',
      'forall (x: int ∈ [0, 5)) { f(x) >= 0 -> f(x) ≡ x }',
    ],
    ['an unparseable atom', 'forall (x: int ∈ [0, 5)) { 2x ≡ x }'],
    [
      'an atom that is not valid JavaScript',
      'forall (x: int ∈ [0, 5)) { f(x) is wonderful }',
    ],
    [
      'a half-bounded floor above zero',
      'forall (x: int ∈ [3, ∞)) { f(x) ≡ x }',
    ],
    [
      'a blocker in the left equation side',
      'forall (x: int ∈ [0, 5)) { (await f(x)) ≡ x }',
    ],
    [
      'a blocker in the right equation side',
      'forall (x: int ∈ [0, 5)) { x ≡ (await f(x)) }',
    ],
    ['a method-call conclusion', 'forall (x: int ∈ [0, 5)) { foo.bar(x, x) }'],
    [
      'a formula the prefix parser rejects',
      'forall (x: int ∈ [0, 5)) (x: int ∈ [0, 5)) { f(x) ≡ x }',
    ],
  ])('%s degrades to a bare payload', (_label, formula) => {
    expect(payloadOf(formula)).toEqual({ kind: 'bare' });
  });

  test('parenthesized arguments and negative literals structure', () => {
    expect(payloadOf('forall (x: int ∈ [0, 5)) { f((x)) ≡ f(-1) }')).toEqual({
      kind: 'structured',
      binders: [{ name: 'x', lo: '0', hi: '5' }],
      conclusion: {
        kind: 'eq',
        left: { kind: 'call', callee: 'f', args: [{ kind: 'id', name: 'x' }] },
        right: {
          kind: 'call',
          callee: 'f',
          args: [{ kind: 'num', lit: '-1' }],
        },
      },
    });
  });
});

describe('emitModule degradations beyond the tracer', () => {
  test('a formula outside the structured slice degrades to a bare payload', () => {
    const src = [
      '/** @ensures{big} forall (x: number ∈ [0, 1]) { f(x) >= 0 } */',
      'export function f(x: number): number {',
      '  return x;',
      '}',
      '',
    ].join('\n');
    const { emission, classified } = emitModule(src, 'f.ts');
    expect(classified).toEqual([]);
    expect(emission.obligations).toEqual([
      {
        function: 'f',
        property: 'big',
        formula: 'forall (x: number ∈ [0, 1]) { f(x) >= 0 }',
        payload: { kind: 'bare' },
      },
    ]);
  });

  test('an istrue conclusion structures as istrue', () => {
    const src = [
      '/** @ensures{nonneg} forall (x: int ∈ [0, 5)) { f(x) >= 0 } */',
      'export function f(x: number): number {',
      '  return x;',
      '}',
      '',
    ].join('\n');
    const { emission } = emitModule(src, 'f.ts');
    expect(emission.obligations[0]!.payload).toEqual({
      kind: 'structured',
      binders: [{ name: 'x', lo: '0', hi: '5' }],
      conclusion: {
        kind: 'istrue',
        expr: {
          kind: 'binop',
          op: '>=',
          left: {
            kind: 'call',
            callee: 'f',
            args: [{ kind: 'id', name: 'x' }],
          },
          right: { kind: 'num', lit: '0' },
        },
      },
    });
  });
});
