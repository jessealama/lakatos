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
