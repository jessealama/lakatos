# CLAUDE.md

## What this package is

Tarski is lakatos's JS-semantics library: the Lean definitions that give TypeScript's values and operations their meaning. `lakatos prove` (thales) proves `@ensures` properties against models built from these definitions. The package is shared: thales requires it by path (`require tarski from "../../tarski"` in `engines/thales/lakefile.lean`); no engine may be required by it. The boundary rule: nothing here mentions `ThalesDsl` or any emission concern — lakatos owns syntax and search, this library owns meaning.

The Lean toolchain pin is `lean-toolchain` here; `engines/thales/lean-toolchain` is a symlink to it. `lake-manifest.json` is tracked.

## Common commands

From `tarski/`:

```bash
lake build                          # the Js library
lake build TarskiTest               # the Lean tests under Test/Js/
lake env lean Test/Js/NormTest.lean # one test file in isolation
```

Wrap `lake env lean` in a timeout when running it by hand; a bad artifact can grind indefinitely.

## Modules

| Module                                                                | Role                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         |
| --------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `Js.lean`                                                             | The umbrella import: every module below, in dependency order. Artifacts and tests `import Js`.                                                                                                                                                                                                                                                                                                                                                                                                                               |
| `Js/Runtime.lean`, `Js/Number/Basic.lean`                             | The domain: `JsM α := Except JsError α`, `JsNumber := Float`, `floatNaN`. **Computability is the invariant** — `decide` must evaluate models over bounded domains.                                                                                                                                                                                                                                                                                                                                                           |
| `Js/Val.lean`                                                         | The tagged `JsVal` domain for unions, optionals, and booleans: `toNumber`/`toBoolean` (throwing projections), `typeof`, `strictEq`, `sameValue`.                                                                                                                                                                                                                                                                                                                                                                             |
| `Js/Binders.lean`                                                     | Binder-domain meaning: `floatInf` and `ballIco` (bounded ∀ over `[lo, hi)`) with its `Decidable` instance. The witness scans live in the prover, not here.                                                                                                                                                                                                                                                                                                                                                                   |
| `Js/Norm.lean` (+ `Js/NormAttr.lean`)                                 | The `js_norm` simp set: what lets pure-looking code shed its monadic wrapping so the closers see bare arithmetic; dual-tagged for grind. A lowered branch is split into one obligation per arm carrying its condition — the only shape in which a literal arm becomes a ground term. Vanilla Lean has no binary64 theory, so each recurring residual goal is one lemma to add here. `NormAttr` registers the attribute one module below the lemmas, since a simp set is only usable in modules that import its registration. |
| `Js/Number/FloatOps.lean`, `Constants.lean`                           | Binary64 operations JS has and Lean does not (`tsRem`, the roundings, `tsSign`, `tsFround`, `tsMin`/`tsMax`, the integer predicates, `sameValue`) and the `Math`/`Number` constants under their source spellings. Built from `Float.Model`, never `extern`, so the kernel can reduce them; `MAX_VALUE`/`MIN_VALUE` are spelled by bits because their decimals do not reduce.                                                                                                                                                 |
| `Js/Number/FloatFacts.lean`, `FloatOpsFacts.lean`, `FroundFacts.lean` | Kernel-checked theory about binary64 and the models above (monotonicity against a bounded constant, order transitivity and totality away from NaN, the roundings' and clamps' defining inequalities). Residual goals are over `Float`, whose every op is `pack (op (unpack ..))`, so an `UnpackedFloat` fact reaches one only through the `Canonical` round-trip. `FroundFacts` is the order theory of `Math.fround`: each stage of the narrowing is monotone on values, so the composite is.                                |

## Tests

`Test/Js/` — Lean unit tests, one file per concern; `lake build TarskiTest` builds them all and each runs alone via `lake env lean`. Test files import only `Js` and its submodules.
