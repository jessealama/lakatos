import Lean
import Tarski.Project

/-! What is in `tarski_eval`, and what may never be.

The set is now the thing a correspondence proof calls, so its membership
is part of the interface rather than a detail of seven test files. The
rule `Tarski/Simp.lean` states is checked here: a definition that
recurses on *syntax* is an ordinary member; a definition that recurses on
a *loop* is not in the set at all; a definition that recurses on the
*heap* is in it only as a guarded simproc, never as a plain unfolding.

The second list is the one that matters. A loop arm in a simp set is not
a slow proof, it is a proof that never comes back, and the failure is
silent until some unrelated obligation stalls. Naming the four heap
recursions here as well pins that they went in *behind their guards*: a
plain `attribute [tarski_eval] construct` would flip the second `#eval`
and nothing else in the suite would notice until a `new` under a symbolic
argument ran forever.

`AxiomsTest` uses the same shape for the same reason — a property of the
environment, read back out of it. -/

open Lean Meta

/-- Whether a declaration is in `tarski_eval` as an unfolding, in either
of the two forms the attribute can take: a definition with no equations
goes in by name, one with equations goes in by its equation lemmas. -/
private def unfoldsIn (n : Name) : CoreM Bool := do
  let some ext ← getSimpExtension? `tarski_eval | return false
  let thms ← ext.getTheorems
  return thms.isDeclToUnfold n || thms.toUnfoldThms.contains n

/-- Whether a simproc is registered in `tarski_eval`. -/
private def simprocIn (n : Name) : CoreM Bool := do
  let some ext ← Simp.getSimprocExtension? `tarski_eval | return false
  return (← ext.getSimprocs).simprocNames.contains n

-- Recursion on syntax, and the projection built on top of it: ordinary
-- members, unfolded wherever they appear.
/-- info: true -/
#guard_msgs in
#eval (#[``Tarski.evalExpr, ``Tarski.evalStmt, ``Tarski.callFunction, ``Tarski.getFrom,
  ``Tarski.findProperty, ``Tarski.getProp, ``Tarski.project,
  ``Tarski.readNumber,
  -- The iteration protocol and the pattern walk. `callIteratorNative` is
  -- split out of `callNative` for `callReflectNative`'s reason and is
  -- registered all the same: seven arms are far below the equation-lemma
  -- ceiling, and a closed destructuring has to reduce without a local
  -- lemma list (`Test/Tarski/DestructuringSimpTest.lean`).
  ``Tarski.getIterator, ``Tarski.iteratorStep, ``Tarski.iteratorClose,
  ``Tarski.bindPattern, ``Tarski.bindElements, ``Tarski.bindProps,
  ``Tarski.evalArgs, ``Tarski.evalArrayElements, ``Tarski.evalForOfLoop,
  ``Tarski.callIteratorNative].allM unfoldsIn)

-- Recursion on a loop (`evalWhile`, `evalDoWhile`, `evalFor`, `evalForOf`,
-- `joinElements`, `listFromArrayLike`, `rawSegments`, `forInNext`, the
-- three bound-function steps, and the three walks that run until an
-- iterator says stop) or on the heap (the three prototype walks and
-- `construct`): never a plain unfolding. The loop arms are `rw`'s, and
-- the `*UnfoldTest` files are where that happens; the four heap
-- recursions are the guarded simprocs below.
--
-- The last two are neither: `callReflectNative` and `callStringNative`
-- are out because of the *compiler's* ceiling rather than a loop's — a
-- `match` over twenty-nine and thirty-four arms with bodies that size has
-- no equation lemmas to register, so `rw` on either diverges and putting
-- either in the set overflows `maxRecDepth` before a proof runs.
-- `callIteratorNative` is the one split-out group that *is* registered:
-- seven arms are far below that ceiling.
/-- info: false -/
#guard_msgs in
#eval (#[``Tarski.evalWhile, ``Tarski.evalDoWhile, ``Tarski.evalFor, ``Tarski.joinElements,
  ``Tarski.getFromUp, ``Tarski.findPropertyUp, ``Tarski.protoChainHas,
  ``Tarski.construct, ``Tarski.listFromArrayLike, ``Tarski.forInNext, ``Tarski.rawSegments,
  ``Tarski.callBound, ``Tarski.constructBound, ``Tarski.instanceOfBound,
  ``Tarski.callReflectNative, ``Tarski.callStringNative,
  -- The four walks that run until an *iterator* says stop are loops by
  -- the same rule, and `Test/Tarski/ForOfUnfoldTest.lean` is where
  -- `evalForOf` is unfolded a step at a time.
  ``Tarski.evalForOf, ``Tarski.iteratorToList, ``Tarski.fromEntriesInto,
  ``Tarski.groupByInto].anyM unfoldsIn)

-- The four heap recursions are in the set, as simprocs.
/-- info: true -/
#guard_msgs in
#eval (#[``Tarski.unfoldGetFromUp, ``Tarski.unfoldFindPropertyUp,
  ``Tarski.unfoldProtoChainHas, ``Tarski.unfoldConstruct].allM simprocIn)
