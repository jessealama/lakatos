import ThalesDsl.Prove

open ThalesDsl Lean

-- What a `number` bound's op string DENOTES.
--
-- The root suite's binder-containment check samples the domain lemma hands
-- the refuter and asserts the prover's guard admits every value, evaluating
-- that guard with JavaScript's `<` and `<=`. That is sound only because they
-- are the same IEEE-754 binary64 comparisons as Lean's on `Float` — but it
-- leaves one leg unchecked: that the op strings the transcriber emits mean
-- those relations HERE, on the side the check assumes.
--
-- These pin that leg. Each asserts the shape elabProp builds: which relation
-- the op string becomes, and which operand the bound variable is — a lower
-- bound reads `endpoint ≤ a`, an upper bound `a ≤ endpoint`. Swap either and
-- the containment check would be validating a guard the prover never uses.

ts_def "idf" := ts.fn(ts.param["a"](ts.number)) : ts.number {
  ts.return(ts.id["a"])
}

/-- The bound variable, as elabProp names it. -/
private def isVar (s : TSyntax `term) : Bool :=
  s.raw.isIdent && s.raw.getId == `a

-- A lower bound puts the endpoint on the left: `endpoint <relation> a`.
/-- info: true -/
#guard_msgs in
#eval show Elab.Command.CommandElabM Bool from do
  let p ← `(ts_prop| ts.forall(ts.binder["a"](ts.number,
      ts.lower["<="](ts.fnum[0]))) {
    ts.eq(ts.call["idf"](ts.id["a"]), ts.id["a"])
  })
  match (← elabProp [] p).prop with
  | `(∀ ($_ : Float), $lhs ≤ $rhs → $_) => return isVar rhs && !isVar lhs
  | _ => return false

/-- info: true -/
#guard_msgs in
#eval show Elab.Command.CommandElabM Bool from do
  let p ← `(ts_prop| ts.forall(ts.binder["a"](ts.number,
      ts.lower["<"](ts.fnum[0]))) {
    ts.eq(ts.call["idf"](ts.id["a"]), ts.id["a"])
  })
  match (← elabProp [] p).prop with
  | `(∀ ($_ : Float), $lhs < $rhs → $_) => return isVar rhs && !isVar lhs
  | _ => return false

-- An upper bound puts the endpoint on the right: `a <relation> endpoint`.
/-- info: true -/
#guard_msgs in
#eval show Elab.Command.CommandElabM Bool from do
  let p ← `(ts_prop| ts.forall(ts.binder["a"](ts.number,
      ts.upper["<="](ts.fnum[1]))) {
    ts.eq(ts.call["idf"](ts.id["a"]), ts.id["a"])
  })
  match (← elabProp [] p).prop with
  | `(∀ ($_ : Float), $lhs ≤ $rhs → $_) => return isVar lhs && !isVar rhs
  | _ => return false

/-- info: true -/
#guard_msgs in
#eval show Elab.Command.CommandElabM Bool from do
  let p ← `(ts_prop| ts.forall(ts.binder["a"](ts.number,
      ts.upper["<"](ts.fnum[1]))) {
    ts.eq(ts.call["idf"](ts.id["a"]), ts.id["a"])
  })
  match (← elabProp [] p).prop with
  | `(∀ ($_ : Float), $lhs < $rhs → $_) => return isVar lhs && !isVar rhs
  | _ => return false

-- Both bounds: the lower hypothesis comes first, and neither side's
-- relation is disturbed by the other's presence.
/-- info: true -/
#guard_msgs in
#eval show Elab.Command.CommandElabM Bool from do
  let p ← `(ts_prop| ts.forall(ts.binder["a"](ts.number,
      ts.lower["<="](ts.fnum[0]), ts.upper["<"](ts.fnum[1]))) {
    ts.eq(ts.call["idf"](ts.id["a"]), ts.id["a"])
  })
  match (← elabProp [] p).prop with
  | `(∀ ($_ : Float), $lo ≤ $loVar → $hiVar < $hi → $_) =>
      return isVar loVar && !isVar lo && isVar hiVar && !isVar hi
  | _ => return false

-- An infinite endpoint's hypothesis compares against the literal infinity:
-- `ts.fnum[Infinity]` is `floatInf` itself, `ts.fnum[-Infinity]` its
-- negation, never a substituted finite stand-in.
private def isFloatInf (s : TSyntax `term) : Bool :=
  s.raw.isIdent && s.raw.getId.eraseMacroScopes == `floatInf

private def isNegFloatInf (s : TSyntax `term) : Bool :=
  match s with
  | `((-$x)) => isFloatInf x
  | _ => false

/-- info: true -/
#guard_msgs in
#eval show Elab.Command.CommandElabM Bool from do
  let p ← `(ts_prop| ts.forall(ts.binder["a"](ts.number,
      ts.upper["<"](ts.fnum[Infinity]))) {
    ts.eq(ts.call["idf"](ts.id["a"]), ts.id["a"])
  })
  match (← elabProp [] p).prop with
  | `(∀ ($_ : Float), $v < $hi → $_) => return isVar v && isFloatInf hi
  | _ => return false

/-- info: true -/
#guard_msgs in
#eval show Elab.Command.CommandElabM Bool from do
  let p ← `(ts_prop| ts.forall(ts.binder["a"](ts.number,
      ts.lower["<"](ts.fnum[-Infinity]))) {
    ts.eq(ts.call["idf"](ts.id["a"]), ts.id["a"])
  })
  match (← elabProp [] p).prop with
  | `(∀ ($_ : Float), $lo < $v → $_) => return isVar v && isNegFloatInf lo
  | _ => return false

-- A binder with no interval at all carries no hypothesis: the whole of
-- binary64, NaN included. Every interval guards both of its sides, so this
-- is the only unguarded shape.
/-- info: true -/
#guard_msgs in
#eval show Elab.Command.CommandElabM Bool from do
  let p ← `(ts_prop| ts.forall(ts.binder["a"](ts.number)) {
    ts.eq(ts.call["idf"](ts.id["a"]), ts.id["a"])
  })
  match (← elabProp [] p).prop with
  | `(∀ ($_ : Float), $_ → $_) => return false
  | `(∀ ($_ : Float), $_) => return true
  | _ => return false
