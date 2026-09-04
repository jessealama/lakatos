import Lean
import ThalesDsl.Prove
import ThalesDsl.Binders

/-! `#thales_prove` with a plain-`Prop` payload: the form the plain-Lean
emission pipeline writes (#144). The obligation is an ordinary term a
person can read and edit in the artifact; the elaboration recovers binder
structure from the payload's `ballIco` and `∀` heads so the same four-rung
ladder runs unchanged. The bare form — no payload at all — reports the
stub verdict. -/

namespace ThalesDsl

open Lean Elab Command
open Js

syntax "#thales_prove " str ppSpace str ppSpace str " := " term : command

/-- An integer literal term, possibly negated. A negative endpoint reaches
the artifact parenthesized, since that is how the printer writes it in
argument position. -/
partial def intLitTerm? : TSyntax `term → Option Int
  | `($n:num) => some (Int.ofNat n.getNat)
  | `(-$n:num) => some (-(Int.ofNat n.getNat))
  | `(($inner)) => intLitTerm? inner
  | _ => none

/-- One recovered binder: a bounded int range, an unbounded head (bare
int, nat-shaped, or a Float binder), or an opaque one — a class binder,
whose domain is a constructor's image rather than a range, so it is
neither enumerable nor searchable. -/
inductive SpineBinder where
  | ranged (name : String) (lo hi : Int)
  | unbounded (name : String)
  | opaque (name : String)

def SpineBinder.name : SpineBinder → String
  | .ranged n .. | .unbounded n | .opaque n => n

/-- The renderer primes a binder spelled like the artifact's reserved
vocabulary (`pure` → `pure'`); no TS identifier contains a prime, so a
trailing one is always the renderer's, and the witness must report the
source spelling the annotation wrote. -/
def SpineBinder.sourceName (b : SpineBinder) : String :=
  if b.name.endsWith "'" then b.name.dropRight 1 else b.name

structure PropSpine where
  binders : List SpineBinder
  /-- Guard hypotheses in outer-to-inner order, each the full
  `(… : JsM Bool) = pure true` proposition, kept as syntax for search
  threading. -/
  guards : List (TSyntax `term)
  leaf : TSyntax `term
  deriving Inhabited

/-- Whether a term is an emitted guard hypothesis: a boolean island's
`= pure true` proposition. A nat binder's `0 ≤ n` occupies the same arrow
position and is deliberately not one — it stays in the leaf. -/
partial def isGuardProp : TSyntax `term → Bool
  | `(($inner)) => isGuardProp inner
  | `($_ = pure true) => true
  | _ => false

/-- Whether a hypothesis names `x` as some computation's successful
result — the shape a class binder's domain is written as, since the
binder ranges over the constructor's image. -/
partial def isCtorImage (x : Name) : TSyntax `term → Bool
  | `(($inner)) => isCtorImage x inner
  | `($_:term = .ok $y:ident) | `($_:term = Except.ok $y:ident) =>
    y.getId.eraseMacroScopes == x
  | _ => false

/-- The binder spine of a plain-Prop payload: the heads emission writes,
outermost first, then the guard hypotheses under them, and the leaf under
those. A plain Prop carries no structure, so the spine is recovered by
matching the shapes `Render.lean` commits to — rung selection and witness
search both read it. A payload with any other head is its own leaf; a
binder's own bound hypotheses — a nat binder's nonnegativity, a `number`
binder's endpoints — stay in the leaf, since search never runs on an
unbounded domain. -/
partial def propSpine (t : TSyntax `term) : PropSpine :=
  match t with
  | `(($inner)) => propSpine inner
  | `(ballIco $lo $hi fun $x:ident => $body)
  | `(ballIco $lo $hi (fun $x:ident => $body)) =>
    match intLitTerm? lo, intLitTerm? hi with
    | some l, some h =>
      let inner := propSpine body
      { inner with
        binders := .ranged x.getId.eraseMacroScopes.toString l h :: inner.binders }
    | _, _ => ({ binders := [], guards := [], leaf := t } : PropSpine)
  | `(∀ ($x:ident : Int), $body)
  | `(∀ ($x:ident : JsNumber), $body)
  | `(∀ ($x:ident : Float), $body) =>
    let inner := propSpine body
    { inner with binders := .unbounded x.getId.eraseMacroScopes.toString :: inner.binders }
  -- A constructor-image head: the instance and the hypothesis that names
  -- it as the constructor's output. Placed after the numeric heads, which
  -- claim their own types first.
  | `(∀ ($x:ident : $_ty:term), $body) =>
    -- The head's implication is matched one level down: alongside the
    -- concrete-typed arms above, an arrow inside this pattern leaves the
    -- syntax-match compiler unable to type its holes.
    match body with
    | `($hyp → $rest) =>
      if isCtorImage x.getId.eraseMacroScopes hyp then
        let inner := propSpine rest
        { inner with binders := .opaque x.getId.eraseMacroScopes.toString :: inner.binders }
      else ({ binders := [], guards := [], leaf := t } : PropSpine)
    | _ => ({ binders := [], guards := [], leaf := t } : PropSpine)
  | `($g → $rest) =>
    if isGuardProp g then
      let inner := propSpine rest
      -- Guards sit inside every binder; one wrapping a binder is no shape
      -- emission writes, so the implication stays the leaf instead.
      if inner.binders.isEmpty then { inner with guards := g :: inner.guards }
      else ({ binders := [], guards := [], leaf := t } : PropSpine)
    else ({ binders := [], guards := [], leaf := t } : PropSpine)
  | _ => ({ binders := [], guards := [], leaf := t } : PropSpine)

def intTerm (i : Int) : CommandElabM (TSyntax `term) := do
  let n := Syntax.mkNumLit (toString i.natAbs)
  if i < 0 then `((-$n : Int)) else `(($n : Int))

/-- The witness-search term for a spine: one `findCexIco` per binder, the
guards threaded inside them, and a decidable test on the leaf — the shape
`extractWitness` reduces. A guard that is false, or that throws, excludes
the assignment, so a reported witness always satisfies every guard. Only
the falsity path ever elaborates this, so a leaf with no `Decidable`
instance costs nothing here. -/
def buildSearchTerm (spine : List (String × Int × Int))
    (guards : List (TSyntax `term)) (leaf : TSyntax `term) :
    CommandElabM (TSyntax `term) := do
  let base ← `(if $leaf then (none : Option (List Int)) else some [])
  let init ← guards.foldrM (init := base) fun g acc =>
    `(if $g then $acc else (none : Option (List Int)))
  spine.foldrM (init := init) fun (x, lo, hi) acc => do
    let xi := mkIdent (Name.mkSimple x)
    `(findCexIco $(← intTerm lo) $(← intTerm hi) (fun ($xi : Int) => $acc))

elab_rules : command
  | `(#thales_prove $file:str $fn:str $prop:str := $p:term) => do
    let identity : Identity := ⟨file.getString, fn.getString, prop.getString⟩
    -- No model-registry pre-check: a term payload is only emitted for a
    -- declaration the frontend mapped — unmappable ones were classified
    -- Inappropriate before emission.
    let verdict : Verdict ←
      try
        let spine : PropSpine := propSpine p
        -- Witness keys carry source names; the search term below keeps the
        -- artifact's primed spellings, which the leaf references.
        let names := spine.binders.map (·.sourceName)
        -- Bounded whenever every recovered binder is (an empty spine is a
        -- closed leaf, domain size 1).
        -- A leaf the decide rungs cannot handle falls through them the way
        -- any undecidable goal does.
        let allBounded := spine.binders.all (· matches .ranged ..)
        let ranged := spine.binders.filterMap fun
          | .ranged x lo hi => some (x, lo, hi)
          | .unbounded _ | .opaque _ => none
        -- How many assignments the enumeration would visit; an empty range
        -- contributes 0, since there is nothing to evaluate.
        let domainSize := ranged.foldl
          (fun acc (_, lo, hi) => acc * (hi - lo).toNat) 1
        -- Witness search never runs on an unbounded domain.
        let searchStx ←
          if allBounded then buildSearchTerm ranged spine.guards spine.leaf
          else `((none : Option (List Int)))
        let budget := max (thales.heartbeats.get (← getOptions)) 1
        let evalCap := thales.maxEvaluatedElements.get (← getOptions)
        liftTermElabM <|
          tryCatchRuntimeEx
            (attemptLadder identity p searchStx names allBounded domainSize
              budget evalCap)
            fun ex => do
              if ex.isMaxHeartbeat || (← isKernelTimeout ex) then
                return timeoutVerdict identity budget
              return ⟨identity, .Error,
                s!"proof search failed: {← ex.toMessageData.toString}", none, none⟩
      catch ex =>
        pure ⟨identity, .Error,
          s!"property elaboration failed: {← ex.toMessageData.toString}", none, none⟩
    verdict.emit

/-- The bare form: an obligation the frontend emitted with no structured
payload. The verdict is the stub `NotTried`, so the envelope never changes
shape on degradation. -/
syntax "#thales_prove " str ppSpace str ppSpace str : command

elab_rules : command
  | `(#thales_prove $file:str $fn:str $prop:str) => do
    let identity : Identity := ⟨file.getString, fn.getString, prop.getString⟩
    Verdict.emit
      ⟨identity, .NotTried, "stub: no structured property provided", none, none⟩

end ThalesDsl
