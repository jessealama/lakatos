import Lean
import ThalesDsl.Prove

/-! `#thales_prove` with a plain-`Prop` payload: the form the plain-Lean
emission pipeline writes (#144). The obligation is an ordinary term a
person can read and edit in the artifact; the elaboration recovers binder
structure from `ballIco` applications so the same four-rung ladder runs
unchanged. The old constructor grammar keeps winning wherever it parses. -/

namespace ThalesDsl

open Lean Elab Command
open Js

syntax "#thales_prove " str ppSpace str ppSpace str " := " term : command

/-- An integer literal term, possibly negated. -/
def intLitTerm? : TSyntax `term → Option Int
  | `($n:num) => some (Int.ofNat n.getNat)
  | `(-$n:num) => some (-(Int.ofNat n.getNat))
  | _ => none

/-- The `ballIco` spine of a plain-Prop payload: literal-bounded binders,
outermost first, and the leaf under them — the same data the old grammar
carried structurally, recovered here for rung selection and witness
search. A payload with any other head is its own leaf. -/
partial def ballIcoSpine (t : TSyntax `term) :
    List (String × Int × Int) × TSyntax `term :=
  match t with
  | `(($inner)) => ballIcoSpine inner
  | `(ballIco $lo $hi fun $x:ident => $body)
  | `(ballIco $lo $hi (fun $x:ident => $body)) =>
    match intLitTerm? lo, intLitTerm? hi with
    | some l, some h =>
      let (rest, leaf) := ballIcoSpine body
      ((x.getId.toString, l, h) :: rest, leaf)
    | _, _ => ([], t)
  | _ => ([], t)

def intTerm (i : Int) : CommandElabM (TSyntax `term) := do
  let n := Syntax.mkNumLit (toString i.natAbs)
  if i < 0 then `((-$n : Int)) else `(($n : Int))

/-- The witness-search term for a spine: one `findCexIco` per binder, a
decidable test on the leaf — the shape `extractWitness` reduces. Only the
falsity path ever elaborates it, so a leaf with no `Decidable` instance
costs nothing here. -/
def buildSearchTerm (spine : List (String × Int × Int))
    (leaf : TSyntax `term) : CommandElabM (TSyntax `term) := do
  let init ← `(if $leaf then (none : Option (List Int)) else some [])
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
        let (spine, leaf) := ballIcoSpine p
        let names := spine.map (·.1)
        -- Bounded whenever every recovered binder is (an empty spine is a
        -- closed leaf, domain size 1, like the old grammar's bare islands).
        -- A leaf the decide rungs cannot handle falls through them the way
        -- any undecidable goal does.
        let allBounded := true
        let domainSize := spine.foldl
          (fun acc (_, lo, hi) => acc * (hi - lo).toNat) 1
        let searchStx ← buildSearchTerm spine leaf
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

end ThalesDsl
