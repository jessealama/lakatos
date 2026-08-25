namespace Js

/-- IEEE positive infinity, the endpoint an infinite `number` bound compares
against (core has `Float.isInf` but no constant). -/
def floatInf : Float := 1.0 / 0.0

/-- Bounded ∀ over the half-open interval `[lo, hi)` of `Int` — the shape
Lemma binder guards elaborate to. Carries its own `Decidable` instance so
`decide` works on bounded properties. -/
def ballIco (lo hi : Int) (p : Int → Prop) : Prop :=
  ∀ x : Int, lo ≤ x → x < hi → p x

instance ballIco.instDecidable (lo hi : Int) (p : Int → Prop) [DecidablePred p] :
    Decidable (ballIco lo hi p) :=
  decidable_of_iff (∀ n ∈ List.range (hi - lo).toNat, p (lo + n)) (by
    constructor
    · intro h x hlo hhi
      have hn : (x - lo).toNat < (hi - lo).toNat := by omega
      have hp := h (x - lo).toNat (List.mem_range.mpr hn)
      have hx : lo + (((x - lo).toNat : Nat) : Int) = x := by omega
      rwa [hx] at hp
    · intro h n hn
      have hn' := List.mem_range.mp hn
      apply h <;> omega)

end Js
