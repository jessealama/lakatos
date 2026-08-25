import Init.Data.Float.Model.Float

/-!
Background theory about binary64 arithmetic, proven from `Float.Model`.

Lean's float model ships essentially no lemmas, so a residual goal about
`Float` has no theory to appeal to until one is proven here. Everything
below is kernel-checked — no axioms, no `native_decide`.

`Float` operations are `pack (op (unpack ..) (unpack ..))`, so a fact
about `UnpackedFloat` only reaches a residual goal once the round-trip is
available to cross the repacking — `unpack ∘ pack` for a result that gets
repacked, `pack ∘ unpack` for one that gets compared. Both directions are
below; `Norm.lean` consumes what they enable.

The file culminates in the four monotonicity facts at the `Float` layer —
mul, add, sub, and div against a suitably bounded constant preserve `≤` —
built in layers: round-to-nearest-even as arithmetic on values
(`rnShiftF`), the closed form of `roundWithAccuracy` under its documented
exponent contract (`WellPlaced`), an integer value semantics (`key`) that
`compare` agrees with on canonical floats, the overflow-aware `pack`
crossing, and per-operation shape and monotonicity lemmas over the
constructor grid.
-/

namespace Js.Number.FloatFacts

open Float.Model Float.Model.UnpackedFloat

/-! ## Sign algebra -/

theorem sign_apply_neg (s : Sign) (n : Int) : (-s).apply n = -(s.apply n) := by
  cases s
  · exact (Int.neg_neg n).symm
  · rfl

theorem sign_neg_neg (s : Sign) : - -s = s := by
  cases s <;> rfl

theorem sign_beq_neg_neg (s t : Sign) : (s == - -t) = (s == t) := by
  cases s <;> cases t <;> rfl

theorem sign_mul_comm (s t : Sign) : s * t = t * s := by
  cases s <;> cases t <;> rfl

theorem sign_toBitVec_ofBitVec (v : BitVec 1) : (Sign.ofBitVec v).toBitVec = v := by
  revert v; decide

/-! ## Negation and subtraction -/

theorem neg_neg (a : UnpackedFloat) : a.neg.neg = a := by
  cases a <;> grind [UnpackedFloat.neg, sign_neg_neg]

/-- IEEE subtraction is addition of the negation, so ordering facts about
`add` transfer to `sub` without a second rounding analysis. -/
theorem sub_eq_add_neg (spec : Format) (a b : UnpackedFloat) :
    UnpackedFloat.sub spec a b = UnpackedFloat.add spec a b.neg := by
  cases a <;> cases b <;>
    grind [UnpackedFloat.sub, UnpackedFloat.add, UnpackedFloat.neg,
           sign_apply_neg, sign_neg_neg, sign_beq_neg_neg]

/-! ## Commutativity

`mul` and `add` are symmetric row by row: the exceptional rows mirror
each other (NaN has a single constructor, so both NaN rows agree), and
the finite rows commute because their mantissa and exponent arithmetic
does. -/

theorem mul_comm (spec : Format) (a b : UnpackedFloat) :
    UnpackedFloat.mul spec a b = UnpackedFloat.mul spec b a := by
  cases a <;> cases b <;>
    simp [UnpackedFloat.mul, sign_mul_comm, Nat.mul_comm, Int.add_comm]

theorem add_comm (spec : Format) (a b : UnpackedFloat) :
    UnpackedFloat.add spec a b = UnpackedFloat.add spec b a := by
  cases a <;> cases b <;>
    simp [UnpackedFloat.add, Int.min_comm, Int.add_comm] <;>
    rename_i s t <;> cases s <;> cases t <;> rfl

/-! ## Round-to-nearest-even on mantissas -/

/-- Accuracies ordered by where the discarded fraction sits relative to a
half ulp: exact, below half, exactly half, above half. -/
def accuracyRank : Accuracy → Nat
  | .exact => 0
  | .inexact .lt => 1
  | .inexact .eq => 2
  | .inexact .gt => 3

/-- Rounding respects the lexicographic order on (mantissa, discarded
fraction); this is the single-step core of every monotonicity result. -/
theorem roundToNearestEven_le_of_lex {m₁ m₂ : Nat} {a₁ a₂ : Accuracy}
    (h : m₁ < m₂ ∨ (m₁ = m₂ ∧ accuracyRank a₁ ≤ accuracyRank a₂)) :
    Accuracy.roundToNearestEven m₁ a₁ ≤ Accuracy.roundToNearestEven m₂ a₂ := by
  cases a₁ <;> cases a₂ <;>
  · first
    | grind [Accuracy.roundToNearestEven, accuracyRank]
    | (rename_i o₁ o₂
       cases o₁ <;> cases o₂ <;> grind [Accuracy.roundToNearestEven, accuracyRank])
    | (rename_i o
       cases o <;> grind [Accuracy.roundToNearestEven, accuracyRank])

/-! ## The shift pipeline as division

`roundWithAccuracy` iterates `shiftRightOne`, accumulating the discarded
bits into a round bit and a sticky bit. The closed form below replaces
that iteration with `/` and `%`, which is what the arithmetic lemmas
downstream actually consume. -/

/-- What `n` right-shifts of an exact mantissa `m` produce: the quotient,
the last bit shifted out, and whether anything below it was nonzero. -/
def shiftedForm (m n : Nat) : ExtendedMantissa :=
  if n = 0 then ⟨m, false, false⟩
  else ⟨m / 2 ^ n, m / 2 ^ (n - 1) % 2 == 1, m % 2 ^ (n - 1) != 0⟩

theorem repeat_shiftRightOne_eq (m n : Nat) :
    Nat.repeat ExtendedMantissa.shiftRightOne n ⟨m, false, false⟩ = shiftedForm m n := by
  induction n with
  | zero => simp [shiftedForm, Nat.repeat]
  | succ k ih =>
    rw [Nat.repeat, ih]
    cases k with
    | zero =>
      simp [shiftedForm, ExtendedMantissa.shiftRightOne]
      grind
    | succ j =>
      simp only [shiftedForm, ExtendedMantissa.shiftRightOne, if_neg (by omega : ¬j + 1 = 0),
        if_neg (by omega : ¬j + 1 + 1 = 0)]
      refine ExtendedMantissa.mk.injEq .. ▸ ⟨?_, ?_, ?_⟩
      · show m / 2 ^ (j + 1) / 2 = m / 2 ^ (j + 1 + 1)
        rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ]
      · show (m / 2 ^ (j + 1) % 2 != 0) = (m / 2 ^ (j + 1 + 1 - 1) % 2 == 1)
        grind
      · show ((m / 2 ^ j % 2 == 1) || (m % 2 ^ j != 0)) = (m % 2 ^ (j + 1 + 1 - 1) != 0)
        have h : m % 2 ^ (j + 1) = 2 ^ j * (m / 2 ^ j % 2) + m % 2 ^ j := by
          rw [Nat.pow_succ, Nat.mod_mul]
          omega
        grind

/-- Round-to-nearest-even of `m / 2^n`, as pure arithmetic. -/
def rnShift (m n : Nat) : Nat :=
  let q := m / 2 ^ n
  let r := m % 2 ^ n
  if r * 2 < 2 ^ n then q
  else if r * 2 = 2 ^ n then q + q % 2
  else q + 1

/-- The shift pipeline's rounded mantissa is exactly `rnShift`. -/
theorem roundedMantissa_shiftedForm (m n : Nat) :
    (shiftedForm m n).roundedMantissa = rnShift m n := by
  cases n with
  | zero =>
    simp [shiftedForm, rnShift, ExtendedMantissa.roundedMantissa, ExtendedMantissa.accuracy,
      Accuracy.roundToNearestEven]
    grind
  | succ k =>
    have h : m % 2 ^ (k + 1) = 2 ^ k * (m / 2 ^ k % 2) + m % 2 ^ k := by
      rw [Nat.pow_succ, Nat.mod_mul]; omega
    have hk : 0 < 2 ^ k := Nat.two_pow_pos k
    have hmk : m % 2 ^ k < 2 ^ k := Nat.mod_lt _ hk
    simp only [shiftedForm, if_neg (by omega : ¬k + 1 = 0), Nat.add_sub_cancel]
    rw [ExtendedMantissa.roundedMantissa]
    have h2' : m / 2 ^ k % 2 = 0 ∨ m / 2 ^ k % 2 = 1 := by omega
    rcases h2' with h2 | h2 <;>
      rcases Nat.eq_zero_or_pos (m % 2 ^ k) with h3 | h3 <;>
        simp [ExtendedMantissa.accuracy, h2, h3, Accuracy.roundToNearestEven,
          rnShift, Nat.pow_succ] <;> grind

theorem rnShift_mono {m m' : Nat} (n : Nat) (h : m ≤ m') : rnShift m n ≤ rnShift m' n := by
  have hq : m / 2 ^ n ≤ m' / 2 ^ n := Nat.div_le_div_right h
  have hd : 0 < 2 ^ n := Nat.two_pow_pos n
  have e1 := Nat.div_add_mod m (2 ^ n)
  have e2 := Nat.div_add_mod m' (2 ^ n)
  have r1 : m % 2 ^ n < 2 ^ n := Nat.mod_lt _ hd
  have r2 : m' % 2 ^ n < 2 ^ n := Nat.mod_lt _ hd
  rw [rnShift, rnShift]
  by_cases hqq : m / 2 ^ n = m' / 2 ^ n
  · have hr : m % 2 ^ n ≤ m' % 2 ^ n := by
      have := hqq ▸ e1; omega
    grind
  · have : m / 2 ^ n + 1 ≤ m' / 2 ^ n := by omega
    grind

/-- `rnShift` rounds the quotient to itself or its successor. -/
theorem rnShift_bounds (m n : Nat) :
    m / 2 ^ n ≤ rnShift m n ∧ rnShift m n ≤ m / 2 ^ n + 1 := by
  rw [rnShift]; grind

/-! ## Value-monotonicity of rounding

`rnPos p F m` is the value (relative to the input exponent) of `m`
rounded to `p` significant bits, but never at a granularity finer than
shift `F`; `p = 53` and `F` derived from the minimum exponent gives
binary64 rounding with subnormals. Monotonicity must cover arguments
that round at different shifts — the cross-binade case. -/

def rnPos (p F m : Nat) : Nat :=
  let n := max (m.log2 + 1 - p) F
  rnShift m n * 2 ^ n

theorem rnPos_mono_aux (p F m m' n n' : Nat) (hp : 1 ≤ p) (hm : 0 < m) (h : m ≤ m')
    (hn : n = max (m.log2 + 1 - p) F) (hn' : n' = max (m'.log2 + 1 - p) F) :
    rnShift m n * 2 ^ n ≤ rnShift m' n' * 2 ^ n' := by
  have hm' : 0 < m' := Nat.lt_of_lt_of_le hm h
  have hlog : m.log2 ≤ m'.log2 :=
    (Nat.le_log2 (by omega)).mpr (Nat.le_trans (Nat.log2_self_le (by omega)) h)
  have hnn' : n ≤ n' := by omega
  rcases Nat.eq_or_lt_of_le hnn' with heq | hlt
  · -- same shift: mantissa monotonicity
    rw [← heq]
    exact Nat.mul_le_mul_right _ (rnShift_mono n h)
  · -- n < n' forces n' into the log2 branch, so m' sits in a strictly
    -- higher binade; chain through the binade boundary 2^(m'.log2)
    have hn'val : n' = m'.log2 + 1 - p := by omega
    have hlog2' : p ≤ m'.log2 + 1 := by omega
    have hn'le : n' ≤ m'.log2 := by omega
    have hmlt : m < 2 ^ (n + p) := by
      have h1 : m < 2 ^ (m.log2 + 1) := Nat.lt_log2_self
      have h2 : m.log2 + 1 ≤ n + p := by omega
      exact Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by omega) h2)
    have hdiv : m / 2 ^ n < 2 ^ p := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos n)]
      calc m < 2 ^ (n + p) := hmlt
        _ = 2 ^ p * 2 ^ n := by rw [← Nat.pow_add, Nat.add_comm]
    have hub : rnShift m n * 2 ^ n ≤ 2 ^ (p + n) := by
      have h1 : rnShift m n ≤ m / 2 ^ n + 1 := (rnShift_bounds m n).2
      have h2 : rnShift m n ≤ 2 ^ p := by omega
      calc rnShift m n * 2 ^ n ≤ 2 ^ p * 2 ^ n := Nat.mul_le_mul_right _ h2
        _ = 2 ^ (p + n) := by rw [Nat.pow_add]
    have hlb : 2 ^ m'.log2 ≤ rnShift m' n' * 2 ^ n' := by
      have h1 : 2 ^ m'.log2 ≤ m' := Nat.log2_self_le (by omega)
      have h2 : 2 ^ (m'.log2 - n') ≤ m' / 2 ^ n' := by
        rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos n')]
        calc 2 ^ (m'.log2 - n') * 2 ^ n' = 2 ^ m'.log2 := by
              rw [← Nat.pow_add]; congr 1; omega
          _ ≤ m' := h1
      have h3 : 2 ^ (m'.log2 - n') ≤ rnShift m' n' :=
        Nat.le_trans h2 (rnShift_bounds m' n').1
      calc 2 ^ m'.log2 = 2 ^ (m'.log2 - n') * 2 ^ n' := by
            rw [← Nat.pow_add]; congr 1; omega
        _ ≤ rnShift m' n' * 2 ^ n' := Nat.mul_le_mul_right _ h3
    have hmid : p + n ≤ m'.log2 := by omega
    exact Nat.le_trans hub (Nat.le_trans (Nat.pow_le_pow_right (by omega) hmid) hlb)

theorem rnPos_mono (p F : Nat) (hp : 1 ≤ p) {m m' : Nat} (h : m ≤ m') :
    rnPos p F m ≤ rnPos p F m' := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have h0 : ∀ n, rnShift 0 n = 0 := by
      intro n; rw [rnShift]; simp [Nat.two_pow_pos]
    simp [rnPos, h0]
  · exact rnPos_mono_aux p F m m' _ _ hp hm h rfl rfl

/-! ## Packing round-trips

`Float.Model` operations unpack, compute, and repack; relating two
operation results therefore always crosses `pack` followed by `unpack`.
Core ships extraction lemmas for the mantissa and exponent fields but
not the sign, so that one is here too. -/

theorem unpackSign_packComponents64 {sign : Sign} {ev : BitVec 11} {mv : BitVec 52} :
    Sign.ofBitVec (unpackSign (packComponents .binary64 sign ev mv)) = sign := by
  simp only [unpackSign, packComponents, BitVec.extractLsb]
  rw [BitVec.extractLsb'_append_eq_of_le (by omega),
    BitVec.extractLsb'_append_eq_of_le (by omega)]
  cases sign <;> rfl

/-- A normal binary64 float survives the pack/unpack round-trip. The
bounds are the canonical-form invariants for normal numbers. -/
theorem unpack_pack_of_normal64 (s : Sign) (m : Nat) (e : Int) (hm : 0 < m)
    (hlo : 2 ^ 52 ≤ m) (hhi : m < 2 ^ 53)
    (helo : -1074 ≤ e) (hehi : e ≤ 971) :
    UnpackedFloat.unpack .binary64 (UnpackedFloat.pack .binary64 (.finite s m e hm)) =
      .finite s m e hm := by
  have hlog : m.log2 = 52 := by
    have h1 : 52 ≤ m.log2 := (Nat.le_log2 (by omega)).mpr hlo
    have h2 : ¬53 ≤ m.log2 := fun hc => by
      have := (Nat.le_log2 (by omega)).mp hc; omega
    omega
  have hbias : (e + Format.binary64.exponentBias + Format.binary64.mantissaBitsWithoutImplicit).toNat
      = (e + 1075).toNat := by
    show (e + (2 ^ (11 - 1) - 1 : Nat) + (52 : Nat)).toNat = (e + 1075).toNat
    omega
  rw [UnpackedFloat.pack]
  simp only [hlog, hbias]
  rw [if_neg (by omega), if_pos (by simp [Format.mantissaBits])]
  rw [UnpackedFloat.unpack]
  simp only [unpackMantissa_packComponents, unpackExponent_packComponents,
    unpackSign_packComponents64]
  have hne1 : BitVec.ofNat 11 (e + 1075).toNat ≠ -1#11 := by
    intro heq
    have := congrArg BitVec.toNat heq
    simp [BitVec.toNat_ofNat] at this
    omega
  have hne0 : BitVec.ofNat 11 (e + 1075).toNat ≠ 0#11 := by
    intro heq
    have := congrArg BitVec.toNat heq
    simp [BitVec.toNat_ofNat] at this
    omega
  rw [if_neg hne1, if_neg hne0]
  have hmant : (1#1 ++ BitVec.ofNat 52 m).toNat = m := by
    rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (BitVec.ofNat 52 m).isLt,
      BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    simp [BitVec.toNat_ofNat]
    omega
  have hb1023 : ((Format.binary64.exponentBias : Nat) : Int) = 1023 := rfl
  simp [hmant, BitVec.toNat_ofNat, hb1023]
  omega

-- Kernel-computed round-trip pins for the shapes the general lemmas do
-- not yet cover: subnormal, overflow to infinity, zero, infinity.
example :
    UnpackedFloat.unpack .binary64 (UnpackedFloat.pack .binary64
      (.finite .positive 1 (-1074) (by omega))) = .finite .positive 1 (-1074) (by omega) := rfl
example :
    UnpackedFloat.unpack .binary64 (UnpackedFloat.pack .binary64
      (.finite .positive (2 ^ 52) 1000 (by omega))) = .infinity .positive := rfl
example :
    UnpackedFloat.unpack .binary64 (UnpackedFloat.pack .binary64 (.zero .negative)) =
      .zero .negative := rfl
example :
    UnpackedFloat.unpack .binary64 (UnpackedFloat.pack .binary64 (.infinity .negative)) =
      .infinity .negative := rfl

/-! ## Canonical forms and the pack/unpack round-trip

Every `Float.Model` operation unpacks its arguments, computes, and
repacks, so relating two of them means crossing `pack` then `unpack`.
That crossing is the identity exactly on the values `unpack` can produce
— `Format.Valid` already rules out the one hazard, non-canonical `NaN`
payloads — and `Canonical` names them. -/

/-- The values `unpack` produces: the three specials, plus finite
mantissa/exponent pairs in subnormal or normal position. -/
inductive Canonical : UnpackedFloat → Prop
  | notANumber : Canonical .notANumber
  | infinity (s : Sign) : Canonical (.infinity s)
  | zero (s : Sign) : Canonical (.zero s)
  | subnormal (s : Sign) (m : Nat) (h : 0 < m) (hm : m < 2 ^ 52) :
      Canonical (.finite s m (-1074) h)
  | normal (s : Sign) (m : Nat) (e : Int) (h : 0 < m)
      (hlo : 2 ^ 52 ≤ m) (hhi : m < 2 ^ 53) (helo : -1074 ≤ e) (hehi : e ≤ 971) :
      Canonical (.finite s m e h)

theorem toNat_one_append {w : Nat} (v : BitVec w) :
    (1#1 ++ v).toNat = 2 ^ w + v.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt v.isLt]
  simp [Nat.shiftLeft_eq]

theorem canonical_unpack (b : BitVec Format.binary64.numBits) :
    Canonical (unpack .binary64 b) := by
  rw [UnpackedFloat.unpack]
  split
  · split
    · exact .infinity _
    · exact .notANumber
  · rename_i hnotinf
    split
    · rename_i hzeroexp
      split
      · exact .zero _
      · rename_i hmnz
        have hbias : ((Format.binary64.exponentBias : Nat) : Int) = 1023 := rfl
        have hmb : ((Format.binary64.mantissaBitsWithoutImplicit : Nat) : Int) = 52 := rfl
        have hexp0 : (unpackExponent b).toNat = 0 := by
          simp [BitVec.toNat_eq] at hzeroexp; exact hzeroexp
        have he : ((unpackExponent b).toNat : Int)
            - ((Format.binary64.exponentBias : Nat)
              + (Format.binary64.mantissaBitsWithoutImplicit : Nat)) + 1 = -1074 := by
          rw [hexp0, hbias, hmb]; omega
        rw [he]
        exact .subnormal _ _ _ (unpackMantissa b).isLt
    · rename_i hnzexp
      have hmlt : (unpackMantissa b).toNat < 2 ^ 52 := (unpackMantissa b).isLt
      have happ : (1#1 ++ unpackMantissa b).toNat = 2 ^ 52 + (unpackMantissa b).toNat :=
        toNat_one_append _
      have hexpLt : (unpackExponent b).toNat < 2048 := (unpackExponent b).isLt
      simp [BitVec.toNat_eq] at hnotinf hnzexp
      have hbias : ((Format.binary64.exponentBias : Nat) : Int) = 1023 := rfl
      have hmb : ((Format.binary64.mantissaBitsWithoutImplicit : Nat) : Int) = 52 := rfl
      refine .normal _ _ _ _ ?_ ?_ (by rw [hbias, hmb]; omega) (by rw [hbias, hmb]; omega) <;> omega

/-- Repacking a canonical value and unpacking it again changes nothing.
The normal case is `unpack_pack_of_normal64`; the rest are the specials
and the subnormal band. -/
theorem unpack_pack_of_canonical {u : UnpackedFloat} (h : Canonical u) :
    unpack .binary64 (UnpackedFloat.pack .binary64 u) = u := by
  cases h with
  | notANumber => rfl
  | infinity s => cases s <;> rfl
  | zero s => cases s <;> rfl
  | subnormal s m h hm =>
      have hlog : ¬52 ≤ m.log2 := fun hc => by
        have := (Nat.le_log2 (by omega)).mp hc; omega
      have hbias : (-1074 + (Format.binary64.exponentBias : Int)
          + (Format.binary64.mantissaBitsWithoutImplicit : Int)).toNat = 1 := by decide
      have hmb : Format.binary64.mantissaBits = 53 := by decide
      rw [UnpackedFloat.pack]
      simp only [hbias, hmb]
      rw [if_neg (by decide), if_neg (by omega), UnpackedFloat.unpack]
      simp only [unpackMantissa_packComponents, unpackExponent_packComponents,
        unpackSign_packComponents64]
      have hmant : (BitVec.ofNat 52 m).toNat = m := by
        simp [BitVec.toNat_ofNat]; omega
      have hne : BitVec.ofNat 52 m ≠ 0#52 := by
        intro heq
        have := congrArg BitVec.toNat heq
        rw [hmant] at this
        simp at this
        omega
      rw [if_neg (by decide), if_pos trivial, dif_neg hne]
      have hb1023 : ((Format.binary64.exponentBias : Nat) : Int) = 1023 := rfl
      simp [hmant, hb1023]
  | normal s m e h hlo hhi helo hehi =>
      exact unpack_pack_of_normal64 s m e h hlo hhi helo hehi

/-- Negation only flips the sign, so it stays inside the canonical set. -/
theorem canonical_neg {u : UnpackedFloat} (h : Canonical u) : Canonical u.neg := by
  cases h with
  | notANumber => exact .notANumber
  | infinity s => exact .infinity _
  | zero s => exact .zero _
  | subnormal s m h hm => exact .subnormal _ m h hm
  | normal s m e h hlo hhi helo hehi => exact .normal _ m e h hlo hhi helo hehi

theorem model_unpack_pack (u : UnpackedFloat) :
    (Float.Model.pack u).unpack = unpack .binary64 (UnpackedFloat.pack .binary64 u) := rfl

theorem model_unpack_pack_neg (f : Float.Model) :
    (Float.Model.pack f.unpack.neg).unpack = f.unpack.neg := by
  rw [model_unpack_pack]
  exact unpack_pack_of_canonical (canonical_neg (canonical_unpack _))

/-! ## The reverse round-trip

`unpack_pack_of_canonical` strips a repacking from a value that gets
repacked; a fact whose result is *compared* instead — `le`, `lt`, `beq`
all read `unpack` and never repack — needs the other direction. It holds
of every valid bit pattern, the validity being what rules out the one
counterexample, a non-canonical `NaN` payload. -/

/-- A 64-bit word is its own (1, 11, 52) split reassembled. -/
theorem packComponents_unpack (b : BitVec Format.binary64.numBits) :
    packComponents .binary64 (Sign.ofBitVec (unpackSign b)) (unpackExponent b)
      (unpackMantissa b) = b := by
  simp only [packComponents, sign_toBitVec_ofBitVec, unpackSign, unpackExponent,
    unpackMantissa, BitVec.extractLsb]
  ext i hi
  grind

/-- The decomposition with the exponent and mantissa named by whichever
`unpack` branch produced them. -/
theorem packComponents_eq_self {b : BitVec Format.binary64.numBits}
    {e : BitVec Format.binary64.exponentBits}
    {m : BitVec Format.binary64.mantissaBitsWithoutImplicit}
    (he : unpackExponent b = e) (hm : unpackMantissa b = m) :
    packComponents .binary64 (Sign.ofBitVec (unpackSign b)) e m = b := by
  subst he hm; exact packComponents_unpack b

theorem pack_unpack_of_valid {b : BitVec Format.binary64.numBits}
    (hv : Format.binary64.Valid b) :
    UnpackedFloat.pack .binary64 (unpack .binary64 b) = b := by
  have hbias : ((Format.binary64.exponentBias : Nat) : Int) = 1023 := rfl
  have hmb : ((Format.binary64.mantissaBitsWithoutImplicit : Nat) : Int) = 52 := rfl
  have hmlt : (unpackMantissa b).toNat < 2 ^ 52 := (unpackMantissa b).isLt
  have hElt : (unpackExponent b).toNat < 2 ^ 11 := (unpackExponent b).isLt
  rw [UnpackedFloat.unpack]
  split
  · rename_i hexp
    split
    · rename_i hmant
      exact packComponents_eq_self hexp hmant
    · rename_i hmant
      exact (hv.eq_packedNaN hexp hmant).symm
  · rename_i hexpne
    split
    · rename_i hexp0
      split
      · rename_i hmant
        exact packComponents_eq_self hexp0 hmant
      · rename_i hmant
        -- subnormal: the biased exponent lands on 1, and a mantissa below
        -- 2^52 cannot reach the normal branch's log2 test
        have hE : (unpackExponent b).toNat = 0 := by rw [hexp0]; rfl
        have hmpos : 0 < (unpackMantissa b).toNat := by
          rcases Nat.eq_zero_or_pos (unpackMantissa b).toNat with h | h
          · exact absurd (BitVec.toNat_inj.mp (by simpa using h)) hmant
          · exact h
        have hbe : (((unpackExponent b).toNat : Int)
            - ((Format.binary64.exponentBias : Nat)
              + (Format.binary64.mantissaBitsWithoutImplicit : Nat))
            + 1 + (Format.binary64.exponentBias : Nat)
            + (Format.binary64.mantissaBitsWithoutImplicit : Nat)).toNat = 1 := by
          rw [hE, hbias, hmb]; omega
        have hlog : ¬((unpackMantissa b).toNat.log2 + 1 = Format.binary64.mantissaBits) := by
          have h52 : ¬52 ≤ (unpackMantissa b).toNat.log2 := fun hc => by
            have := (Nat.le_log2 (by omega)).mp hc; omega
          have h53 : Format.binary64.mantissaBits = 53 := by decide
          omega
        rw [UnpackedFloat.pack]
        simp only [hbe]
        rw [if_neg (by decide), if_neg hlog]
        refine packComponents_eq_self hexp0 ?_
        rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rename_i hexpnz
      -- normal: the biased exponent is the stored one, which is neither
      -- all-ones nor zero, and the implicit bit pins log2 at 52
      have hEne : (unpackExponent b).toNat ≠ 2 ^ 11 - 1 := fun h =>
        hexpne (BitVec.toNat_inj.mp (by simpa using h))
      have hEnz : (unpackExponent b).toNat ≠ 0 := fun h =>
        hexpnz (BitVec.toNat_inj.mp (by simpa using h))
      have happ : (1#1 ++ unpackMantissa b).toNat = 2 ^ 52 + (unpackMantissa b).toNat :=
        toNat_one_append _
      have hbe : (((unpackExponent b).toNat : Int)
          - ((Format.binary64.exponentBias : Nat)
            + (Format.binary64.mantissaBitsWithoutImplicit : Nat))
          + (Format.binary64.exponentBias : Nat)
          + (Format.binary64.mantissaBitsWithoutImplicit : Nat)).toNat
          = (unpackExponent b).toNat := by
        rw [hbias, hmb]; omega
      have hlog : (1#1 ++ unpackMantissa b).toNat.log2 + 1 = Format.binary64.mantissaBits := by
        have h1 : 52 ≤ (1#1 ++ unpackMantissa b).toNat.log2 :=
          (Nat.le_log2 (by omega)).mpr (by omega)
        have h2 : ¬53 ≤ (1#1 ++ unpackMantissa b).toNat.log2 := fun hc => by
          have := (Nat.le_log2 (by omega)).mp hc; omega
        have h53 : Format.binary64.mantissaBits = 53 := by decide
        omega
      rw [UnpackedFloat.pack]
      simp only [hbe]
      rw [if_neg (by simp only [Format.binary64]; omega), if_pos hlog]
      refine packComponents_eq_self ?_ ?_
      · rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      · rw [← BitVec.toNat_inj, BitVec.toNat_ofNat, happ,
          show (2 : Nat) ^ Format.binary64.mantissaBitsWithoutImplicit = 2 ^ 52 from rfl]
        omega

/-- A `Float.Model` carries its own validity proof, so it is exactly a
valid bit pattern and the round-trip is unconditional. -/
theorem model_pack_unpack (f : Float.Model) : Float.Model.pack f.unpack = f := by
  obtain ⟨bits, hv⟩ := f
  have h : UnpackedFloat.pack .binary64 (unpack .binary64 bits.toBitVec) = bits.toBitVec :=
    pack_unpack_of_valid hv
  simp only [Float.Model.pack, Float.Model.unpack, h]

/-! ## Facts at the `Float` layer

What the residual goals are actually stated in. -/

/-- IEEE subtraction is addition of the negation. Lifting the
`UnpackedFloat` fact costs one round-trip: `-b` repacks before `+`
unpacks it again. -/
theorem float_sub_eq_add_neg (a b : Float) : a - b = a + (-b) := by
  show Float.ofModel (Float.Model.sub a.toModel b.toModel)
     = Float.ofModel (Float.Model.add a.toModel (Float.Model.neg b.toModel))
  congr 1
  rw [Float.Model.sub, Float.Model.add, Float.Model.neg, model_unpack_pack_neg,
    sub_eq_add_neg]

/-- Double negation. Both round-trip directions are load-bearing here:
the inner `-b` repacks before the outer `neg` unpacks it, and the result
must repack to the float it started as. -/
theorem float_neg_neg (a : Float) : - -a = a := by
  show Float.ofModel (Float.Model.neg (Float.Model.neg a.toModel)) = a
  rw [Float.Model.neg, Float.Model.neg, model_unpack_pack_neg, neg_neg, model_pack_unpack]

/-- Commutativity survives the packing: both orientations round the same
unpacked product. -/
theorem float_mul_comm (a b : Float) : a * b = b * a := by
  show Float.ofModel (Float.Model.mul a.toModel b.toModel)
     = Float.ofModel (Float.Model.mul b.toModel a.toModel)
  congr 1
  rw [Float.Model.mul, Float.Model.mul, mul_comm]

theorem float_add_comm (a b : Float) : a + b = b + a := by
  show Float.ofModel (Float.Model.add a.toModel b.toModel)
     = Float.ofModel (Float.Model.add b.toModel a.toModel)
  congr 1
  rw [Float.Model.add, Float.Model.add, add_comm]


/-! ## Fraction-augmented rounding arithmetic -/

/-- Round-to-nearest-even of `(m + num/den) / 2^n`: the discarded part is
`(m % 2^n + num/den)` out of `2^n`, compared against half via
cross-multiplication by `den`. -/
def rnShiftF (m n num den : Nat) : Nat :=
  let q := m / 2 ^ n
  let r := (m % 2 ^ n) * den + num
  if r * 2 < 2 ^ n * den then q
  else if r * 2 = 2 ^ n * den then q + q % 2
  else q + 1

theorem rnShiftF_zero_num (m n den : Nat) (hden : 0 < den) :
    rnShiftF m n 0 den = rnShift m n := by
  rw [rnShiftF, rnShift]
  have h1 : m % 2 ^ n * den * 2 < 2 ^ n * den ↔ m % 2 ^ n * 2 < 2 ^ n := by
    rw [Nat.mul_right_comm]
    exact Nat.mul_lt_mul_right hden
  have h2 : m % 2 ^ n * den * 2 = 2 ^ n * den ↔ m % 2 ^ n * 2 = 2 ^ n := by
    rw [Nat.mul_right_comm]
    exact ⟨fun h => Nat.eq_of_mul_eq_mul_right hden h, fun h => by rw [h]⟩
  grind

theorem rnShiftF_of_lt {m n num den : Nat}
    (h : (m % 2 ^ n * den + num) * 2 < 2 ^ n * den) :
    rnShiftF m n num den = m / 2 ^ n := by
  rw [rnShiftF]
  grind

theorem rnShiftF_of_eq {m n num den : Nat}
    (h : (m % 2 ^ n * den + num) * 2 = 2 ^ n * den) :
    rnShiftF m n num den = m / 2 ^ n + m / 2 ^ n % 2 := by
  rw [rnShiftF]
  grind

theorem rnShiftF_of_gt {m n num den : Nat}
    (h : 2 ^ n * den < (m % 2 ^ n * den + num) * 2) :
    rnShiftF m n num den = m / 2 ^ n + 1 := by
  rw [rnShiftF]
  grind

theorem rnShiftF_bounds (m n num den : Nat) :
    m / 2 ^ n ≤ rnShiftF m n num den ∧ rnShiftF m n num den ≤ m / 2 ^ n + 1 := by
  rw [rnShiftF]
  grind

/-! ## The shift pipeline with an initial accuracy -/

/-- `k+1` right-shifts starting from residual bits `(rb, sb)`: the
original round bit joins the sticky mass. -/
theorem repeat_shiftRightOne_eq_from (m : Nat) (rb sb : Bool) (k : Nat) :
    Nat.repeat ExtendedMantissa.shiftRightOne (k + 1) ⟨m, rb, sb⟩ =
      ⟨m / 2 ^ (k + 1), m / 2 ^ k % 2 == 1, (m % 2 ^ k != 0) || rb || sb⟩ := by
  induction k with
  | zero =>
    simp [Nat.repeat, ExtendedMantissa.shiftRightOne]
    grind
  | succ j ih =>
    rw [Nat.repeat, ih]
    simp only [ExtendedMantissa.shiftRightOne]
    refine ExtendedMantissa.mk.injEq .. ▸ ⟨?_, ?_, ?_⟩
    · show m / 2 ^ (j + 1) / 2 = m / 2 ^ (j + 1 + 1)
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ]
    · show (m / 2 ^ (j + 1) % 2 != 0) = (m / 2 ^ (j + 1) % 2 == 1)
      grind
    · show ((m / 2 ^ j % 2 == 1) || ((m % 2 ^ j != 0) || rb || sb))
          = ((m % 2 ^ (j + 1) != 0) || rb || sb)
      have h : m % 2 ^ (j + 1) = 2 ^ j * (m / 2 ^ j % 2) + m % 2 ^ j := by
        rw [Nat.pow_succ, Nat.mod_mul]
        omega
      grind

/-- The four ways an initial fraction can sit against a half ulp, with
the arithmetic fact each case carries. -/
theorem accuracyOfFraction_cases (num den : Nat) (_hden : 0 < den) (hnum : num < den) :
    (accuracyOfFraction num den = .exact ∧ num = 0)
    ∨ (accuracyOfFraction num den = .inexact .lt ∧ 0 < num ∧ 2 * num < den)
    ∨ (accuracyOfFraction num den = .inexact .eq ∧ 0 < num ∧ 2 * num = den)
    ∨ (accuracyOfFraction num den = .inexact .gt ∧ 0 < num ∧ den < 2 * num) := by
  rcases Nat.eq_zero_or_pos num with h0 | h0
  · subst h0
    exact Or.inl ⟨by rw [accuracyOfFraction, if_pos rfl], rfl⟩
  · rcases Nat.lt_trichotomy (2 * num) den with hc | hc | hc
    · exact Or.inr (Or.inl ⟨by
        rw [accuracyOfFraction, if_neg (by omega), Nat.compare_eq_lt.mpr hc], h0, hc⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨by
        rw [accuracyOfFraction, if_neg (by omega), Nat.compare_eq_eq.mpr hc], h0, hc⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨by
        rw [accuracyOfFraction, if_neg (by omega), Nat.compare_eq_gt.mpr hc], h0, hc⟩))

/-- Which `rnShiftF` branch fires at a successor shift, characterized
den-free by the round bit, the low bits, and the initial fraction. -/
theorem rnShiftF_succ_char (m k num den : Nat) (hden : 0 < den) (hnum : num < den) :
    (m / 2 ^ k % 2 = 0 → rnShiftF m (k + 1) num den = m / 2 ^ (k + 1))
    ∧ (m / 2 ^ k % 2 = 1 → m % 2 ^ k = 0 → num = 0 →
        rnShiftF m (k + 1) num den = m / 2 ^ (k + 1) + m / 2 ^ (k + 1) % 2)
    ∧ (m / 2 ^ k % 2 = 1 → (0 < m % 2 ^ k ∨ 0 < num) →
        rnShiftF m (k + 1) num den = m / 2 ^ (k + 1) + 1) := by
  have h : m % 2 ^ (k + 1) = 2 ^ k * (m / 2 ^ k % 2) + m % 2 ^ k := by
    rw [Nat.pow_succ, Nat.mod_mul]
    omega
  have hmk : m % 2 ^ k < 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
  have hpow : 2 ^ (k + 1) * den = 2 ^ k * den * 2 := by
    rw [Nat.pow_succ]
    grind
  have hmul : (m % 2 ^ k + 1) * den ≤ 2 ^ k * den := Nat.mul_le_mul_right _ (by omega)
  have hms : (m % 2 ^ k + 1) * den = m % 2 ^ k * den + den := Nat.succ_mul _ _
  refine ⟨?_, ?_, ?_⟩
  · intro hb
    apply rnShiftF_of_lt
    have hmm : m % 2 ^ (k + 1) * den = m % 2 ^ k * den := by
      rw [h, hb]
      grind
    omega
  · intro hb hs h0
    apply rnShiftF_of_eq
    have hmm : m % 2 ^ (k + 1) * den = 2 ^ k * den := by
      rw [h, hb, hs]
      grind
    omega
  · intro hb hs
    apply rnShiftF_of_gt
    have hmm : m % 2 ^ (k + 1) * den = 2 ^ k * den + m % 2 ^ k * den := by
      rw [h, hb]
      grind
    have hsd : 0 < m % 2 ^ k * den ∨ 0 < num := by
      rcases hs with hs | hs
      · exact Or.inl (Nat.mul_pos hs hden)
      · exact Or.inr hs
    omega

/-- The pipeline seeded with `accuracyOfFraction num den` rounds to exactly
`rnShiftF`. -/
theorem roundedMantissa_ofFraction (m n num den : Nat) (hden : 0 < den)
    (hnum : num < den) :
    (Nat.repeat ExtendedMantissa.shiftRightOne n
        (ExtendedMantissa.ofMantissaAndAccuracy m (accuracyOfFraction num den))).roundedMantissa
      = rnShiftF m n num den := by
  obtain ⟨hchar0, hchar1, hchar2⟩ := rnShiftF_succ_char m (n - 1) num den hden hnum
  rcases accuracyOfFraction_cases num den hden hnum with
      ⟨ha, hf⟩ | ⟨ha, hp, hf⟩ | ⟨ha, hp, hf⟩ | ⟨ha, hp, hf⟩ <;>
    rw [ha] <;>
    simp only [ExtendedMantissa.ofMantissaAndAccuracy] <;>
    cases n with
    | zero =>
      simp only [Nat.repeat]
      rw [ExtendedMantissa.roundedMantissa]
      grind [ExtendedMantissa.accuracy, Accuracy.roundToNearestEven, rnShiftF]
    | succ k =>
      rw [repeat_shiftRightOne_eq_from, ExtendedMantissa.roundedMantissa]
      rcases Bool.eq_false_or_eq_true (m / 2 ^ k % 2 == 1) with hb | hb <;>
        rcases Bool.eq_false_or_eq_true (m % 2 ^ k != 0) with hs | hs <;>
          simp only [hb, hs, Bool.or_false, Bool.or_true,
            ExtendedMantissa.accuracy, Accuracy.roundToNearestEven] <;>
          grind

/-! ## The closed form of binary64 rounding -/

/-- The exponent the rounded result of `(m, e)` sits on: 53 significant
bits, floored at the subnormal quantum. -/
def grid (m : Nat) (e : Int) : Int :=
  max (totalExponent m e - 53) (-1074)

theorem grid_ge (m : Nat) (e : Int) : -1074 ≤ grid m e := by
  simp [grid]; omega

/-- `roundWithAccuracy`'s documented contract: the input exponent does not
exceed the grid, so no significant bits sit below the input's own
granularity. Every call site below satisfies it. -/
def WellPlaced (m : Nat) (e : Int) : Prop := e ≤ grid m e

theorem rnShiftF_le (m : Nat) (e : Int) (num den : Nat) (hw : WellPlaced m e) :
    rnShiftF m ((grid m e - e).toNat) num den ≤ 2 ^ 53 := by
  have h2 := (rnShiftF_bounds m ((grid m e - e).toNat) num den).2
  have hlog : m < 2 ^ (m.log2 + 1) := Nat.lt_log2_self
  have hn : m.log2 + 1 ≤ (grid m e - e).toNat + 53 := by
    simp only [WellPlaced, grid, totalExponent] at hw
    simp only [grid, totalExponent]
    omega
  have hm : m < 2 ^ 53 * 2 ^ (grid m e - e).toNat := by
    calc m < 2 ^ (m.log2 + 1) := hlog
      _ ≤ 2 ^ ((grid m e - e).toNat + 53) := Nat.pow_le_pow_right (by omega) hn
      _ = 2 ^ 53 * 2 ^ (grid m e - e).toNat := by rw [← Nat.pow_add, Nat.add_comm]
  have hq : m / 2 ^ (grid m e - e).toNat < 2 ^ 53 := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    omega
  omega

theorem targetExponent_binary64 (t : Int) :
    Format.binary64.targetExponent t = max (t - 53) (-1074) := by
  rw [Format.targetExponent]
  have h1 : ((Format.binary64.mantissaBits : Nat) : Int) = 53 := by decide
  have h2 : Format.binary64.minExponent = -1074 := by decide
  rw [h1, h2]

/-- `roundWithAccuracy`, definitionally, with every pipeline stage named. -/
theorem roundWA_unfold (spec : Format) (s : Sign) (m : Nat) (e : Int) (a : Accuracy) :
    roundWithAccuracy spec s m e a =
      (let n₁ := (spec.targetExponent (totalExponent m e) - e).toNat
      let r := (Nat.repeat ExtendedMantissa.shiftRightOne n₁
        (ExtendedMantissa.ofMantissaAndAccuracy m a)).roundedMantissa
      let e₁ := e + n₁
      let n₂ := (spec.targetExponent (totalExponent r e₁) - e₁).toNat
      let fm := (Nat.repeat ExtendedMantissa.shiftRightOne n₂
        (ExtendedMantissa.ofMantissaAndAccuracy r .exact)).mantissa
      if h : fm = 0 then .zero s
      else .finite s fm (e₁ + n₂) (Nat.pos_of_ne_zero h)) := rfl

/-- The second shift of the pipeline only fires on mantissa overflow, and
then it is exact: the value it drops is a zero bit. -/
theorem roundWA_eq (s : Sign) (m : Nat) (e : Int) (num den : Nat)
    (hw : WellPlaced m e) (hden : 0 < den) (hnum : num < den) :
    roundWithAccuracy .binary64 s m e (accuracyOfFraction num den) =
      if rnShiftF m ((grid m e - e).toNat) num den = 2 ^ 53 then
        .finite s (2 ^ 52) (grid m e + 1) (by simp)
      else if h : rnShiftF m ((grid m e - e).toNat) num den = 0 then .zero s
      else .finite s (rnShiftF m ((grid m e - e).toNat) num den) (grid m e)
        (Nat.pos_of_ne_zero h) := by
  have hG := grid_ge m e
  have hr_le := rnShiftF_le m e num den hw
  have htgt : Format.binary64.targetExponent (totalExponent m e) = grid m e := by
    rw [targetExponent_binary64, grid]
  have he₁ : e + ((grid m e - e).toNat : Int) = grid m e := by
    simp only [WellPlaced] at hw
    omega
  rw [roundWA_unfold]
  simp only [htgt, he₁,
    roundedMantissa_ofFraction m ((grid m e - e).toNat) num den hden hnum]
  rcases Nat.eq_or_lt_of_le hr_le with hovf | hlt
  · -- Overflow: the rounded mantissa is exactly 2^53; one exact shift
    -- carries it into the next binade.
    simp only [hovf]
    have hlog : (2 ^ 53 : Nat).log2 = 53 := by
      have h1 : 53 ≤ (2 ^ 53 : Nat).log2 := (Nat.le_log2 (by omega)).mpr (Nat.le_refl _)
      have h2 : (2 ^ 53 : Nat).log2 < 54 :=
        (Nat.log2_lt (by omega)).mpr (Nat.pow_lt_pow_right (by omega) (by omega))
      omega
    have htgt₂ : Format.binary64.targetExponent (totalExponent (2 ^ 53) (grid m e))
        = grid m e + 1 := by
      rw [targetExponent_binary64, totalExponent, hlog]
      omega
    have hn₂ : (grid m e + 1 - grid m e).toNat = 1 := by omega
    have hshift : (Nat.repeat ExtendedMantissa.shiftRightOne 1
        (ExtendedMantissa.ofMantissaAndAccuracy (2 ^ 53) .exact)).mantissa = 2 ^ 52 := by
      simp only [ExtendedMantissa.ofMantissaAndAccuracy, Nat.repeat,
        ExtendedMantissa.shiftRightOne]
    simp only [htgt₂, hn₂, hshift, Int.natCast_one]
    rw [dif_neg (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos 52)), if_pos trivial]
  · -- No overflow: the second shift is the identity.
    have hlog : (rnShiftF m ((grid m e - e).toNat) num den).log2 ≤ 52 := by
      rcases Nat.eq_zero_or_pos (rnShiftF m ((grid m e - e).toNat) num den) with h0 | h0
      · rw [h0]
        exact Nat.le_of_lt_succ (by rw [show Nat.log2 0 = 0 from rfl]; omega)
      · exact Nat.le_of_lt_succ ((Nat.log2_lt (by omega)).mpr hlt)
    have htgt₂ : Format.binary64.targetExponent
        (totalExponent (rnShiftF m ((grid m e - e).toNat) num den) (grid m e))
        ≤ grid m e := by
      rw [targetExponent_binary64, totalExponent]
      omega
    have hn₂ : (Format.binary64.targetExponent
        (totalExponent (rnShiftF m ((grid m e - e).toNat) num den) (grid m e))
        - grid m e).toNat = 0 := by omega
    simp only [hn₂, Nat.repeat, ExtendedMantissa.ofMantissaAndAccuracy,
      Int.natCast_zero, Int.add_zero]
    rw [if_neg (by omega : ¬rnShiftF m ((grid m e - e).toNat) num den = 2 ^ 53)]

/-! ## Value semantics -/

/-- Larger than any value binary64 rounding can produce from the operations
below, so infinities sit strictly outside every finite key. -/
def HUGE : Int := 2 ^ 6000

/-- The value of an unpacked float in `2^(-1074)` units (the binary64
subnormal quantum), with infinities pushed past every finite value. Only
meaningful on exponents `≥ -1074`, which covers every canonical float and
every binary64 rounding output. -/
def key : UnpackedFloat → Int
  | .notANumber => 0
  | .infinity s => s.apply HUGE
  | .zero _ => 0
  | .finite s m e _ => s.apply (m * 2 ^ (e + 1074).toNat)

/-- The key of a positive rounding, in closed form. -/
theorem key_roundWA_pos (m : Nat) (e : Int) (num den : Nat)
    (hw : WellPlaced m e) (hden : 0 < den) (hnum : num < den) :
    key (roundWithAccuracy .binary64 .positive m e (accuracyOfFraction num den)) =
      rnShiftF m ((grid m e - e).toNat) num den * 2 ^ (grid m e + 1074).toNat := by
  have hG := grid_ge m e
  rw [roundWA_eq .positive m e num den hw hden hnum]
  by_cases hovf : rnShiftF m ((grid m e - e).toNat) num den = 2 ^ 53
  · rw [if_pos hovf, hovf]
    simp only [key, Sign.apply]
    have ha : (grid m e + 1 + 1074).toNat = (grid m e + 1074).toNat + 1 := by omega
    rw [ha]
    have hnat : (2 : Nat) ^ 53 * 2 ^ (grid m e + 1074).toNat
        = 2 ^ 52 * 2 ^ ((grid m e + 1074).toNat + 1) := by
      rw [Nat.pow_succ]
      grind
    have hcast2 : (2 : Int) = ((2 : Nat) : Int) := rfl
    rw [hcast2, ← Int.natCast_pow, ← Int.natCast_pow, ← Int.natCast_mul, ← Int.natCast_mul]
    omega
  · rw [if_neg hovf]
    rcases Nat.eq_zero_or_pos (rnShiftF m ((grid m e - e).toNat) num den) with h0 | h0
    · rw [dif_pos h0, h0]
      simp [key]
    · rw [dif_neg (Nat.pos_iff_ne_zero.mp h0)]
      simp [key, Sign.apply]

/-- Rounding only threads the sign through, so the negative key mirrors the
positive one. -/
theorem key_roundWA_neg (m : Nat) (e : Int) (num den : Nat)
    (hw : WellPlaced m e) (hden : 0 < den) (hnum : num < den) :
    key (roundWithAccuracy .binary64 .negative m e (accuracyOfFraction num den)) =
      -key (roundWithAccuracy .binary64 .positive m e (accuracyOfFraction num den)) := by
  rw [roundWA_eq .negative m e num den hw hden hnum,
    roundWA_eq .positive m e num den hw hden hnum]
  by_cases hovf : rnShiftF m ((grid m e - e).toNat) num den = 2 ^ 53
  · rw [if_pos hovf, if_pos hovf]
    simp [key, Sign.apply]
  · rw [if_neg hovf, if_neg hovf]
    rcases Nat.eq_zero_or_pos (rnShiftF m ((grid m e - e).toNat) num den) with h0 | h0
    · rw [dif_pos h0, dif_pos h0]
      simp [key]
    · rw [dif_neg (Nat.pos_iff_ne_zero.mp h0), dif_neg (Nat.pos_iff_ne_zero.mp h0)]
      simp [key, Sign.apply]

/-! ## The master monotonicity theorem

Rounding is monotone on real values. The two inputs may sit on different
grids; the hypothesis compares the exact values `(mᵢ + numᵢ/den) · 2^eᵢ`
at the common exponent `min e₁ e₂`, cross-multiplied by `den` to stay in
`Nat`. -/

/-- Same output grid: the quotient at the grid is monotone by division, and
an equal quotient hands the decision to the discarded fractions, compared on
the common scale. -/
theorem rnShiftF_mono_scaled
    {den m₁ num₁ n₁ p₁ m₂ num₂ n₂ p₂ : Nat}
    (_hden : 0 < den) (hnum₁ : num₁ < den) (hnum₂ : num₂ < den)
    (hgg : n₁ + p₁ = n₂ + p₂)
    (h : (m₁ * den + num₁) * 2 ^ p₁ ≤ (m₂ * den + num₂) * 2 ^ p₂) :
    rnShiftF m₁ n₁ num₁ den ≤ rnShiftF m₂ n₂ num₂ den := by
  have hb₁ := rnShiftF_bounds m₁ n₁ num₁ den
  have hb₂ := rnShiftF_bounds m₂ n₂ num₂ den
  -- Decompose each side against the common scale den * 2^(n+p).
  have decomp : ∀ (m num n p : Nat), num < den →
      (m * den + num) * 2 ^ p
        = den * 2 ^ n * 2 ^ p * (m / 2 ^ n) + (m % 2 ^ n * den + num) * 2 ^ p
      ∧ (m % 2 ^ n * den + num) * 2 ^ p < den * 2 ^ n * 2 ^ p := by
    intro m num n p hnum
    have hd : ∀ q r, m = 2 ^ n * q + r →
        (m * den + num) * 2 ^ p
          = den * 2 ^ n * 2 ^ p * q + (r * den + num) * 2 ^ p := by
      intro q r hqr
      rw [hqr]
      grind
    have hmod : m % 2 ^ n < 2 ^ n := Nat.mod_lt _ (Nat.two_pow_pos n)
    refine ⟨hd (m / 2 ^ n) (m % 2 ^ n) (Nat.div_add_mod m (2 ^ n)).symm, ?_⟩
    have hinner : m % 2 ^ n * den + num < 2 ^ n * den := by
      have h1 : (m % 2 ^ n + 1) * den ≤ 2 ^ n * den :=
        Nat.mul_le_mul_right _ (by omega)
      have h2 : (m % 2 ^ n + 1) * den = m % 2 ^ n * den + den := by grind
      omega
    calc (m % 2 ^ n * den + num) * 2 ^ p
        < 2 ^ n * den * 2 ^ p := (Nat.mul_lt_mul_right (Nat.two_pow_pos p)).mpr hinner
      _ = den * 2 ^ n * 2 ^ p := by grind
  obtain ⟨hV₁, hr₁⟩ := decomp m₁ num₁ n₁ p₁ hnum₁
  obtain ⟨hV₂, hr₂⟩ := decomp m₂ num₂ n₂ p₂ hnum₂
  -- The two scales agree.
  have hDD : den * 2 ^ n₁ * 2 ^ p₁ = den * 2 ^ n₂ * 2 ^ p₂ := by
    rw [Nat.mul_assoc, Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add, hgg]
  rw [hV₁, hV₂, ← hDD] at h
  rw [← hDD] at hr₂
  have hq : m₁ / 2 ^ n₁ ≤ m₂ / 2 ^ n₂ := by
    rcases Nat.lt_or_ge (m₂ / 2 ^ n₂) (m₁ / 2 ^ n₁) with hlt | hge
    · exfalso
      have hstep : den * 2 ^ n₁ * 2 ^ p₁ * (m₂ / 2 ^ n₂ + 1)
          ≤ den * 2 ^ n₁ * 2 ^ p₁ * (m₁ / 2 ^ n₁) :=
        Nat.mul_le_mul_left _ (by omega)
      have hsucc : den * 2 ^ n₁ * 2 ^ p₁ * (m₂ / 2 ^ n₂ + 1)
          = den * 2 ^ n₁ * 2 ^ p₁ * (m₂ / 2 ^ n₂) + den * 2 ^ n₁ * 2 ^ p₁ :=
        Nat.mul_succ _ _
      omega
    · exact hge
  rcases Nat.eq_or_lt_of_le hq with hqe | hql
  · -- Equal quotients: the discarded fractions decide.
    have hrr : (m₁ % 2 ^ n₁ * den + num₁) * 2 ^ p₁
        ≤ (m₂ % 2 ^ n₂ * den + num₂) * 2 ^ p₂ := by
      rw [← hqe] at h
      omega
    -- Branch tests transfer to the common scale.
    have trans : ∀ (m num n p : Nat),
        ((m % 2 ^ n * den + num) * 2 < 2 ^ n * den
          ↔ (m % 2 ^ n * den + num) * 2 ^ p * 2 < den * 2 ^ n * 2 ^ p)
        ∧ ((m % 2 ^ n * den + num) * 2 = 2 ^ n * den
          ↔ (m % 2 ^ n * den + num) * 2 ^ p * 2 = den * 2 ^ n * 2 ^ p) := by
      intro m num n p
      have e1 : (m % 2 ^ n * den + num) * 2 ^ p * 2
          = (m % 2 ^ n * den + num) * 2 * 2 ^ p := by grind
      have e2 : den * 2 ^ n * 2 ^ p = 2 ^ n * den * 2 ^ p := by grind
      rw [e1, e2, Nat.mul_lt_mul_right (Nat.two_pow_pos p)]
      refine ⟨Iff.rfl, ?_, ?_⟩
      · intro hh
        rw [hh]
      · exact fun hh => Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos p) hh
    obtain ⟨ht₁l, ht₁e⟩ := trans m₁ num₁ n₁ p₁
    obtain ⟨ht₂l, ht₂e⟩ := trans m₂ num₂ n₂ p₂
    rw [← hDD] at ht₂l ht₂e
    have hmul2 : (m₁ % 2 ^ n₁ * den + num₁) * 2 ^ p₁ * 2
        ≤ (m₂ % 2 ^ n₂ * den + num₂) * 2 ^ p₂ * 2 :=
      Nat.mul_le_mul_right _ hrr
    rcases Nat.lt_trichotomy ((m₂ % 2 ^ n₂ * den + num₂) * 2) (2 ^ n₂ * den) with hc₂ | hc₂ | hc₂
    · -- Right fraction below half: so is the left one; both round down.
      have hc₁ : (m₁ % 2 ^ n₁ * den + num₁) * 2 < 2 ^ n₁ * den := by
        apply ht₁l.mpr
        have := ht₂l.mp hc₂
        omega
      rw [rnShiftF_of_lt hc₁, rnShiftF_of_lt hc₂]
      omega
    · -- Right fraction at half: the left one is at or below it.
      have hc₁ : (m₁ % 2 ^ n₁ * den + num₁) * 2 < 2 ^ n₁ * den
          ∨ (m₁ % 2 ^ n₁ * den + num₁) * 2 = 2 ^ n₁ * den := by
        have hD2 := ht₂e.mp hc₂
        rcases Nat.lt_or_ge ((m₁ % 2 ^ n₁ * den + num₁) * 2 ^ p₁ * 2)
            (den * 2 ^ n₁ * 2 ^ p₁) with hlt | hge
        · exact Or.inl (ht₁l.mpr hlt)
        · exact Or.inr (ht₁e.mpr (by omega))
      rw [rnShiftF_of_eq hc₂]
      rcases hc₁ with hc₁ | hc₁
      · rw [rnShiftF_of_lt hc₁]
        omega
      · rw [rnShiftF_of_eq hc₁]
        omega
    · -- Right fraction above half: it rounds up, clearing every left case.
      rw [rnShiftF_of_gt hc₂]
      omega
  · -- Strictly larger quotient: the +1 rounding slack cannot cross it.
    omega

theorem key_roundWA_mono {m₁ m₂ num₁ num₂ den : Nat} {e₁ e₂ : Int}
    (hden : 0 < den) (hnum₁ : num₁ < den) (hnum₂ : num₂ < den)
    (hw₁ : WellPlaced m₁ e₁) (hw₂ : WellPlaced m₂ e₂)
    (h : (m₁ * den + num₁) * 2 ^ (e₁ - min e₁ e₂).toNat
       ≤ (m₂ * den + num₂) * 2 ^ (e₂ - min e₁ e₂).toNat) :
    key (roundWithAccuracy .binary64 .positive m₁ e₁ (accuracyOfFraction num₁ den))
      ≤ key (roundWithAccuracy .binary64 .positive m₂ e₂ (accuracyOfFraction num₂ den)) := by
  rw [key_roundWA_pos m₁ e₁ num₁ den hw₁ hden hnum₁,
    key_roundWA_pos m₂ e₂ num₂ den hw₂ hden hnum₂]
  have hcast : ∀ a b : Nat, a ≤ b → (a : Int) ≤ (b : Int) := fun _ _ => Int.ofNat_le.mpr
  apply hcast
  rcases Int.lt_trichotomy (grid m₁ e₁) (grid m₂ e₂) with hG | hG | hG
  · -- Coarser grid on the left: the right result clears a whole binade
    -- above everything the left grid can express.
    have hle₁ : rnShiftF m₁ ((grid m₁ e₁ - e₁).toNat) num₁ den ≤ 2 ^ 53 :=
      rnShiftF_le m₁ e₁ num₁ den hw₁
    have hb₂ := rnShiftF_bounds m₂ ((grid m₂ e₂ - e₂).toNat) num₂ den
    have hlog₂ : 52 ≤ m₂.log2 ∧ (grid m₂ e₂ - e₂).toNat = m₂.log2 - 52 := by
      have hG' := hG
      have hw := hw₂
      simp only [WellPlaced, grid, totalExponent] at hG' hw ⊢
      omega
    have hm₂ : m₂ ≠ 0 := by
      intro h0
      have hl0 : Nat.log2 0 = 0 := rfl
      rw [h0, hl0] at hlog₂
      omega
    have hq₂ : 2 ^ 52 ≤ m₂ / 2 ^ (grid m₂ e₂ - e₂).toNat := by
      rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos _), ← Nat.pow_add]
      have h52 : 52 + (grid m₂ e₂ - e₂).toNat = m₂.log2 := by omega
      rw [h52]
      exact Nat.log2_self_le hm₂
    have hexp : (grid m₁ e₁ + 1074).toNat + 53 ≤ (grid m₂ e₂ + 1074).toNat + 52 := by
      have hg1 := grid_ge m₁ e₁
      have hg2 := grid_ge m₂ e₂
      omega
    calc rnShiftF m₁ ((grid m₁ e₁ - e₁).toNat) num₁ den * 2 ^ (grid m₁ e₁ + 1074).toNat
        ≤ 2 ^ 53 * 2 ^ (grid m₁ e₁ + 1074).toNat := Nat.mul_le_mul_right _ hle₁
      _ = 2 ^ ((grid m₁ e₁ + 1074).toNat + 53) := by rw [← Nat.pow_add, Nat.add_comm]
      _ ≤ 2 ^ ((grid m₂ e₂ + 1074).toNat + 52) := Nat.pow_le_pow_right (by omega) hexp
      _ = 2 ^ 52 * 2 ^ (grid m₂ e₂ + 1074).toNat := by rw [← Nat.pow_add, Nat.add_comm]
      _ ≤ rnShiftF m₂ ((grid m₂ e₂ - e₂).toNat) num₂ den * 2 ^ (grid m₂ e₂ + 1074).toNat :=
          Nat.mul_le_mul_right _ (Nat.le_trans hq₂ hb₂.1)
  · -- Same grid: the scaled core theorem decides.
    rw [hG]
    apply Nat.mul_le_mul_right
    apply rnShiftF_mono_scaled hden hnum₁ hnum₂ _ h
    have hw1 := hw₁
    have hw2 := hw₂
    simp only [WellPlaced] at hw1 hw2
    omega
  · -- Coarser grid on the right would need the left value to reach a
    -- higher binade than the right value bounds.
    exfalso
    have hlog₁ : 52 ≤ m₁.log2 := by
      have hG' := hG
      have hw := hw₁
      simp only [WellPlaced, grid, totalExponent] at hG' hw
      omega
    have hm₁ : m₁ ≠ 0 := by
      intro h0
      have hl0 : Nat.log2 0 = 0 := rfl
      rw [h0, hl0] at hlog₁
      omega
    have hlow : 2 ^ (m₁.log2 + (e₁ - min e₁ e₂).toNat) * den
        ≤ (m₁ * den + num₁) * 2 ^ (e₁ - min e₁ e₂).toNat := by
      have h1 : 2 ^ m₁.log2 * den ≤ m₁ * den + num₁ := by
        have := Nat.mul_le_mul_right den (Nat.log2_self_le hm₁)
        omega
      calc 2 ^ (m₁.log2 + (e₁ - min e₁ e₂).toNat) * den
          = 2 ^ m₁.log2 * den * 2 ^ (e₁ - min e₁ e₂).toNat := by
            rw [Nat.pow_add]
            grind
        _ ≤ (m₁ * den + num₁) * 2 ^ (e₁ - min e₁ e₂).toNat :=
            Nat.mul_le_mul_right _ h1
    have hhigh : (m₂ * den + num₂) * 2 ^ (e₂ - min e₁ e₂).toNat
        < 2 ^ (m₂.log2 + 1 + (e₂ - min e₁ e₂).toNat) * den := by
      have h1 : m₂ * den + num₂ < 2 ^ (m₂.log2 + 1) * den := by
        have := Nat.mul_le_mul_right den (Nat.lt_log2_self (n := m₂))
        have h2 : (m₂ + 1) * den = m₂ * den + den := by grind
        have h3 : m₂ + 1 ≤ 2 ^ (m₂.log2 + 1) := Nat.lt_log2_self
        have h4 := Nat.mul_le_mul_right den h3
        omega
      calc (m₂ * den + num₂) * 2 ^ (e₂ - min e₁ e₂).toNat
          < 2 ^ (m₂.log2 + 1) * den * 2 ^ (e₂ - min e₁ e₂).toNat :=
            (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr h1
        _ = 2 ^ (m₂.log2 + 1 + (e₂ - min e₁ e₂).toNat) * den := by
            rw [Nat.pow_add]
            grind
    have hexp : m₁.log2 + (e₁ - min e₁ e₂).toNat < m₂.log2 + 1 + (e₂ - min e₁ e₂).toNat := by
      rcases Nat.lt_or_ge (m₁.log2 + (e₁ - min e₁ e₂).toNat)
          (m₂.log2 + 1 + (e₂ - min e₁ e₂).toNat) with hlt | hge
      · exact hlt
      · exfalso
        have hpk : 2 ^ (m₂.log2 + 1 + (e₂ - min e₁ e₂).toNat) * den
            ≤ 2 ^ (m₁.log2 + (e₁ - min e₁ e₂).toNat) * den :=
          Nat.mul_le_mul_right den (Nat.pow_le_pow_right (by omega) hge)
        omega
    have hG' := hG
    have hw := hw₁
    simp only [WellPlaced, grid, totalExponent] at hG' hw
    omega

/-! ## Compare agrees with key on canonical floats -/

/-- The mantissa/exponent bounds a canonical finite float carries. -/
theorem canonical_finite_bounds {s : Sign} {m : Nat} {e : Int} {h : 0 < m}
    (hc : Canonical (.finite s m e h)) :
    m < 2 ^ 53 ∧ -1074 ≤ e ∧ e ≤ 971 ∧ (2 ^ 52 ≤ m ∨ e = -1074) := by
  cases hc with
  | subnormal s m hm hlt => exact ⟨by omega, by omega, by omega, Or.inr rfl⟩
  | normal s m e hm hlo hhi helo hehi => exact ⟨hhi, helo, hehi, Or.inl hlo⟩

/-- The scaled value of a canonical finite float, and its bound below the
infinity sentinel. -/
theorem canonical_value_lt {m : Nat} {e : Int} (hm : m < 2 ^ 53) (he : e ≤ 971) :
    m * 2 ^ (e + 1074).toNat < 2 ^ 2098 := by
  have hx : (e + 1074).toNat ≤ 2045 := by omega
  calc m * 2 ^ (e + 1074).toNat
      < 2 ^ 53 * 2 ^ (e + 1074).toNat :=
        (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr hm
    _ = 2 ^ (53 + (e + 1074).toNat) := by rw [Nat.pow_add]
    _ ≤ 2 ^ 2098 := Nat.pow_le_pow_right (by omega) (by omega)

/-- Every canonical float's key is strictly inside the infinities. -/
theorem key_lt_HUGE {u : UnpackedFloat} (h : Canonical u)
    (hni : ∀ s, u ≠ .infinity s) : key u < HUGE ∧ -HUGE < key u := by
  have h2 : ((2 ^ 2098 : Nat) : Int) = 2 ^ 2098 := by
    rw [Int.natCast_pow]
    rfl
  have hhn : (2 ^ 2098 : Nat) < 2 ^ 6000 := Nat.pow_lt_pow_right (by omega) (by omega)
  have hh : (2 ^ 2098 : Int) < HUGE := by
    rw [HUGE, show ((2 : Int)) = ((2 : Nat) : Int) from rfl, ← Int.natCast_pow,
      ← Int.natCast_pow]
    omega
  have hp : (0 : Int) < HUGE := by
    rw [HUGE, show ((2 : Int)) = ((2 : Nat) : Int) from rfl, ← Int.natCast_pow]
    have := Nat.two_pow_pos 6000
    omega
  cases h with
  | notANumber =>
    simp only [key]
    omega
  | infinity s => exact absurd rfl (hni s)
  | zero s =>
    simp only [key]
    omega
  | subnormal s m hm hlt =>
    have hv := canonical_value_lt (m := m) (e := -1074) (by omega) (by omega)
    cases s <;> simp only [key, Sign.apply] <;>
      rw [show ((2 : Int)) = ((2 : Nat) : Int) from rfl, ← Int.natCast_pow,
        ← Int.natCast_mul] <;>
      omega
  | normal s m e hm hlo hhi helo hehi =>
    have hv := canonical_value_lt (m := m) (e := e) hhi hehi
    cases s <;> simp only [key, Sign.apply] <;>
      rw [show ((2 : Int)) = ((2 : Nat) : Int) from rfl, ← Int.natCast_pow,
        ← Int.natCast_mul] <;>
      omega

/-- Crossing a binade upward crosses every value below it: the canonical
bounds force the higher exponent's mantissa into normal position. -/
theorem canonical_value_lt_of_exp_lt {m₁ m₂ : Nat} {e₁ e₂ : Int}
    (h₁ : m₁ < 2 ^ 53) (hlo₁ : -1074 ≤ e₁)
    (hnorm₂ : 2 ^ 52 ≤ m₂ ∨ e₂ = -1074) (he : e₁ < e₂) :
    m₁ * 2 ^ (e₁ + 1074).toNat < m₂ * 2 ^ (e₂ + 1074).toNat := by
  have hm₂ : 2 ^ 52 ≤ m₂ := by
    rcases hnorm₂ with h | h
    · exact h
    · omega
  calc m₁ * 2 ^ (e₁ + 1074).toNat
      < 2 ^ 53 * 2 ^ (e₁ + 1074).toNat :=
        (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr h₁
    _ = 2 ^ (53 + (e₁ + 1074).toNat) := by rw [Nat.pow_add]
    _ ≤ 2 ^ (52 + (e₂ + 1074).toNat) := Nat.pow_le_pow_right (by omega) (by omega)
    _ = 2 ^ 52 * 2 ^ (e₂ + 1074).toNat := by rw [Nat.pow_add]
    _ ≤ m₂ * 2 ^ (e₂ + 1074).toNat := Nat.mul_le_mul_right _ hm₂

/-- The lexicographic comparison on canonical finite floats is exactly the
comparison of their scaled values. -/
theorem canonical_lex_eq_value {m₁ m₂ : Nat} {e₁ e₂ : Int}
    (h₁ : m₁ < 2 ^ 53) (hlo₁ : -1074 ≤ e₁) (hn₁ : 2 ^ 52 ≤ m₁ ∨ e₁ = -1074)
    (h₂ : m₂ < 2 ^ 53) (hlo₂ : -1074 ≤ e₂) (hn₂ : 2 ^ 52 ≤ m₂ ∨ e₂ = -1074) :
    (compare e₁ e₂).then (compare m₁ m₂)
      = compare (m₁ * 2 ^ (e₁ + 1074).toNat) (m₂ * 2 ^ (e₂ + 1074).toNat) := by
  rcases Int.lt_trichotomy e₁ e₂ with he | he | he
  · rw [Int.compare_eq_lt.mpr he]
    exact (Nat.compare_eq_lt.mpr (canonical_value_lt_of_exp_lt h₁ hlo₁ hn₂ he)).symm
  · subst he
    rw [Int.compare_eq_eq.mpr rfl]
    rcases Nat.lt_trichotomy m₁ m₂ with hm | hm | hm
    · rw [Nat.compare_eq_lt.mpr hm, Nat.compare_eq_lt.mpr
        ((Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr hm)]
      rfl
    · subst hm
      rw [Nat.compare_eq_eq.mpr rfl, Nat.compare_eq_eq.mpr rfl]
      rfl
    · rw [Nat.compare_eq_gt.mpr hm, Nat.compare_eq_gt.mpr
        ((Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr hm)]
      rfl
  · rw [Int.compare_eq_gt.mpr he]
    exact (Nat.compare_eq_gt.mpr (canonical_value_lt_of_exp_lt h₂ hlo₂ hn₁ he)).symm

theorem HUGE_pos : (0 : Int) < HUGE := by
  rw [HUGE, show ((2 : Int)) = ((2 : Nat) : Int) from rfl, ← Int.natCast_pow]
  have := Nat.two_pow_pos 6000
  omega

theorem int_compare_natCast (a b : Nat) :
    compare ((a : Int)) ((b : Int)) = compare a b := by
  rcases Nat.lt_trichotomy a b with h | h | h
  · rw [Nat.compare_eq_lt.mpr h, Int.compare_eq_lt.mpr (by omega)]
  · subst h
    rw [Nat.compare_eq_eq.mpr rfl, Int.compare_eq_eq.mpr rfl]
  · rw [Nat.compare_eq_gt.mpr h, Int.compare_eq_gt.mpr (by omega)]

theorem int_compare_neg (a b : Int) : compare (-a) (-b) = (compare a b).swap := by
  rcases Int.lt_trichotomy a b with h | h | h
  · rw [Int.compare_eq_lt.mpr h, Int.compare_eq_gt.mpr (by omega)]
    rfl
  · subst h
    rw [Int.compare_eq_eq.mpr rfl, Int.compare_eq_eq.mpr rfl]
    rfl
  · rw [Int.compare_eq_gt.mpr h, Int.compare_eq_lt.mpr (by omega)]
    rfl

theorem key_finite_cast (s : Sign) (m : Nat) (e : Int) (h : 0 < m) :
    key (.finite s m e h) = s.apply ((m * 2 ^ (e + 1074).toNat : Nat) : Int) := by
  cases s <;> simp only [key, Sign.apply] <;>
    rw [show ((2 : Int)) = ((2 : Nat) : Int) from rfl, ← Int.natCast_pow,
      ← Int.natCast_mul]

/-- The finite-finite arm: lexicographic comparison equals key comparison,
via the canonical bounds. -/
theorem compare_eq_key_finite {s₁ s₂ : Sign} {m₁ m₂ : Nat} {e₁ e₂ : Int}
    {h₁ : 0 < m₁} {h₂ : 0 < m₂}
    (hm₁ : m₁ < 2 ^ 53) (hlo₁ : -1074 ≤ e₁) (hn₁ : 2 ^ 52 ≤ m₁ ∨ e₁ = -1074)
    (hm₂ : m₂ < 2 ^ 53) (hlo₂ : -1074 ≤ e₂) (hn₂ : 2 ^ 52 ≤ m₂ ∨ e₂ = -1074) :
    UnpackedFloat.compare (.finite s₁ m₁ e₁ h₁) (.finite s₂ m₂ e₂ h₂)
      = some (compare (key (.finite s₁ m₁ e₁ h₁)) (key (.finite s₂ m₂ e₂ h₂))) := by
  have hN₁ : 0 < m₁ * 2 ^ (e₁ + 1074).toNat := Nat.mul_pos h₁ (Nat.two_pow_pos _)
  have hN₂ : 0 < m₂ * 2 ^ (e₂ + 1074).toNat := Nat.mul_pos h₂ (Nat.two_pow_pos _)
  have hlex := canonical_lex_eq_value hm₁ hlo₁ hn₁ hm₂ hlo₂ hn₂
  cases s₁ <;> cases s₂ <;>
    rw [key_finite_cast, key_finite_cast] <;>
    simp only [UnpackedFloat.compare, Sign.apply]
  · rw [int_compare_neg, int_compare_natCast, ← hlex]
  · rw [Int.compare_eq_lt.mpr (by omega)]
  · rw [Int.compare_eq_gt.mpr (by omega)]
  · rw [int_compare_natCast, ← hlex]

/-- On canonical non-NaN floats, IEEE comparison is integer comparison of
keys. -/
theorem compare_eq_key {u v : UnpackedFloat} (hu : Canonical u) (hv : Canonical v)
    (hun : u ≠ .notANumber) (hvn : v ≠ .notANumber) :
    UnpackedFloat.compare u v = some (compare (key u) (key v)) := by
  have hp := HUGE_pos
  cases hu with
  | notANumber => exact absurd rfl hun
  | infinity s =>
    cases hv with
    | notANumber => exact absurd rfl hvn
    | infinity t =>
      cases s <;> cases t <;> simp only [UnpackedFloat.compare, key, Sign.apply]
      · rw [Int.compare_eq_eq.mpr rfl]
        rfl
      · rw [Int.compare_eq_lt.mpr (by omega)]
        rfl
      · rw [Int.compare_eq_gt.mpr (by omega)]
        rfl
      · rw [Int.compare_eq_eq.mpr rfl]
        rfl
    | zero t =>
      have hb := key_lt_HUGE (Canonical.zero t) (fun _ h => UnpackedFloat.noConfusion h)
      cases s <;> simp only [key, Sign.apply] at hb ⊢ <;>
        simp only [UnpackedFloat.compare]
      · rw [Int.compare_eq_lt.mpr hb.2]
      · rw [Int.compare_eq_gt.mpr hb.1]
    | subnormal t m hm hmlt =>
      have hb := key_lt_HUGE (Canonical.subnormal t m hm hmlt)
        (fun _ h => UnpackedFloat.noConfusion h)
      cases s <;> simp only [key, Sign.apply] at hb ⊢ <;>
        simp only [UnpackedFloat.compare]
      · rw [Int.compare_eq_lt.mpr hb.2]
      · rw [Int.compare_eq_gt.mpr hb.1]
    | normal t m e hm hlo hhi helo hehi =>
      have hb := key_lt_HUGE (Canonical.normal t m e hm hlo hhi helo hehi)
        (fun _ h => UnpackedFloat.noConfusion h)
      cases s <;> simp only [key, Sign.apply] at hb ⊢ <;>
        simp only [UnpackedFloat.compare]
      · rw [Int.compare_eq_lt.mpr hb.2]
      · rw [Int.compare_eq_gt.mpr hb.1]
  | zero s =>
    cases hv with
    | notANumber => exact absurd rfl hvn
    | infinity t =>
      have hb := key_lt_HUGE (Canonical.zero s) (fun _ h => UnpackedFloat.noConfusion h)
      cases t <;> simp only [key, Sign.apply] at hb ⊢ <;>
        simp only [UnpackedFloat.compare]
      · rw [Int.compare_eq_gt.mpr hb.2]
      · rw [Int.compare_eq_lt.mpr hb.1]
    | zero t =>
      simp only [UnpackedFloat.compare, key]
      rw [Int.compare_eq_eq.mpr rfl]
    | subnormal t m hm hmlt =>
      have hN : 0 < m * 2 ^ ((-1074 : Int) + 1074).toNat := Nat.mul_pos hm (Nat.two_pow_pos _)
      cases t <;> rw [key_finite_cast] <;>
        simp only [UnpackedFloat.compare, key, Sign.apply]
      · rw [Int.compare_eq_gt.mpr (by omega)]
      · rw [Int.compare_eq_lt.mpr (by omega)]
    | normal t m e hm hlo hhi helo hehi =>
      have hN : 0 < m * 2 ^ (e + 1074).toNat := Nat.mul_pos hm (Nat.two_pow_pos _)
      cases t <;> rw [key_finite_cast] <;>
        simp only [UnpackedFloat.compare, key, Sign.apply]
      · rw [Int.compare_eq_gt.mpr (by omega)]
      · rw [Int.compare_eq_lt.mpr (by omega)]
  | subnormal s m hm hmlt =>
    cases hv with
    | notANumber => exact absurd rfl hvn
    | infinity t =>
      have hb := key_lt_HUGE (Canonical.subnormal s m hm hmlt)
        (fun _ h => UnpackedFloat.noConfusion h)
      cases t <;> simp only [key, Sign.apply] at hb ⊢ <;>
        simp only [UnpackedFloat.compare]
      · rw [Int.compare_eq_gt.mpr hb.2]
      · rw [Int.compare_eq_lt.mpr hb.1]
    | zero t =>
      have hN : 0 < m * 2 ^ ((-1074 : Int) + 1074).toNat := Nat.mul_pos hm (Nat.two_pow_pos _)
      cases s <;> rw [key_finite_cast] <;>
        simp only [UnpackedFloat.compare, key, Sign.apply]
      · rw [Int.compare_eq_lt.mpr (by omega)]
      · rw [Int.compare_eq_gt.mpr (by omega)]
    | subnormal t m' hm' hmlt' =>
      exact compare_eq_key_finite (by omega) (by omega) (Or.inr rfl)
        (by omega) (by omega) (Or.inr rfl)
    | normal t m' e' hm' hlo' hhi' helo' hehi' =>
      exact compare_eq_key_finite (by omega) (by omega) (Or.inr rfl)
        hhi' helo' (Or.inl hlo')
  | normal s m e hm hlo hhi helo hehi =>
    cases hv with
    | notANumber => exact absurd rfl hvn
    | infinity t =>
      have hb := key_lt_HUGE (Canonical.normal s m e hm hlo hhi helo hehi)
        (fun _ h => UnpackedFloat.noConfusion h)
      cases t <;> simp only [key, Sign.apply] at hb ⊢ <;>
        simp only [UnpackedFloat.compare]
      · rw [Int.compare_eq_gt.mpr hb.2]
      · rw [Int.compare_eq_lt.mpr hb.1]
    | zero t =>
      have hN : 0 < m * 2 ^ (e + 1074).toNat := Nat.mul_pos hm (Nat.two_pow_pos _)
      cases s <;> rw [key_finite_cast] <;>
        simp only [UnpackedFloat.compare, key, Sign.apply]
      · rw [Int.compare_eq_lt.mpr (by omega)]
      · rw [Int.compare_eq_gt.mpr (by omega)]
    | subnormal t m' hm' hmlt' =>
      exact compare_eq_key_finite hhi helo (Or.inl hlo)
        (by omega) (by omega) (Or.inr rfl)
    | normal t m' e' hm' hlo' hhi' helo' hehi' =>
      exact compare_eq_key_finite hhi helo (Or.inl hlo)
        hhi' helo' (Or.inl hlo')

/-! ## Crossing pack for rounding outputs -/

/-- What binary64 rounding hands to `pack`: canonical below the overflow
line, or a normal-position mantissa on a too-large exponent. -/
inductive RoundShape : UnpackedFloat → Prop
  | canonical {u : UnpackedFloat} (h : Canonical u) : RoundShape u
  | overflow (s : Sign) (m : Nat) (e : Int) (h : 0 < m)
      (hlo : 2 ^ 52 ≤ m) (hhi : m < 2 ^ 53) (he : 972 ≤ e) (hecap : e ≤ 4000) :
      RoundShape (.finite s m e h)

theorem pow52_lt_53 : (2 : Nat) ^ 52 < 2 ^ 53 := Nat.pow_lt_pow_right (by omega) (by omega)

/-- Assemble a finite `RoundShape` from bounds, without rewriting under the
positivity proof. -/
theorem roundShape_finite_of (s : Sign) (r : Nat) (G : Int) (h : 0 < r)
    (hc : (r < 2 ^ 52 ∧ G = -1074)
      ∨ (2 ^ 52 ≤ r ∧ r < 2 ^ 53 ∧ -1074 ≤ G ∧ G ≤ 971)
      ∨ (2 ^ 52 ≤ r ∧ r < 2 ^ 53 ∧ 972 ≤ G ∧ G ≤ 4000)) : RoundShape (.finite s r G h) := by
  rcases hc with ⟨h1, rfl⟩ | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · exact .canonical (.subnormal s r h h1)
  · exact .canonical (.normal s r G h h1 h2 h3 h4)
  · exact .overflow s r G h h1 h2 h3 h4

/-- Rounding outputs land in `RoundShape`. -/
theorem roundShape_roundWA (s : Sign) (m : Nat) (e : Int) (num den : Nat)
    (hw : WellPlaced m e) (hden : 0 < den) (hnum : num < den)
    (hcap : totalExponent m e ≤ 3900) :
    RoundShape (roundWithAccuracy .binary64 s m e (accuracyOfFraction num den)) := by
  have hG := grid_ge m e
  have hGcap : grid m e ≤ 3847 := by
    simp only [grid, totalExponent] at *
    omega
  have hle := rnShiftF_le m e num den hw
  rw [roundWA_eq s m e num den hw hden hnum]
  by_cases hovf : rnShiftF m ((grid m e - e).toNat) num den = 2 ^ 53
  · rw [if_pos hovf]
    by_cases hbig : grid m e + 1 ≤ 971
    · exact .canonical (.normal s _ _ _ (Nat.le_refl _) pow52_lt_53 (by omega) hbig)
    · exact .overflow s _ _ _ (Nat.le_refl _) pow52_lt_53 (by omega) (by omega)
  · rw [if_neg hovf]
    rcases Nat.eq_zero_or_pos (rnShiftF m ((grid m e - e).toNat) num den) with h0 | h0
    · rw [dif_pos h0]
      exact .canonical (.zero s)
    · rw [dif_neg (Nat.pos_iff_ne_zero.mp h0)]
      have hr53 : rnShiftF m ((grid m e - e).toNat) num den < 2 ^ 53 := by omega
      by_cases hsub : grid m e = -1074
      · rcases Nat.lt_or_ge (rnShiftF m ((grid m e - e).toNat) num den) (2 ^ 52) with hlt | hge
        · exact roundShape_finite_of s _ _ h0 (Or.inl ⟨hlt, hsub⟩)
        · exact .canonical (.normal s _ _ _ hge hr53 (by omega) (by omega))
      · -- Above the floor, the quotient sits in normal position.
        have hlog : 52 ≤ m.log2 ∧ (grid m e - e).toNat = m.log2 - 52 := by
          have hw' := hw
          simp only [WellPlaced, grid, totalExponent] at hw' ⊢
          rcases Nat.eq_zero_or_pos m with hm0 | hm0
          · exfalso
            rw [hm0, show Nat.log2 0 = 0 from rfl] at hw'
            simp only [grid, totalExponent, hm0, show Nat.log2 0 = 0 from rfl] at hsub
            omega
          · simp only [grid, totalExponent] at hsub
            omega
        have hq : 2 ^ 52 ≤ m / 2 ^ (grid m e - e).toNat := by
          rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos _), ← Nat.pow_add]
          have h52 : 52 + (grid m e - e).toNat = m.log2 := by omega
          rw [h52]
          refine Nat.log2_self_le ?_
          intro hm0
          rw [hm0, show Nat.log2 0 = 0 from rfl] at hlog
          omega
        have hge : 2 ^ 52 ≤ rnShiftF m ((grid m e - e).toNat) num den :=
          Nat.le_trans hq (rnShiftF_bounds m _ num den).1
        by_cases hbig : grid m e ≤ 971
        · exact .canonical (.normal s _ _ _ hge hr53 (by omega) hbig)
        · exact .overflow s _ _ _ hge hr53 (by omega) (by omega)

/-- Packing a normal-position mantissa on an exponent past 971 overflows
to infinity. -/
theorem unpack_pack_overflow (s : Sign) (m : Nat) (e : Int) (h : 0 < m)
    (_hlo : 2 ^ 52 ≤ m) (_hhi : m < 2 ^ 53) (he : 972 ≤ e) :
    unpack .binary64 (UnpackedFloat.pack .binary64 (.finite s m e h)) = .infinity s := by
  have hbias : (e + Format.binary64.exponentBias + Format.binary64.mantissaBitsWithoutImplicit).toNat
      = (e + 1075).toNat := by
    show (e + (2 ^ (11 - 1) - 1 : Nat) + (52 : Nat)).toNat = (e + 1075).toNat
    omega
  rw [UnpackedFloat.pack]
  simp only [hbias]
  rw [if_pos (by
    rw [show (2 : Nat) ^ Format.binary64.exponentBits = 2048 from rfl]
    omega : 2 ^ Format.binary64.exponentBits ≤ (e + 1075).toNat + 1)]
  cases s <;> rfl

theorem pow2098_facts : (2 ^ 2098 : Int) < HUGE ∧ ((2 ^ 2098 : Nat) : Int) = 2 ^ 2098 := by
  have h2 : ((2 ^ 2098 : Nat) : Int) = 2 ^ 2098 := by
    rw [Int.natCast_pow]
    rfl
  have hhn : (2 ^ 2098 : Nat) < 2 ^ 6000 := Nat.pow_lt_pow_right (by omega) (by omega)
  refine ⟨?_, h2⟩
  rw [HUGE, show ((2 : Int)) = ((2 : Nat) : Int) from rfl, ← Int.natCast_pow,
    ← Int.natCast_pow]
  omega

/-- An overflowed value's magnitude clears the whole canonical range. -/
theorem overflow_key_ge {m : Nat} {e : Int} (hlo : 2 ^ 52 ≤ m) (he : 972 ≤ e) :
    (2 ^ 2098 : Nat) ≤ m * 2 ^ (e + 1074).toNat := by
  calc (2 ^ 2098 : Nat) = 2 ^ 52 * 2 ^ 2046 := by rw [← Nat.pow_add]
    _ ≤ m * 2 ^ 2046 := Nat.mul_le_mul_right _ hlo
    _ ≤ m * 2 ^ (e + 1074).toNat :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))

/-- A canonical key that is not an infinity stays strictly inside ±2^2098. -/
theorem canonical_key_small {u : UnpackedFloat} (hc : Canonical u)
    (hinf : ∀ t, u ≠ .infinity t) :
    -(2 ^ 2098 : Int) < key u ∧ key u < (2 ^ 2098 : Int) := by
  obtain ⟨hth, hcast⟩ := pow2098_facts
  cases hc with
  | notANumber => simp only [key]; omega
  | infinity t => exact absurd rfl (hinf t)
  | zero t => simp only [key]; omega
  | subnormal t m hm hmlt =>
    have hv2 := canonical_value_lt (m := m) (e := -1074) (by omega) (by omega)
    rw [key_finite_cast]
    cases t <;> simp only [Sign.apply] <;> omega
  | normal t m e hm hlo hhi helo hehi =>
    have hv2 := canonical_value_lt (m := m) (e := e) hhi hehi
    rw [key_finite_cast]
    cases t <;> simp only [Sign.apply] <;> omega

/-- The pack crossing preserves key order: in-range values survive intact,
and overflow collapses to the infinity on the same side of every in-range
key. -/
theorem key_unpack_pack_mono {u v : UnpackedFloat}
    (hu : RoundShape u) (hv : RoundShape v)
    (hun : u ≠ .notANumber) (hvn : v ≠ .notANumber)
    (h : key u ≤ key v) :
    key (unpack .binary64 (UnpackedFloat.pack .binary64 u))
      ≤ key (unpack .binary64 (UnpackedFloat.pack .binary64 v)) := by
  obtain ⟨hth, hcast⟩ := pow2098_facts
  have hp := HUGE_pos
  have hbound : ∀ {w : UnpackedFloat}, Canonical w → -HUGE ≤ key w ∧ key w ≤ HUGE := by
    intro w hw
    by_cases hinf : ∃ t, w = .infinity t
    · obtain ⟨t, rfl⟩ := hinf
      cases t <;> simp only [key, Sign.apply] <;> omega
    · have h1 := key_lt_HUGE hw (fun t ht => hinf ⟨t, ht⟩)
      omega
  cases hu with
  | canonical hcu =>
    rw [unpack_pack_of_canonical hcu]
    cases hv with
    | canonical hcv =>
      rw [unpack_pack_of_canonical hcv]
      exact h
    | overflow t m' e' h' hlo' hhi' he' hecap' =>
      rw [unpack_pack_overflow t m' e' h' hlo' hhi' he']
      have hovN := overflow_key_ge hlo' he'
      cases t
      · -- v overflowed negative: only u = -∞ survives the hypothesis.
        rw [key_finite_cast] at h
        simp only [Sign.apply] at h
        by_cases hinf : ∃ t, u = .infinity t
        · obtain ⟨t, rfl⟩ := hinf
          cases t
          · simp only [key, Sign.apply]
            omega
          · exfalso
            simp only [key, Sign.apply] at h
            omega
        · exfalso
          have hsmall := canonical_key_small hcu (fun t ht => hinf ⟨t, ht⟩)
          omega
      · exact (hbound hcu).2
  | overflow t m' e' h' hlo' hhi' he' hecap' =>
    rw [unpack_pack_overflow t m' e' h' hlo' hhi' he']
    have hovN := overflow_key_ge hlo' he'
    cases t
    · -- u overflowed negative: its packing is -∞, below every packed key.
      cases hv with
      | canonical hcv =>
        rw [unpack_pack_of_canonical hcv]
        have h1 := hbound hcv
        show -HUGE ≤ key v
        omega
      | overflow t₂ m₂ e₂ h₂ hlo₂ hhi₂ he₂ hecap₂ =>
        rw [unpack_pack_overflow t₂ m₂ e₂ h₂ hlo₂ hhi₂ he₂]
        cases t₂ <;> simp only [key, Sign.apply] <;> omega
    · -- u overflowed positive: the hypothesis forces v past the range too.
      rw [key_finite_cast] at h
      simp only [Sign.apply] at h
      cases hv with
      | canonical hcv =>
        by_cases hinf : ∃ t₂, v = .infinity t₂
        · obtain ⟨t₂, rfl⟩ := hinf
          cases t₂
          · exfalso
            simp only [key, Sign.apply] at h
            omega
          · rw [unpack_pack_of_canonical hcv]
            simp only [key, Sign.apply]
            omega
        · exfalso
          have hsmall := canonical_key_small hcv (fun t₂ ht => hinf ⟨t₂, ht⟩)
          omega
      | overflow t₂ m₂ e₂ h₂ hlo₂ hhi₂ he₂ hecap₂ =>
        rw [unpack_pack_overflow t₂ m₂ e₂ h₂ hlo₂ hhi₂ he₂]
        cases t₂
        · exfalso
          rw [key_finite_cast] at h
          simp only [Sign.apply] at h
          omega
        · simp only [key, Sign.apply]
          omega

/-- The pack crossing cannot introduce a NaN. -/
theorem unpack_pack_ne_nan {u : UnpackedFloat} (hu : RoundShape u)
    (hun : u ≠ .notANumber) :
    unpack .binary64 (UnpackedFloat.pack .binary64 u) ≠ .notANumber := by
  cases hu with
  | canonical hc =>
    rw [unpack_pack_of_canonical hc]
    exact hun
  | overflow s m e h hlo hhi he hecap =>
    rw [unpack_pack_overflow s m e h hlo hhi he]
    exact fun hcon => UnpackedFloat.noConfusion hcon

/-! ## The operations, keyed

Each operation on canonical inputs produces a `RoundShape`, never a NaN
(under the finiteness side conditions), and its key is monotone. `mul`
rounds the exact product; `add` and `sub` go through `round`, whose
exponent-decreasing pre-shift restores the rounding contract; `div`
rounds the exact quotient with a remainder-derived accuracy. -/

/-! ## `round` and `normalize`

`round` (used by `add`/`sub` through `normalize`) first shifts the
mantissa down to the grid exactly, which restores the rounding contract
for any input; everything proven about `roundWithAccuracy` then applies. -/

theorem log2_mul_pow {m : Nat} (hm : 0 < m) (k : Nat) :
    (m * 2 ^ k).log2 = m.log2 + k := by
  have hne : m * 2 ^ k ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (Nat.mul_pos hm (Nat.two_pow_pos k))
  have h1 : 2 ^ (m.log2 + k) ≤ m * 2 ^ k := by
    rw [Nat.pow_add]
    exact Nat.mul_le_mul_right _ (Nat.log2_self_le (by omega))
  have h2 : m * 2 ^ k < 2 ^ (m.log2 + k + 1) := by
    have he : m.log2 + k + 1 = m.log2 + 1 + k := by omega
    rw [he, Nat.pow_add]
    exact (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr Nat.lt_log2_self
  have hle := (Nat.le_log2 hne).mpr h1
  have hlt := (Nat.log2_lt hne).mpr h2
  omega

/-- `round`, definitionally, as the pre-shift feeding `roundWithAccuracy`. -/
theorem round_unfold (spec : Format) (s : Sign) (m : Nat) (e : Int) :
    UnpackedFloat.round spec s m e =
      roundWithAccuracy spec s
        (m <<< (e - spec.targetExponent (totalExponent m e)).toNat)
        (e - ((e - spec.targetExponent (totalExponent m e)).toNat : Int)) .exact := rfl

theorem round_eq_roundWA (s : Sign) (m : Nat) (e : Int) :
    UnpackedFloat.round .binary64 s m e =
      roundWithAccuracy .binary64 s (m * 2 ^ (e - grid m e).toNat)
        (e - ((e - grid m e).toNat : Int)) (accuracyOfFraction 0 1) := by
  rw [round_unfold, Nat.shiftLeft_eq,
    show accuracyOfFraction 0 1 = Accuracy.exact from rfl]
  simp only [targetExponent_binary64, grid]

/-- The pre-shifted input satisfies the rounding contract. -/
theorem wellPlaced_round_input {m : Nat} (hm : 0 < m) (e : Int) :
    WellPlaced (m * 2 ^ (e - grid m e).toNat) (e - ((e - grid m e).toNat : Int)) := by
  simp only [WellPlaced, grid, totalExponent]
  rw [log2_mul_pow hm]
  omega

theorem natCast_mul_intPow_nonneg (a b : Nat) : (0 : Int) ≤ (a : Int) * 2 ^ b := by
  have h1 : ((a * 2 ^ b : Nat) : Int) = (a : Int) * 2 ^ b := by
    rw [Int.natCast_mul, Int.natCast_pow]
    rfl
  omega

theorem key_round_pos_nonneg (m : Nat) (hm : 0 < m) (E : Int) :
    0 ≤ key (UnpackedFloat.round .binary64 .positive m E) := by
  rw [round_eq_roundWA, key_roundWA_pos _ _ 0 1 (wellPlaced_round_input hm E)
    Nat.one_pos Nat.zero_lt_one]
  exact natCast_mul_intPow_nonneg _ _

theorem key_round_neg (m : Nat) (hm : 0 < m) (E : Int) :
    key (UnpackedFloat.round .binary64 .negative m E)
      = -key (UnpackedFloat.round .binary64 .positive m E) := by
  rw [round_eq_roundWA, round_eq_roundWA]
  exact key_roundWA_neg _ _ 0 1 (wellPlaced_round_input hm E) Nat.one_pos Nat.zero_lt_one

/-- Monotonicity of positive `round` on scaled values. -/
theorem key_round_pos_mono {m₁ m₂ : Nat} {E₁ E₂ : Int} (h₁ : 0 < m₁) (h₂ : 0 < m₂)
    (h : m₁ * 2 ^ (E₁ - min E₁ E₂).toNat ≤ m₂ * 2 ^ (E₂ - min E₁ E₂).toNat) :
    key (UnpackedFloat.round .binary64 .positive m₁ E₁)
      ≤ key (UnpackedFloat.round .binary64 .positive m₂ E₂) := by
  rw [round_eq_roundWA, round_eq_roundWA]
  apply key_roundWA_mono Nat.one_pos Nat.zero_lt_one Nat.zero_lt_one
    (wellPlaced_round_input h₁ E₁) (wellPlaced_round_input h₂ E₂)
  simp only [Nat.mul_one, Nat.add_zero]
  -- Exponent bookkeeping: both sides re-express the original scaled values
  -- at the finer common exponent.
  have hexp₁ : (E₁ - grid m₁ E₁).toNat
        + ((E₁ - ((E₁ - grid m₁ E₁).toNat : Int))
          - min (E₁ - ((E₁ - grid m₁ E₁).toNat : Int))
                (E₂ - ((E₂ - grid m₂ E₂).toNat : Int))).toNat
      = (E₁ - min E₁ E₂).toNat
        + (min E₁ E₂ - min (E₁ - ((E₁ - grid m₁ E₁).toNat : Int))
            (E₂ - ((E₂ - grid m₂ E₂).toNat : Int))).toNat := by
    omega
  have hexp₂ : (E₂ - grid m₂ E₂).toNat
        + ((E₂ - ((E₂ - grid m₂ E₂).toNat : Int))
          - min (E₁ - ((E₁ - grid m₁ E₁).toNat : Int))
                (E₂ - ((E₂ - grid m₂ E₂).toNat : Int))).toNat
      = (E₂ - min E₁ E₂).toNat
        + (min E₁ E₂ - min (E₁ - ((E₁ - grid m₁ E₁).toNat : Int))
            (E₂ - ((E₂ - grid m₂ E₂).toNat : Int))).toNat := by
    omega
  have hstep := Nat.mul_le_mul_right
    (2 ^ (min E₁ E₂ - min (E₁ - ((E₁ - grid m₁ E₁).toNat : Int))
      (E₂ - ((E₂ - grid m₂ E₂).toNat : Int))).toNat) h
  calc m₁ * 2 ^ (E₁ - grid m₁ E₁).toNat
        * 2 ^ ((E₁ - ((E₁ - grid m₁ E₁).toNat : Int))
            - min (E₁ - ((E₁ - grid m₁ E₁).toNat : Int))
              (E₂ - ((E₂ - grid m₂ E₂).toNat : Int))).toNat
      = m₁ * 2 ^ (E₁ - min E₁ E₂).toNat
        * 2 ^ (min E₁ E₂ - min (E₁ - ((E₁ - grid m₁ E₁).toNat : Int))
            (E₂ - ((E₂ - grid m₂ E₂).toNat : Int))).toNat := by
        rw [Nat.mul_assoc, Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add, hexp₁]
    _ ≤ m₂ * 2 ^ (E₂ - min E₁ E₂).toNat
        * 2 ^ (min E₁ E₂ - min (E₁ - ((E₁ - grid m₁ E₁).toNat : Int))
            (E₂ - ((E₂ - grid m₂ E₂).toNat : Int))).toNat := hstep
    _ = m₂ * 2 ^ (E₂ - grid m₂ E₂).toNat
        * 2 ^ ((E₂ - ((E₂ - grid m₂ E₂).toNat : Int))
            - min (E₁ - ((E₁ - grid m₁ E₁).toNat : Int))
              (E₂ - ((E₂ - grid m₂ E₂).toNat : Int))).toNat := by
        rw [Nat.mul_assoc, Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add, hexp₂]

/-! ## `normalize`: the signed entry point `add` and `sub` use -/

theorem normalize_eq_of_neg {M : Int} (E : Int) (z : Sign) (h : M < 0) :
    UnpackedFloat.normalize .binary64 M E z
      = UnpackedFloat.round .binary64 .negative (-M).toNat E := by
  simp only [UnpackedFloat.normalize, Int.compare_eq_lt.mpr h]

theorem normalize_eq_of_zero (E : Int) (z : Sign) :
    UnpackedFloat.normalize .binary64 0 E z = .zero z := by
  simp only [UnpackedFloat.normalize, Int.compare_eq_eq.mpr rfl]

theorem normalize_eq_of_pos {M : Int} (E : Int) (z : Sign) (h : 0 < M) :
    UnpackedFloat.normalize .binary64 M E z
      = UnpackedFloat.round .binary64 .positive M.toNat E := by
  simp only [UnpackedFloat.normalize, Int.compare_eq_gt.mpr h]

theorem intPow_pos (x : Nat) : (0 : Int) < 2 ^ x := by
  rw [show ((2 : Int)) = ((2 : Nat) : Int) from rfl, ← Int.natCast_pow]
  have := Nat.two_pow_pos x
  omega

theorem int_mul_pow_neg {M : Int} (x : Nat) (h : M < 0) : M * 2 ^ x < 0 := by
  have hp := intPow_pos x
  have h1 : M * 2 ^ x ≤ -1 * 2 ^ x :=
    Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
  omega

theorem int_mul_pow_pos {M : Int} (x : Nat) (h : 0 < M) : 0 < M * 2 ^ x := by
  have hp := intPow_pos x
  have h1 : 1 * 2 ^ x ≤ M * 2 ^ x :=
    Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
  omega

theorem toNat_value_cast {M : Int} (x : Nat) (h : 0 ≤ M) :
    ((M.toNat * 2 ^ x : Nat) : Int) = M * 2 ^ x := by
  rw [Int.natCast_mul, Int.natCast_pow, Int.toNat_of_nonneg h]
  rfl

/-- Monotonicity of `normalize` on scaled signed values. -/
theorem key_normalize_mono {M₁ M₂ E₁ E₂ : Int} (z₁ z₂ : Sign)
    (h : M₁ * 2 ^ (E₁ - min E₁ E₂).toNat ≤ M₂ * 2 ^ (E₂ - min E₁ E₂).toNat) :
    key (UnpackedFloat.normalize .binary64 M₁ E₁ z₁)
      ≤ key (UnpackedFloat.normalize .binary64 M₂ E₂ z₂) := by
  rcases Int.lt_trichotomy M₁ 0 with hM₁ | hM₁ | hM₁
  · rcases Int.lt_trichotomy M₂ 0 with hM₂ | hM₂ | hM₂
    · -- both negative: mirror of the positive case
      rw [normalize_eq_of_neg E₁ z₁ hM₁, normalize_eq_of_neg E₂ z₂ hM₂,
        key_round_neg _ (by omega) _, key_round_neg _ (by omega) _]
      have hmono : key (UnpackedFloat.round .binary64 .positive (-M₂).toNat E₂)
          ≤ key (UnpackedFloat.round .binary64 .positive (-M₁).toNat E₁) := by
        apply key_round_pos_mono (by omega) (by omega)
        rw [Int.min_comm E₂ E₁]
        have hc₁ := toNat_value_cast (M := -M₁) ((E₁ - min E₁ E₂).toNat) (by omega)
        have hc₂ := toNat_value_cast (M := -M₂) ((E₂ - min E₁ E₂).toNat) (by omega)
        have hneg₁ : (-M₁) * 2 ^ (E₁ - min E₁ E₂).toNat = -(M₁ * 2 ^ (E₁ - min E₁ E₂).toNat) := by
          rw [Int.neg_mul]
        have hneg₂ : (-M₂) * 2 ^ (E₂ - min E₁ E₂).toNat = -(M₂ * 2 ^ (E₂ - min E₁ E₂).toNat) := by
          rw [Int.neg_mul]
        omega
      omega
    · subst hM₂
      rw [normalize_eq_of_neg E₁ z₁ hM₁, normalize_eq_of_zero E₂ z₂,
        key_round_neg _ (by omega) _]
      have := key_round_pos_nonneg (-M₁).toNat (by omega) E₁
      have hz : key (UnpackedFloat.zero z₂) = 0 := rfl
      omega
    · rw [normalize_eq_of_neg E₁ z₁ hM₁, normalize_eq_of_pos E₂ z₂ hM₂,
        key_round_neg _ (by omega) _]
      have h1 := key_round_pos_nonneg (-M₁).toNat (by omega) E₁
      have h2 := key_round_pos_nonneg M₂.toNat (by omega) E₂
      omega
  · subst hM₁
    rcases Int.lt_trichotomy M₂ 0 with hM₂ | hM₂ | hM₂
    · exfalso
      have := int_mul_pow_neg (M := M₂) ((E₂ - min E₁ E₂).toNat) hM₂
      have h0 : (0 : Int) * 2 ^ (E₁ - min E₁ E₂).toNat = 0 := Int.zero_mul _
      omega
    · subst hM₂
      rw [normalize_eq_of_zero E₁ z₁, normalize_eq_of_zero E₂ z₂]
      have hz₁ : key (UnpackedFloat.zero z₁) = 0 := rfl
      have hz₂ : key (UnpackedFloat.zero z₂) = 0 := rfl
      omega
    · rw [normalize_eq_of_zero E₁ z₁, normalize_eq_of_pos E₂ z₂ hM₂]
      have := key_round_pos_nonneg M₂.toNat (by omega) E₂
      have hz : key (UnpackedFloat.zero z₁) = 0 := rfl
      omega
  · rcases Int.lt_trichotomy M₂ 0 with hM₂ | hM₂ | hM₂
    · exfalso
      have h1 := int_mul_pow_neg (M := M₂) ((E₂ - min E₁ E₂).toNat) hM₂
      have h2 := int_mul_pow_pos (M := M₁) ((E₁ - min E₁ E₂).toNat) hM₁
      omega
    · exfalso
      subst hM₂
      have h2 := int_mul_pow_pos (M := M₁) ((E₁ - min E₁ E₂).toNat) hM₁
      have h0 : (0 : Int) * 2 ^ (E₂ - min E₁ E₂).toNat = 0 := Int.zero_mul _
      omega
    · rw [normalize_eq_of_pos E₁ z₁ hM₁, normalize_eq_of_pos E₂ z₂ hM₂]
      apply key_round_pos_mono (by omega) (by omega)
      have hc₁ := toNat_value_cast (M := M₁) ((E₁ - min E₁ E₂).toNat) (by omega)
      have hc₂ := toNat_value_cast (M := M₂) ((E₂ - min E₁ E₂).toNat) (by omega)
      omega

/-- Rounding never produces a NaN. -/
theorem roundWA_ne_nan (s : Sign) (m : Nat) (e : Int) (num den : Nat)
    (hw : WellPlaced m e) (hden : 0 < den) (hnum : num < den) :
    roundWithAccuracy .binary64 s m e (accuracyOfFraction num den) ≠ .notANumber := by
  rw [roundWA_eq s m e num den hw hden hnum]
  by_cases hovf : rnShiftF m ((grid m e - e).toNat) num den = 2 ^ 53
  · rw [if_pos hovf]
    exact fun hc => UnpackedFloat.noConfusion hc
  · rw [if_neg hovf]
    rcases Nat.eq_zero_or_pos (rnShiftF m ((grid m e - e).toNat) num den) with h0 | h0
    · rw [dif_pos h0]
      exact fun hc => UnpackedFloat.noConfusion hc
    · rw [dif_neg (Nat.pos_iff_ne_zero.mp h0)]
      exact fun hc => UnpackedFloat.noConfusion hc

theorem round_shape (s : Sign) {m : Nat} (hm : 0 < m) (E : Int)
    (hcap : totalExponent m E ≤ 3900) :
    RoundShape (UnpackedFloat.round .binary64 s m E)
      ∧ UnpackedFloat.round .binary64 s m E ≠ .notANumber := by
  rw [round_eq_roundWA]
  have hcap' : totalExponent (m * 2 ^ (E - grid m E).toNat)
      (E - ((E - grid m E).toNat : Int)) ≤ 3900 := by
    simp only [totalExponent] at hcap ⊢
    rw [log2_mul_pow hm]
    omega
  exact ⟨roundShape_roundWA _ _ _ 0 1 (wellPlaced_round_input hm E)
      Nat.one_pos Nat.zero_lt_one hcap',
    roundWA_ne_nan _ _ _ 0 1 (wellPlaced_round_input hm E) Nat.one_pos Nat.zero_lt_one⟩

theorem normalize_shape (M E : Int) (z : Sign)
    (hcap : totalExponent M.natAbs E ≤ 3900) :
    RoundShape (UnpackedFloat.normalize .binary64 M E z)
      ∧ UnpackedFloat.normalize .binary64 M E z ≠ .notANumber := by
  rcases Int.lt_trichotomy M 0 with hM | hM | hM
  · rw [normalize_eq_of_neg E z hM]
    have habs : (-M).toNat = M.natAbs := by omega
    rw [habs]
    exact round_shape _ (by omega) E hcap
  · subst hM
    rw [normalize_eq_of_zero E z]
    exact ⟨.canonical (.zero z), fun hc => UnpackedFloat.noConfusion hc⟩
  · rw [normalize_eq_of_pos E z hM]
    have habs : M.toNat = M.natAbs := by omega
    rw [habs]
    exact round_shape _ (by omega) E hcap

/-- Keys of round shapes stay weakly inside the infinities: the overflow
exponent cap keeps even overflowed magnitudes below `HUGE`. -/
theorem roundShape_key_bounds {w : UnpackedFloat} (hw : RoundShape w)
    (hn : w ≠ .notANumber) : -HUGE ≤ key w ∧ key w ≤ HUGE := by
  have hp := HUGE_pos
  cases hw with
  | canonical hc =>
    by_cases hinf : ∃ t, w = .infinity t
    · obtain ⟨t, rfl⟩ := hinf
      cases t <;> simp only [key, Sign.apply] <;> omega
    · have h1 := key_lt_HUGE hc (fun t ht => hinf ⟨t, ht⟩)
      omega
  | overflow t m e h hlo hhi he hecap =>
    have hv : m * 2 ^ (e + 1074).toNat < 2 ^ 5127 := by
      calc m * 2 ^ (e + 1074).toNat
          < 2 ^ 53 * 2 ^ (e + 1074).toNat :=
            (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr hhi
        _ = 2 ^ (53 + (e + 1074).toNat) := by rw [Nat.pow_add]
        _ ≤ 2 ^ 5127 := Nat.pow_le_pow_right (by omega) (by omega)
    have hhg : ((2 ^ 5127 : Nat) : Int) < HUGE := by
      have h2 : ((2 ^ 5127 : Nat) : Int) = 2 ^ 5127 := by
        rw [Int.natCast_pow]
        rfl
      have hhn : (2 ^ 5127 : Nat) < 2 ^ 6000 := Nat.pow_lt_pow_right (by omega) (by omega)
      rw [HUGE, show ((2 : Int)) = ((2 : Nat) : Int) from rfl, ← Int.natCast_pow]
      omega
    rw [key_finite_cast]
    cases t <;> simp only [Sign.apply] <;> omega

/-! ## Multiplication by a positive finite constant -/

theorem log2_mono {a b : Nat} (h : a ≤ b) : a.log2 ≤ b.log2 := by
  rcases Nat.eq_zero_or_pos a with h0 | h0
  · rw [h0, show Nat.log2 0 = 0 from rfl]
    omega
  · exact (Nat.le_log2 (by omega)).mpr (Nat.le_trans (Nat.log2_self_le (by omega)) h)

theorem log2_mul_le {a b : Nat} (ha : 0 < a) (hb : 0 < b) :
    (a * b).log2 ≤ a.log2 + b.log2 + 1 := by
  have h1 : a * b < 2 ^ (a.log2 + 1) * 2 ^ (b.log2 + 1) := by
    have hx := Nat.lt_log2_self (n := a)
    have hy := Nat.lt_log2_self (n := b)
    calc a * b ≤ a * (2 ^ (b.log2 + 1) - 1) := Nat.mul_le_mul_left _ (by omega)
      _ < 2 ^ (a.log2 + 1) * 2 ^ (b.log2 + 1) := by
          have := Nat.mul_lt_mul_of_lt_of_le hx
            (Nat.le_refl (2 ^ (b.log2 + 1) - 1)) (by have := Nat.two_pow_pos (b.log2 + 1); omega)
          have h2 : 2 ^ (a.log2 + 1) * (2 ^ (b.log2 + 1) - 1)
              < 2 ^ (a.log2 + 1) * 2 ^ (b.log2 + 1) :=
            Nat.mul_lt_mul_left (Nat.two_pow_pos _) |>.mpr (by have := Nat.two_pow_pos (b.log2 + 1); omega)
          omega
  rw [← Nat.pow_add] at h1
  have := (Nat.log2_lt (Nat.pos_iff_ne_zero.mp (Nat.mul_pos ha hb))).mpr h1
  omega

/-- The exact product of two canonically-bounded mantissas is well-placed. -/
theorem mul_wellPlaced {m mc : Nat} {e ec : Int} (hm : 0 < m) (hmc : 0 < mc)
    (hn₁ : 2 ^ 52 ≤ m ∨ e = -1074) (hn₂ : 2 ^ 52 ≤ mc ∨ ec = -1074) :
    WellPlaced (m * mc) (e + ec) := by
  simp only [WellPlaced, grid, totalExponent]
  have hcase : 2 ^ 52 ≤ m * mc ∨ (e = -1074 ∧ ec = -1074) := by
    rcases hn₁ with h1 | h1
    · exact Or.inl (Nat.le_trans h1 (Nat.le_mul_of_pos_right m hmc))
    · rcases hn₂ with h2 | h2
      · exact Or.inl (Nat.le_trans h2 (Nat.le_mul_of_pos_left mc hm))
      · exact Or.inr ⟨h1, h2⟩
  rcases hcase with h | ⟨h1, h2⟩
  · have hl := (Nat.le_log2 (by omega)).mpr h
    omega
  · omega

/-- `mul` against a positive finite constant: the shape of the result. -/
theorem mul_shape {u : UnpackedFloat} (hu : Canonical u) (hun : u ≠ .notANumber)
    {mc : Nat} {ec : Int} {hc : 0 < mc}
    (hmc : mc < 2 ^ 53) (hloc : -1074 ≤ ec) (hhic : ec ≤ 971)
    (hnc : 2 ^ 52 ≤ mc ∨ ec = -1074) :
    RoundShape (UnpackedFloat.mul .binary64 u (.finite .positive mc ec hc))
      ∧ UnpackedFloat.mul .binary64 u (.finite .positive mc ec hc) ≠ .notANumber := by
  cases hu with
  | notANumber => exact absurd rfl hun
  | infinity s =>
    exact ⟨.canonical (.infinity _), fun hcon => UnpackedFloat.noConfusion hcon⟩
  | zero s =>
    exact ⟨.canonical (.zero _), fun hcon => UnpackedFloat.noConfusion hcon⟩
  | subnormal s m hm hmlt =>
    show RoundShape (roundWithAccuracy .binary64 (s * .positive) (m * mc) (-1074 + ec) .exact) ∧ _
    rw [show Accuracy.exact = accuracyOfFraction 0 1 from rfl]
    have hw := mul_wellPlaced (e := -1074) hm hc (Or.inr rfl) hnc
    have hcap : totalExponent (m * mc) (-1074 + ec) ≤ 3900 := by
      have h1 := log2_mul_le hm hc
      have h2 : m.log2 ≤ 52 := by
        have := (Nat.log2_lt (by omega)).mpr (Nat.lt_trans hmlt pow52_lt_53)
        omega
      have h3 : mc.log2 ≤ 52 := by
        have := (Nat.log2_lt (by omega)).mpr hmc
        omega
      simp only [totalExponent]
      omega
    exact ⟨roundShape_roundWA _ _ _ 0 1 hw Nat.one_pos Nat.zero_lt_one hcap,
      roundWA_ne_nan _ _ _ 0 1 hw Nat.one_pos Nat.zero_lt_one⟩
  | normal s m e hm hlo hhi helo hehi =>
    show RoundShape (roundWithAccuracy .binary64 (s * .positive) (m * mc) (e + ec) .exact) ∧ _
    rw [show Accuracy.exact = accuracyOfFraction 0 1 from rfl]
    have hw := mul_wellPlaced (e := e) hm hc (Or.inl hlo) hnc
    have hcap : totalExponent (m * mc) (e + ec) ≤ 3900 := by
      have h1 := log2_mul_le hm hc
      have h2 : m.log2 ≤ 52 := by
        have := (Nat.log2_lt (by omega)).mpr hhi
        omega
      have h3 : mc.log2 ≤ 52 := by
        have := (Nat.log2_lt (by omega)).mpr hmc
        omega
      simp only [totalExponent]
      omega
    exact ⟨roundShape_roundWA _ _ _ 0 1 hw Nat.one_pos Nat.zero_lt_one hcap,
      roundWA_ne_nan _ _ _ 0 1 hw Nat.one_pos Nat.zero_lt_one⟩

/-- Transfer key order (values scaled to the subnormal quantum) to values
scaled to the common exponent. -/
theorem key_order_scaled {m₁ m₂ : Nat} {e₁ e₂ : Int}
    (hlo₁ : -1074 ≤ e₁) (hlo₂ : -1074 ≤ e₂)
    (h : m₁ * 2 ^ (e₁ + 1074).toNat ≤ m₂ * 2 ^ (e₂ + 1074).toNat) :
    m₁ * 2 ^ (e₁ - min e₁ e₂).toNat ≤ m₂ * 2 ^ (e₂ - min e₁ e₂).toNat := by
  have hx₁ : (e₁ + 1074).toNat = (e₁ - min e₁ e₂).toNat + (min e₁ e₂ + 1074).toNat := by
    omega
  have hx₂ : (e₂ + 1074).toNat = (e₂ - min e₁ e₂).toNat + (min e₁ e₂ + 1074).toNat := by
    omega
  rw [hx₁, hx₂, Nat.pow_add, Nat.pow_add, ← Nat.mul_assoc, ← Nat.mul_assoc] at h
  exact Nat.le_of_mul_le_mul_right h (Nat.two_pow_pos _)

/-- The scaled-value hypothesis `key_roundWA_mono` wants for the exact
products entering `mul`'s rounding. -/
theorem mul_value_hyp {ma mb mc : Nat} {ea eb ec : Int}
    (hlo₁ : -1074 ≤ ea) (hlo₂ : -1074 ≤ eb)
    (h : ma * 2 ^ (ea + 1074).toNat ≤ mb * 2 ^ (eb + 1074).toNat) :
    (ma * mc * 1 + 0) * 2 ^ (ea + ec - min (ea + ec) (eb + ec)).toNat
      ≤ (mb * mc * 1 + 0) * 2 ^ (eb + ec - min (ea + ec) (eb + ec)).toNat := by
  have hs := key_order_scaled hlo₁ hlo₂ h
  have hmul := Nat.mul_le_mul_right mc hs
  have hE₁ : (ea + ec - min (ea + ec) (eb + ec)).toNat = (ea - min ea eb).toNat := by omega
  have hE₂ : (eb + ec - min (ea + ec) (eb + ec)).toNat = (eb - min ea eb).toNat := by omega
  rw [hE₁, hE₂]
  calc (ma * mc * 1 + 0) * 2 ^ (ea - min ea eb).toNat
      = ma * 2 ^ (ea - min ea eb).toNat * mc := by grind
    _ ≤ mb * 2 ^ (eb - min ea eb).toNat * mc := hmul
    _ = (mb * mc * 1 + 0) * 2 ^ (eb - min ea eb).toNat := by grind

/-- `mul` monotonicity, finite against finite. -/
theorem key_mul_mono_finite {sa sb : Sign} {ma mb : Nat} {ea eb : Int}
    {hma : 0 < ma} {hmb : 0 < mb} {mc : Nat} {ec : Int} {hc : 0 < mc}
    (_hhia : ma < 2 ^ 53) (hloa : -1074 ≤ ea) (hna : 2 ^ 52 ≤ ma ∨ ea = -1074)
    (_hhib : mb < 2 ^ 53) (hlob : -1074 ≤ eb) (hnb : 2 ^ 52 ≤ mb ∨ eb = -1074)
    (hnc : 2 ^ 52 ≤ mc ∨ ec = -1074)
    (h : key (.finite sa ma ea hma) ≤ key (.finite sb mb eb hmb)) :
    key (UnpackedFloat.mul .binary64 (.finite sa ma ea hma) (.finite .positive mc ec hc))
      ≤ key (UnpackedFloat.mul .binary64 (.finite sb mb eb hmb) (.finite .positive mc ec hc)) := by
  have hwa := mul_wellPlaced (e := ea) hma hc hna hnc
  have hwb := mul_wellPlaced (e := eb) hmb hc hnb hnc
  have hNa : 0 < ma * 2 ^ (ea + 1074).toNat := Nat.mul_pos hma (Nat.two_pow_pos _)
  have hNb : 0 < mb * 2 ^ (eb + 1074).toNat := Nat.mul_pos hmb (Nat.two_pow_pos _)
  rw [key_finite_cast, key_finite_cast] at h
  cases sa <;> cases sb <;> simp only [Sign.apply] at h
  · -- negative, negative
    show key (roundWithAccuracy .binary64 .negative (ma * mc) (ea + ec)
        (accuracyOfFraction 0 1)) ≤ key (roundWithAccuracy .binary64 .negative (mb * mc)
        (eb + ec) (accuracyOfFraction 0 1))
    rw [key_roundWA_neg _ _ 0 1 hwa Nat.one_pos Nat.zero_lt_one,
      key_roundWA_neg _ _ 0 1 hwb Nat.one_pos Nat.zero_lt_one]
    have hmono := key_roundWA_mono (den := 1) Nat.one_pos Nat.zero_lt_one Nat.zero_lt_one
      hwb hwa (mul_value_hyp (mc := mc) (ec := ec) hlob hloa (by omega))
    omega
  · -- negative, positive
    show key (roundWithAccuracy .binary64 .negative (ma * mc) (ea + ec)
        (accuracyOfFraction 0 1)) ≤ key (roundWithAccuracy .binary64 .positive (mb * mc)
        (eb + ec) (accuracyOfFraction 0 1))
    rw [key_roundWA_neg _ _ 0 1 hwa Nat.one_pos Nat.zero_lt_one,
      key_roundWA_pos _ _ 0 1 hwa Nat.one_pos Nat.zero_lt_one,
      key_roundWA_pos _ _ 0 1 hwb Nat.one_pos Nat.zero_lt_one]
    have h1 := natCast_mul_intPow_nonneg
      (rnShiftF (ma * mc) ((grid (ma * mc) (ea + ec) - (ea + ec)).toNat) 0 1)
      ((grid (ma * mc) (ea + ec) + 1074).toNat)
    have h2 := natCast_mul_intPow_nonneg
      (rnShiftF (mb * mc) ((grid (mb * mc) (eb + ec) - (eb + ec)).toNat) 0 1)
      ((grid (mb * mc) (eb + ec) + 1074).toNat)
    omega
  · -- positive, negative: impossible
    exfalso
    omega
  · -- positive, positive
    show key (roundWithAccuracy .binary64 .positive (ma * mc) (ea + ec)
        (accuracyOfFraction 0 1)) ≤ key (roundWithAccuracy .binary64 .positive (mb * mc)
        (eb + ec) (accuracyOfFraction 0 1))
    exact key_roundWA_mono Nat.one_pos Nat.zero_lt_one Nat.zero_lt_one hwa hwb
      (mul_value_hyp (mc := mc) (ec := ec) hloa hlob (by omega))

/-- `mul` against a positive finite constant is key-monotone on canonical
non-NaN inputs. -/
theorem key_mul_mono {a b : UnpackedFloat} (ha : Canonical a) (hb : Canonical b)
    (han : a ≠ .notANumber) (hbn : b ≠ .notANumber)
    {mc : Nat} {ec : Int} {hc : 0 < mc}
    (hmc : mc < 2 ^ 53) (hloc : -1074 ≤ ec) (hhic : ec ≤ 971)
    (hnc : 2 ^ 52 ≤ mc ∨ ec = -1074)
    (h : key a ≤ key b) :
    key (UnpackedFloat.mul .binary64 a (.finite .positive mc ec hc))
      ≤ key (UnpackedFloat.mul .binary64 b (.finite .positive mc ec hc)) := by
  have hp := HUGE_pos
  obtain ⟨hth, hcast⟩ := pow2098_facts
  cases ha with
  | notANumber => exact absurd rfl han
  | infinity s =>
    cases s
    · -- a = -∞: the product is -∞, below every round shape.
      have hsh := mul_shape (hc := hc) hb hbn hmc hloc hhic hnc
      exact (roundShape_key_bounds hsh.1 hsh.2).1
    · -- a = +∞: only b = +∞ satisfies the hypothesis.
      by_cases hinf : ∃ t, b = .infinity t
      · obtain ⟨t, rfl⟩ := hinf
        cases t
        · exfalso
          have h' : HUGE ≤ -HUGE := h
          omega
        · exact Int.le_refl _
      · exfalso
        have hsmall := canonical_key_small hb (fun t ht => hinf ⟨t, ht⟩)
        have h' : HUGE ≤ key b := h
        omega
  | zero s =>
    cases hb with
    | notANumber => exact absurd rfl hbn
    | infinity t =>
      cases t
      · exfalso
        simp only [key, Sign.apply] at h
        omega
      · show (0 : Int) ≤ HUGE
        omega
    | zero t => exact Int.le_refl _
    | subnormal t m hm hmlt =>
      cases t
      · exfalso
        rw [key_finite_cast] at h
        simp only [key, Sign.apply] at h
        have := Nat.mul_pos hm (Nat.two_pow_pos ((-1074 : Int) + 1074).toNat)
        omega
      · show (0 : Int) ≤ key (roundWithAccuracy .binary64 .positive (m * mc) (-1074 + ec)
          (accuracyOfFraction 0 1))
        rw [key_roundWA_pos _ _ 0 1 (mul_wellPlaced (e := -1074) hm hc (Or.inr rfl) hnc)
          Nat.one_pos Nat.zero_lt_one]
        exact natCast_mul_intPow_nonneg _ _
    | normal t m e hm hlo hhi helo hehi =>
      cases t
      · exfalso
        rw [key_finite_cast] at h
        simp only [key, Sign.apply] at h
        have := Nat.mul_pos hm (Nat.two_pow_pos (e + 1074).toNat)
        omega
      · show (0 : Int) ≤ key (roundWithAccuracy .binary64 .positive (m * mc) (e + ec)
          (accuracyOfFraction 0 1))
        rw [key_roundWA_pos _ _ 0 1 (mul_wellPlaced (e := e) hm hc (Or.inl hlo) hnc)
          Nat.one_pos Nat.zero_lt_one]
        exact natCast_mul_intPow_nonneg _ _
  | subnormal s m hm hmlt =>
    have hcanA : Canonical (.finite s m (-1074 : Int) hm) := .subnormal s m hm hmlt
    cases hb with
    | notANumber => exact absurd rfl hbn
    | infinity t =>
      cases t
      · exfalso
        have hsmall := canonical_key_small hcanA (fun t ht => UnpackedFloat.noConfusion ht)
        have h' : key _ ≤ -HUGE := h
        omega
      · have hsh := mul_shape (hc := hc) hcanA (fun hcon => UnpackedFloat.noConfusion hcon)
          hmc hloc hhic hnc
        exact (roundShape_key_bounds hsh.1 hsh.2).2
    | zero t =>
      cases s
      · show key (roundWithAccuracy .binary64 .negative (m * mc) (-1074 + ec)
            (accuracyOfFraction 0 1)) ≤ (0 : Int)
        have hw := mul_wellPlaced (e := -1074) hm hc (Or.inr rfl) hnc
        rw [key_roundWA_neg _ _ 0 1 hw Nat.one_pos Nat.zero_lt_one,
          key_roundWA_pos _ _ 0 1 hw Nat.one_pos Nat.zero_lt_one]
        have := natCast_mul_intPow_nonneg
          (rnShiftF (m * mc) ((grid (m * mc) (-1074 + ec) - (-1074 + ec)).toNat) 0 1)
          ((grid (m * mc) (-1074 + ec) + 1074).toNat)
        omega
      · exfalso
        rw [key_finite_cast] at h
        simp only [key, Sign.apply] at h
        have := Nat.mul_pos hm (Nat.two_pow_pos ((-1074 : Int) + 1074).toNat)
        omega
    | subnormal t m' hm' hmlt' =>
      exact key_mul_mono_finite (by omega) (by omega) (Or.inr rfl)
        (by omega) (by omega) (Or.inr rfl) hnc h
    | normal t m' e' hm' hlo' hhi' helo' hehi' =>
      exact key_mul_mono_finite (by omega) (by omega) (Or.inr rfl)
        hhi' helo' (Or.inl hlo') hnc h
  | normal s m e hm hlo hhi helo hehi =>
    have hcanA : Canonical (.finite s m e hm) := .normal s m e hm hlo hhi helo hehi
    cases hb with
    | notANumber => exact absurd rfl hbn
    | infinity t =>
      cases t
      · exfalso
        have hsmall := canonical_key_small hcanA (fun t ht => UnpackedFloat.noConfusion ht)
        have h' : key _ ≤ -HUGE := h
        omega
      · have hsh := mul_shape (hc := hc) hcanA (fun hcon => UnpackedFloat.noConfusion hcon)
          hmc hloc hhic hnc
        exact (roundShape_key_bounds hsh.1 hsh.2).2
    | zero t =>
      cases s
      · show key (roundWithAccuracy .binary64 .negative (m * mc) (e + ec)
            (accuracyOfFraction 0 1)) ≤ (0 : Int)
        have hw := mul_wellPlaced (e := e) hm hc (Or.inl hlo) hnc
        rw [key_roundWA_neg _ _ 0 1 hw Nat.one_pos Nat.zero_lt_one,
          key_roundWA_pos _ _ 0 1 hw Nat.one_pos Nat.zero_lt_one]
        have := natCast_mul_intPow_nonneg
          (rnShiftF (m * mc) ((grid (m * mc) (e + ec) - (e + ec)).toNat) 0 1)
          ((grid (m * mc) (e + ec) + 1074).toNat)
        omega
      · exfalso
        rw [key_finite_cast] at h
        simp only [key, Sign.apply] at h
        have := Nat.mul_pos hm (Nat.two_pow_pos (e + 1074).toNat)
        omega
    | subnormal t m' hm' hmlt' =>
      exact key_mul_mono_finite hhi helo (Or.inl hlo)
        (by omega) (by omega) (Or.inr rfl) hnc h
    | normal t m' e' hm' hlo' hhi' helo' hehi' =>
      exact key_mul_mono_finite hhi helo (Or.inl hlo)
        hhi' helo' (Or.inl hlo') hnc h

/-! ## Division by a positive finite constant -/

/-- The exponent `divCore` rounds at. -/
def divT (m₁ : Nat) (e₁ : Int) (m₂ : Nat) (e₂ : Int) : Int :=
  min (e₁ - e₂)
    (Format.binary64.targetExponent (totalExponent m₁ e₁ - totalExponent m₂ e₂))

/-- The widened dividend `divCore` divides. -/
def divM (m₁ : Nat) (e₁ : Int) (m₂ : Nat) (e₂ : Int) : Nat :=
  m₁ <<< (e₁ - e₂ - divT m₁ e₁ m₂ e₂).toNat

theorem div_finite_unfold (s₁ : Sign) (m₁ : Nat) (e₁ : Int) (h₁ : 0 < m₁)
    (s₂ : Sign) (m₂ : Nat) (e₂ : Int) (h₂ : 0 < m₂) :
    UnpackedFloat.div .binary64 (.finite s₁ m₁ e₁ h₁) (.finite s₂ m₂ e₂ h₂)
      = roundWithAccuracy .binary64 (s₁ / s₂) (divM m₁ e₁ m₂ e₂ / m₂)
          (divT m₁ e₁ m₂ e₂)
          (accuracyOfFraction (divM m₁ e₁ m₂ e₂ % m₂) m₂) := rfl

theorem divT_le (m₁ : Nat) (e₁ : Int) (m₂ : Nat) (e₂ : Int) :
    divT m₁ e₁ m₂ e₂ ≤ e₁ - e₂
    ∧ divT m₁ e₁ m₂ e₂
        ≤ max (totalExponent m₁ e₁ - totalExponent m₂ e₂ - 53) (-1074) := by
  constructor
  · exact Int.min_le_left _ _
  · rw [divT, targetExponent_binary64]
    exact Int.min_le_right _ _

theorem divM_eq (m₁ : Nat) (e₁ : Int) (m₂ : Nat) (e₂ : Int) :
    divM m₁ e₁ m₂ e₂ = m₁ * 2 ^ (e₁ - e₂ - divT m₁ e₁ m₂ e₂).toNat := by
  rw [divM, Nat.shiftLeft_eq]

/-- The division quotient is presented at an exponent the rounding
contract accepts: past the subnormal floor it carries at least 53
significant bits. -/
theorem div_wellPlaced {m₁ m₂ : Nat} {e₁ e₂ : Int} (h₁ : 0 < m₁) (h₂ : 0 < m₂)
    (_hm₂ : m₂ < 2 ^ 53) :
    WellPlaced (divM m₁ e₁ m₂ e₂ / m₂) (divT m₁ e₁ m₂ e₂) := by
  obtain ⟨hT₁, hT₂⟩ := divT_le m₁ e₁ m₂ e₂
  by_cases hfloor : divT m₁ e₁ m₂ e₂ ≤ -1074
  · have := grid_ge (divM m₁ e₁ m₂ e₂ / m₂) (divT m₁ e₁ m₂ e₂)
    simp only [WellPlaced]
    omega
  · -- Above the floor the target came from the 53-bit budget, which
    -- forces the quotient into normal position.
    have hd : divT m₁ e₁ m₂ e₂ ≤ totalExponent m₁ e₁ - totalExponent m₂ e₂ - 53 := by
      omega
    have hs : ((e₁ - e₂ - divT m₁ e₁ m₂ e₂).toNat : Int) = e₁ - e₂ - divT m₁ e₁ m₂ e₂ := by
      omega
    have hsge : 53 + m₂.log2 ≤ m₁.log2 + (e₁ - e₂ - divT m₁ e₁ m₂ e₂).toNat := by
      simp only [totalExponent] at hd
      omega
    have hMlow : 2 ^ (m₁.log2 + (e₁ - e₂ - divT m₁ e₁ m₂ e₂).toNat) ≤ divM m₁ e₁ m₂ e₂ := by
      rw [divM_eq, Nat.pow_add]
      exact Nat.mul_le_mul_right _ (Nat.log2_self_le (by omega))
    have hq : 2 ^ 52 ≤ divM m₁ e₁ m₂ e₂ / m₂ := by
      have hstep1 : divM m₁ e₁ m₂ e₂ / 2 ^ (m₂.log2 + 1) ≤ divM m₁ e₁ m₂ e₂ / m₂ :=
        Nat.div_le_div_left (Nat.le_of_lt Nat.lt_log2_self) h₂
      have hstep2 : 2 ^ (m₁.log2 + (e₁ - e₂ - divT m₁ e₁ m₂ e₂).toNat) / 2 ^ (m₂.log2 + 1)
          ≤ divM m₁ e₁ m₂ e₂ / 2 ^ (m₂.log2 + 1) :=
        Nat.div_le_div_right hMlow
      have hstep3 : 2 ^ (m₁.log2 + (e₁ - e₂ - divT m₁ e₁ m₂ e₂).toNat) / 2 ^ (m₂.log2 + 1)
          = 2 ^ (m₁.log2 + (e₁ - e₂ - divT m₁ e₁ m₂ e₂).toNat - (m₂.log2 + 1)) :=
        Nat.pow_div (by omega) (by omega)
      have hstep4 : 2 ^ 52
          ≤ 2 ^ (m₁.log2 + (e₁ - e₂ - divT m₁ e₁ m₂ e₂).toNat - (m₂.log2 + 1)) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      omega
    have hlog := (Nat.le_log2 (by omega)).mpr hq
    simp only [WellPlaced, grid, totalExponent]
    omega

theorem div_cap {m₁ m₂ : Nat} {e₁ e₂ : Int} (h₁ : 0 < m₁) (_h₂ : 0 < m₂)
    (hm₁ : m₁ < 2 ^ 53) (he₁ : e₁ ≤ 971) (he₂ : -1074 ≤ e₂) :
    totalExponent (divM m₁ e₁ m₂ e₂ / m₂) (divT m₁ e₁ m₂ e₂) ≤ 3900 := by
  obtain ⟨hT₁, _⟩ := divT_le m₁ e₁ m₂ e₂
  have hql : (divM m₁ e₁ m₂ e₂ / m₂).log2 ≤ (divM m₁ e₁ m₂ e₂).log2 :=
    log2_mono (Nat.div_le_self _ _)
  have hMl : (divM m₁ e₁ m₂ e₂).log2
      = m₁.log2 + (e₁ - e₂ - divT m₁ e₁ m₂ e₂).toNat := by
    rw [divM_eq]
    exact log2_mul_pow h₁ _
  have hl₁ : m₁.log2 ≤ 52 := by
    have := (Nat.log2_lt (by omega)).mpr hm₁
    omega
  simp only [totalExponent] at hT₁ ⊢
  omega

/-- `div` by a positive finite constant: the shape of the result. -/
theorem div_shape {u : UnpackedFloat} (hu : Canonical u) (hun : u ≠ .notANumber)
    {mc : Nat} {ec : Int} {hc : 0 < mc}
    (hmc : mc < 2 ^ 53) (hloc : -1074 ≤ ec) (_hhic : ec ≤ 971) :
    RoundShape (UnpackedFloat.div .binary64 u (.finite .positive mc ec hc))
      ∧ UnpackedFloat.div .binary64 u (.finite .positive mc ec hc) ≠ .notANumber := by
  cases hu with
  | notANumber => exact absurd rfl hun
  | infinity s =>
    exact ⟨.canonical (.infinity _), fun hcon => UnpackedFloat.noConfusion hcon⟩
  | zero s =>
    exact ⟨.canonical (.zero _), fun hcon => UnpackedFloat.noConfusion hcon⟩
  | subnormal s m hm hmlt =>
    rw [div_finite_unfold]
    have hw := div_wellPlaced (e₁ := -1074) (e₂ := ec) hm hc hmc
    have hcap := div_cap (e₁ := -1074) (e₂ := ec) hm hc (by omega) (by omega) hloc
    exact ⟨roundShape_roundWA _ _ _ _ _ hw hc (Nat.mod_lt _ hc) hcap,
      roundWA_ne_nan _ _ _ _ _ hw hc (Nat.mod_lt _ hc)⟩
  | normal s m e hm hlo hhi helo hehi =>
    rw [div_finite_unfold]
    have hw := div_wellPlaced (e₁ := e) (e₂ := ec) hm hc hmc
    have hcap := div_cap (e₁ := e) (e₂ := ec) hm hc hhi hehi hloc
    exact ⟨roundShape_roundWA _ _ _ _ _ hw hc (Nat.mod_lt _ hc) hcap,
      roundWA_ne_nan _ _ _ _ _ hw hc (Nat.mod_lt _ hc)⟩

/-- The scaled-value hypothesis for `div`'s rounding inputs. -/
theorem div_value_hyp {ma mb mc : Nat} {ea eb ec : Int}
    (_hma : 0 < ma) (_hmb : 0 < mb) (_hmc : 0 < mc)
    (hloa : -1074 ≤ ea) (hlob : -1074 ≤ eb)
    (h : ma * 2 ^ (ea + 1074).toNat ≤ mb * 2 ^ (eb + 1074).toNat) :
    (divM ma ea mc ec / mc * mc + divM ma ea mc ec % mc)
        * 2 ^ (divT ma ea mc ec - min (divT ma ea mc ec) (divT mb eb mc ec)).toNat
      ≤ (divM mb eb mc ec / mc * mc + divM mb eb mc ec % mc)
        * 2 ^ (divT mb eb mc ec - min (divT ma ea mc ec) (divT mb eb mc ec)).toNat := by
  have hda : divM ma ea mc ec / mc * mc + divM ma ea mc ec % mc = divM ma ea mc ec := by
    have := Nat.div_add_mod (divM ma ea mc ec) mc
    grind
  have hdb : divM mb eb mc ec / mc * mc + divM mb eb mc ec % mc = divM mb eb mc ec := by
    have := Nat.div_add_mod (divM mb eb mc ec) mc
    grind
  rw [hda, hdb, divM_eq, divM_eq]
  obtain ⟨hTa, _⟩ := divT_le ma ea mc ec
  obtain ⟨hTb, _⟩ := divT_le mb eb mc ec
  have hs := key_order_scaled hloa hlob h
  have hmul := Nat.mul_le_mul_right
    (2 ^ (min ea eb - ec - min (divT ma ea mc ec) (divT mb eb mc ec)).toNat) hs
  have hxa : (ea - ec - divT ma ea mc ec).toNat
        + (divT ma ea mc ec - min (divT ma ea mc ec) (divT mb eb mc ec)).toNat
      = (ea - min ea eb).toNat
        + (min ea eb - ec - min (divT ma ea mc ec) (divT mb eb mc ec)).toNat := by
    omega
  have hxb : (eb - ec - divT mb eb mc ec).toNat
        + (divT mb eb mc ec - min (divT ma ea mc ec) (divT mb eb mc ec)).toNat
      = (eb - min ea eb).toNat
        + (min ea eb - ec - min (divT ma ea mc ec) (divT mb eb mc ec)).toNat := by
    omega
  calc ma * 2 ^ (ea - ec - divT ma ea mc ec).toNat
        * 2 ^ (divT ma ea mc ec - min (divT ma ea mc ec) (divT mb eb mc ec)).toNat
      = ma * 2 ^ (ea - min ea eb).toNat
        * 2 ^ (min ea eb - ec - min (divT ma ea mc ec) (divT mb eb mc ec)).toNat := by
        rw [Nat.mul_assoc, Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add, hxa]
    _ ≤ mb * 2 ^ (eb - min ea eb).toNat
        * 2 ^ (min ea eb - ec - min (divT ma ea mc ec) (divT mb eb mc ec)).toNat := hmul
    _ = mb * 2 ^ (eb - ec - divT mb eb mc ec).toNat
        * 2 ^ (divT mb eb mc ec - min (divT ma ea mc ec) (divT mb eb mc ec)).toNat := by
        rw [Nat.mul_assoc, Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add, hxb]

/-- `div` monotonicity, finite against finite. -/
theorem key_div_mono_finite {sa sb : Sign} {ma mb : Nat} {ea eb : Int}
    {hma : 0 < ma} {hmb : 0 < mb} {mc : Nat} {ec : Int} {hc : 0 < mc}
    (hloa : -1074 ≤ ea) (hlob : -1074 ≤ eb) (hmc : mc < 2 ^ 53)
    (h : key (.finite sa ma ea hma) ≤ key (.finite sb mb eb hmb)) :
    key (UnpackedFloat.div .binary64 (.finite sa ma ea hma) (.finite .positive mc ec hc))
      ≤ key (UnpackedFloat.div .binary64 (.finite sb mb eb hmb) (.finite .positive mc ec hc)) := by
  rw [div_finite_unfold, div_finite_unfold]
  have hwa := div_wellPlaced (e₁ := ea) (e₂ := ec) hma hc hmc
  have hwb := div_wellPlaced (e₁ := eb) (e₂ := ec) hmb hc hmc
  have hNa : 0 < ma * 2 ^ (ea + 1074).toNat := Nat.mul_pos hma (Nat.two_pow_pos _)
  have hNb : 0 < mb * 2 ^ (eb + 1074).toNat := Nat.mul_pos hmb (Nat.two_pow_pos _)
  rw [key_finite_cast, key_finite_cast] at h
  cases sa <;> cases sb <;> simp only [Sign.apply] at h
  · show key (roundWithAccuracy .binary64 .negative (divM ma ea mc ec / mc)
        (divT ma ea mc ec) (accuracyOfFraction (divM ma ea mc ec % mc) mc))
      ≤ key (roundWithAccuracy .binary64 .negative (divM mb eb mc ec / mc)
        (divT mb eb mc ec) (accuracyOfFraction (divM mb eb mc ec % mc) mc))
    rw [key_roundWA_neg _ _ _ _ hwa hc (Nat.mod_lt _ hc),
      key_roundWA_neg _ _ _ _ hwb hc (Nat.mod_lt _ hc)]
    have hmono := key_roundWA_mono hc (Nat.mod_lt _ hc) (Nat.mod_lt _ hc)
      hwb hwa (div_value_hyp (ec := ec) hmb hma hc hlob hloa (by omega))
    omega
  · show key (roundWithAccuracy .binary64 .negative (divM ma ea mc ec / mc)
        (divT ma ea mc ec) (accuracyOfFraction (divM ma ea mc ec % mc) mc))
      ≤ key (roundWithAccuracy .binary64 .positive (divM mb eb mc ec / mc)
        (divT mb eb mc ec) (accuracyOfFraction (divM mb eb mc ec % mc) mc))
    rw [key_roundWA_neg _ _ _ _ hwa hc (Nat.mod_lt _ hc),
      key_roundWA_pos _ _ _ _ hwa hc (Nat.mod_lt _ hc),
      key_roundWA_pos _ _ _ _ hwb hc (Nat.mod_lt _ hc)]
    have h1 := natCast_mul_intPow_nonneg
      (rnShiftF (divM ma ea mc ec / mc)
        ((grid (divM ma ea mc ec / mc) (divT ma ea mc ec) - divT ma ea mc ec).toNat)
        (divM ma ea mc ec % mc) mc)
      ((grid (divM ma ea mc ec / mc) (divT ma ea mc ec) + 1074).toNat)
    have h2 := natCast_mul_intPow_nonneg
      (rnShiftF (divM mb eb mc ec / mc)
        ((grid (divM mb eb mc ec / mc) (divT mb eb mc ec) - divT mb eb mc ec).toNat)
        (divM mb eb mc ec % mc) mc)
      ((grid (divM mb eb mc ec / mc) (divT mb eb mc ec) + 1074).toNat)
    omega
  · exfalso
    omega
  · show key (roundWithAccuracy .binary64 .positive (divM ma ea mc ec / mc)
        (divT ma ea mc ec) (accuracyOfFraction (divM ma ea mc ec % mc) mc))
      ≤ key (roundWithAccuracy .binary64 .positive (divM mb eb mc ec / mc)
        (divT mb eb mc ec) (accuracyOfFraction (divM mb eb mc ec % mc) mc))
    exact key_roundWA_mono hc (Nat.mod_lt _ hc) (Nat.mod_lt _ hc) hwa hwb
      (div_value_hyp (ec := ec) hma hmb hc hloa hlob (by omega))

/-- `div` by a positive finite constant is key-monotone on canonical
non-NaN inputs. -/
theorem key_div_mono {a b : UnpackedFloat} (ha : Canonical a) (hb : Canonical b)
    (han : a ≠ .notANumber) (hbn : b ≠ .notANumber)
    {mc : Nat} {ec : Int} {hc : 0 < mc}
    (hmc : mc < 2 ^ 53) (hloc : -1074 ≤ ec) (hhic : ec ≤ 971)
    (h : key a ≤ key b) :
    key (UnpackedFloat.div .binary64 a (.finite .positive mc ec hc))
      ≤ key (UnpackedFloat.div .binary64 b (.finite .positive mc ec hc)) := by
  have hp := HUGE_pos
  obtain ⟨hth, hcast⟩ := pow2098_facts
  cases ha with
  | notANumber => exact absurd rfl han
  | infinity s =>
    cases s
    · have hsh := div_shape (hc := hc) hb hbn hmc hloc hhic
      exact (roundShape_key_bounds hsh.1 hsh.2).1
    · by_cases hinf : ∃ t, b = .infinity t
      · obtain ⟨t, rfl⟩ := hinf
        cases t
        · exfalso
          have h' : HUGE ≤ -HUGE := h
          omega
        · exact Int.le_refl _
      · exfalso
        have hsmall := canonical_key_small hb (fun t ht => hinf ⟨t, ht⟩)
        have h' : HUGE ≤ key b := h
        omega
  | zero s =>
    cases hb with
    | notANumber => exact absurd rfl hbn
    | infinity t =>
      cases t
      · exfalso
        have h' : (0 : Int) ≤ -HUGE := h
        omega
      · show (0 : Int) ≤ HUGE
        omega
    | zero t => exact Int.le_refl _
    | subnormal t m hm hmlt =>
      cases t
      · exfalso
        rw [key_finite_cast] at h
        simp only [key, Sign.apply] at h
        have := Nat.mul_pos hm (Nat.two_pow_pos ((-1074 : Int) + 1074).toNat)
        omega
      · rw [div_finite_unfold]
        show (0 : Int) ≤ key (roundWithAccuracy .binary64 .positive
          (divM m (-1074) mc ec / mc) (divT m (-1074) mc ec)
          (accuracyOfFraction (divM m (-1074) mc ec % mc) mc))
        rw [key_roundWA_pos _ _ _ _ (div_wellPlaced (e₁ := -1074) (e₂ := ec) hm hc hmc)
          hc (Nat.mod_lt _ hc)]
        exact natCast_mul_intPow_nonneg _ _
    | normal t m e hm hlo hhi helo hehi =>
      cases t
      · exfalso
        rw [key_finite_cast] at h
        simp only [key, Sign.apply] at h
        have := Nat.mul_pos hm (Nat.two_pow_pos (e + 1074).toNat)
        omega
      · rw [div_finite_unfold]
        show (0 : Int) ≤ key (roundWithAccuracy .binary64 .positive
          (divM m e mc ec / mc) (divT m e mc ec)
          (accuracyOfFraction (divM m e mc ec % mc) mc))
        rw [key_roundWA_pos _ _ _ _ (div_wellPlaced (e₁ := e) (e₂ := ec) hm hc hmc)
          hc (Nat.mod_lt _ hc)]
        exact natCast_mul_intPow_nonneg _ _
  | subnormal s m hm hmlt =>
    have hcanA : Canonical (.finite s m (-1074 : Int) hm) := .subnormal s m hm hmlt
    cases hb with
    | notANumber => exact absurd rfl hbn
    | infinity t =>
      cases t
      · exfalso
        have hsmall := canonical_key_small hcanA (fun t ht => UnpackedFloat.noConfusion ht)
        have h' : key _ ≤ -HUGE := h
        omega
      · have hsh := div_shape (hc := hc) hcanA (fun hcon => UnpackedFloat.noConfusion hcon)
          hmc hloc hhic
        exact (roundShape_key_bounds hsh.1 hsh.2).2
    | zero t =>
      cases s
      · rw [div_finite_unfold]
        show key (roundWithAccuracy .binary64 .negative
            (divM m (-1074) mc ec / mc) (divT m (-1074) mc ec)
            (accuracyOfFraction (divM m (-1074) mc ec % mc) mc)) ≤ (0 : Int)
        have hw := div_wellPlaced (e₁ := -1074) (e₂ := ec) hm hc hmc
        rw [key_roundWA_neg _ _ _ _ hw hc (Nat.mod_lt _ hc),
          key_roundWA_pos _ _ _ _ hw hc (Nat.mod_lt _ hc)]
        have := natCast_mul_intPow_nonneg
          (rnShiftF (divM m (-1074) mc ec / mc)
            ((grid (divM m (-1074) mc ec / mc) (divT m (-1074) mc ec)
              - divT m (-1074) mc ec).toNat)
            (divM m (-1074) mc ec % mc) mc)
          ((grid (divM m (-1074) mc ec / mc) (divT m (-1074) mc ec) + 1074).toNat)
        omega
      · exfalso
        rw [key_finite_cast] at h
        simp only [key, Sign.apply] at h
        have := Nat.mul_pos hm (Nat.two_pow_pos ((-1074 : Int) + 1074).toNat)
        omega
    | subnormal t m' hm' hmlt' =>
      exact key_div_mono_finite (by omega) (by omega) hmc h
    | normal t m' e' hm' hlo' hhi' helo' hehi' =>
      exact key_div_mono_finite (by omega) helo' hmc h
  | normal s m e hm hlo hhi helo hehi =>
    have hcanA : Canonical (.finite s m e hm) := .normal s m e hm hlo hhi helo hehi
    cases hb with
    | notANumber => exact absurd rfl hbn
    | infinity t =>
      cases t
      · exfalso
        have hsmall := canonical_key_small hcanA (fun t ht => UnpackedFloat.noConfusion ht)
        have h' : key _ ≤ -HUGE := h
        omega
      · have hsh := div_shape (hc := hc) hcanA (fun hcon => UnpackedFloat.noConfusion hcon)
          hmc hloc hhic
        exact (roundShape_key_bounds hsh.1 hsh.2).2
    | zero t =>
      cases s
      · rw [div_finite_unfold]
        show key (roundWithAccuracy .binary64 .negative
            (divM m e mc ec / mc) (divT m e mc ec)
            (accuracyOfFraction (divM m e mc ec % mc) mc)) ≤ (0 : Int)
        have hw := div_wellPlaced (e₁ := e) (e₂ := ec) hm hc hmc
        rw [key_roundWA_neg _ _ _ _ hw hc (Nat.mod_lt _ hc),
          key_roundWA_pos _ _ _ _ hw hc (Nat.mod_lt _ hc)]
        have := natCast_mul_intPow_nonneg
          (rnShiftF (divM m e mc ec / mc)
            ((grid (divM m e mc ec / mc) (divT m e mc ec) - divT m e mc ec).toNat)
            (divM m e mc ec % mc) mc)
          ((grid (divM m e mc ec / mc) (divT m e mc ec) + 1074).toNat)
        omega
      · exfalso
        rw [key_finite_cast] at h
        simp only [key, Sign.apply] at h
        have := Nat.mul_pos hm (Nat.two_pow_pos (e + 1074).toNat)
        omega
    | subnormal t m' hm' hmlt' =>
      exact key_div_mono_finite helo (by omega) hmc h
    | normal t m' e' hm' hlo' hhi' helo' hehi' =>
      exact key_div_mono_finite helo helo' hmc h

/-! ## Addition of a finite (or zero) constant -/

theorem sign_apply_mul (s : Sign) (n k : Int) : s.apply n * k = s.apply (n * k) := by
  cases s <;> simp only [Sign.apply]
  rw [Int.neg_mul]

theorem sign_apply_natAbs (s : Sign) (n : Int) : (s.apply n).natAbs = n.natAbs := by
  cases s <;> simp only [Sign.apply]
  omega

theorem int_pow_split (u v : Nat) : (2 : Int) ^ (u + v) = 2 ^ u * 2 ^ v := by
  have h1 : (2 : Int) ^ (u + v) = ((2 ^ (u + v) : Nat) : Int) := by
    rw [Int.natCast_pow]
    rfl
  have h2 : (2 : Int) ^ u = ((2 ^ u : Nat) : Int) := by
    rw [Int.natCast_pow]
    rfl
  have h3 : (2 : Int) ^ v = ((2 ^ v : Nat) : Int) := by
    rw [Int.natCast_pow]
    rfl
  rw [h1, h2, h3, ← Int.natCast_mul, Nat.pow_add]

/-- Cancel a positive power on the right of an `Int` inequality. -/
theorem int_le_cancel_pow {A B : Int} (v : Nat) (h : A * 2 ^ v ≤ B * 2 ^ v) : A ≤ B := by
  have hp := intPow_pos v
  rcases Int.lt_or_le B A with hlt | hle
  · exfalso
    have h1 : (B + 1) * 2 ^ v ≤ A * 2 ^ v :=
      Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
    have h2 : (B + 1) * 2 ^ v = B * 2 ^ v + 2 ^ v := by
      rw [Int.add_mul]
      omega
    omega
  · exact hle

/-- `add`, finite against finite, definitionally: the aligned signed sum
handed to `normalize`. -/
theorem add_finite_unfold (s₁ : Sign) (m₁ : Nat) (e₁ : Int) (h₁ : 0 < m₁)
    (s₂ : Sign) (m₂ : Nat) (e₂ : Int) (h₂ : 0 < m₂) :
    UnpackedFloat.add .binary64 (.finite s₁ m₁ e₁ h₁) (.finite s₂ m₂ e₂ h₂)
      = UnpackedFloat.normalize .binary64
          (s₁.apply (m₁ <<< (e₁ - min e₁ e₂).toNat)
            + s₂.apply (m₂ <<< (e₂ - min e₁ e₂).toNat))
          (min e₁ e₂) .positive := rfl

/-- The aligned sum's scaled value is the sum of the operands' keys. -/
theorem add_key_value (s₁ : Sign) (m₁ : Nat) (e₁ : Int) (h₁ : 0 < m₁)
    (s₂ : Sign) (m₂ : Nat) (e₂ : Int) (h₂ : 0 < m₂)
    (hlo₁ : -1074 ≤ e₁) (hlo₂ : -1074 ≤ e₂) :
    (s₁.apply (m₁ <<< (e₁ - min e₁ e₂).toNat)
        + s₂.apply (m₂ <<< (e₂ - min e₁ e₂).toNat)) * 2 ^ (min e₁ e₂ + 1074).toNat
      = key (.finite s₁ m₁ e₁ h₁) + key (.finite s₂ m₂ e₂ h₂) := by
  rw [key_finite_cast, key_finite_cast, Int.add_mul, sign_apply_mul, sign_apply_mul,
    Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  have h1 : (2 : Int) ^ (min e₁ e₂ + 1074).toNat
      = ((2 ^ (min e₁ e₂ + 1074).toNat : Nat) : Int) := by
    rw [Int.natCast_pow]
    rfl
  congr 2
  · rw [h1, ← Int.natCast_mul, Nat.mul_assoc, ← Nat.pow_add]
    have he : (e₁ - min e₁ e₂).toNat + (min e₁ e₂ + 1074).toNat = (e₁ + 1074).toNat := by
      omega
    rw [he]
  · rw [h1, ← Int.natCast_mul, Nat.mul_assoc, ← Nat.pow_add]
    have he : (e₂ - min e₁ e₂).toNat + (min e₁ e₂ + 1074).toNat = (e₂ + 1074).toNat := by
      omega
    rw [he]

/-- A canonical finite float sits exactly on its own grid. -/
theorem grid_canonical {s : Sign} {m : Nat} {e : Int} {h : 0 < m}
    (hcan : Canonical (.finite s m e h)) : grid m e = e := by
  cases hcan with
  | subnormal s m hm hmlt =>
    have hl : m.log2 ≤ 51 := by
      have h52 : m < 2 ^ 52 := hmlt
      have := (Nat.log2_lt (by omega)).mpr h52
      omega
    simp only [grid, totalExponent]
    omega
  | normal s m e hm hlo hhi helo hehi =>
    have hl : m.log2 = 52 := by
      have h1 := (Nat.le_log2 (by omega)).mpr hlo
      have h2 := (Nat.log2_lt (by omega)).mpr hhi
      omega
    simp only [grid, totalExponent]
    omega

/-- Rounding a canonical value returns it unchanged. -/
theorem round_canonical_self {s : Sign} {m : Nat} {e : Int} {h : 0 < m}
    (hcan : Canonical (.finite s m e h)) :
    UnpackedFloat.round .binary64 s m e = .finite s m e h := by
  obtain ⟨hhi, hlo, _, _⟩ := canonical_finite_bounds hcan
  have hg := grid_canonical hcan
  have h0 : (e - grid m e).toNat = 0 := by omega
  rw [round_eq_roundWA, h0]
  simp only [Nat.pow_zero, Nat.mul_one, Int.natCast_zero, Int.sub_zero]
  rw [roundWA_eq _ _ _ _ _ (by simp only [WellPlaced]; omega) Nat.one_pos Nat.zero_lt_one]
  have hr : rnShiftF m 0 0 1 = m := by
    have hlt : (m % 2 ^ 0 * 1 + 0) * 2 < 2 ^ 0 * 1 := by
      simp [Nat.mod_one]
    rw [rnShiftF_of_lt hlt]
    simp
  have h0' : (grid m e - e).toNat = 0 := by omega
  have hr' : rnShiftF m ((grid m e - e).toNat) 0 1 = m := by
    rw [h0']
    exact hr
  simp only [hr']
  rw [if_neg (by omega), dif_neg (by omega)]
  simp only [hg]

/-- `normalize` applied to a canonical value's own aligned form returns it. -/
theorem normalize_canonical_self {sc : Sign} {mc : Nat} {ec : Int} {hc : 0 < mc}
    (hcan : Canonical (.finite sc mc ec hc)) :
    UnpackedFloat.normalize .binary64 (sc.apply mc) ec .positive = .finite sc mc ec hc := by
  cases sc with
  | negative =>
    have hM : Sign.apply .negative (mc : Int) < 0 := by
      simp only [Sign.apply]
      omega
    rw [normalize_eq_of_neg _ _ hM]
    have ht : (-Sign.apply .negative (mc : Int)).toNat = mc := by
      simp only [Sign.apply]
      omega
    rw [ht]
    exact round_canonical_self hcan
  | positive =>
    have hM : 0 < Sign.apply .positive (mc : Int) := by
      simp only [Sign.apply]
      omega
    rw [normalize_eq_of_pos _ _ hM]
    have ht : (Sign.apply .positive (mc : Int)).toNat = mc := by
      simp only [Sign.apply]
      omega
    rw [ht]
    exact round_canonical_self hcan

set_option exponentiation.threshold 2200 in
/-- The aligned sum stays under the exponent cap `normalize_shape` needs. -/
theorem add_cap {m₁ m₂ : Nat} {e₁ e₂ : Int} (s₁ s₂ : Sign)
    (hm₁ : m₁ < 2 ^ 53) (hm₂ : m₂ < 2 ^ 53)
    (hlo₁ : -1074 ≤ e₁) (hhi₁ : e₁ ≤ 971) (hlo₂ : -1074 ≤ e₂) (hhi₂ : e₂ ≤ 971) :
    totalExponent (s₁.apply (m₁ <<< (e₁ - min e₁ e₂).toNat)
        + s₂.apply (m₂ <<< (e₂ - min e₁ e₂).toNat)).natAbs (min e₁ e₂) ≤ 3900 := by
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  have hA : m₁ * 2 ^ (e₁ - min e₁ e₂).toNat < 2 ^ 2098 := by
    calc m₁ * 2 ^ (e₁ - min e₁ e₂).toNat
        < 2 ^ 53 * 2 ^ (e₁ - min e₁ e₂).toNat :=
          (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr hm₁
      _ = 2 ^ (53 + (e₁ - min e₁ e₂).toNat) := by rw [Nat.pow_add]
      _ ≤ 2 ^ 2098 := Nat.pow_le_pow_right (by omega) (by omega)
  have hB : m₂ * 2 ^ (e₂ - min e₁ e₂).toNat < 2 ^ 2098 := by
    calc m₂ * 2 ^ (e₂ - min e₁ e₂).toNat
        < 2 ^ 53 * 2 ^ (e₂ - min e₁ e₂).toNat :=
          (Nat.mul_lt_mul_right (Nat.two_pow_pos _)).mpr hm₂
      _ = 2 ^ (53 + (e₂ - min e₁ e₂).toNat) := by rw [Nat.pow_add]
      _ ≤ 2 ^ 2098 := Nat.pow_le_pow_right (by omega) (by omega)
  have habs : (s₁.apply ((m₁ * 2 ^ (e₁ - min e₁ e₂).toNat : Nat) : Int)
      + s₂.apply ((m₂ * 2 ^ (e₂ - min e₁ e₂).toNat : Nat) : Int)).natAbs
      ≤ m₁ * 2 ^ (e₁ - min e₁ e₂).toNat + m₂ * 2 ^ (e₂ - min e₁ e₂).toNat := by
    cases s₁ <;> cases s₂ <;> simp only [Sign.apply] <;> omega
  have hsum : (s₁.apply ((m₁ * 2 ^ (e₁ - min e₁ e₂).toNat : Nat) : Int)
      + s₂.apply ((m₂ * 2 ^ (e₂ - min e₁ e₂).toNat : Nat) : Int)).natAbs < 2 ^ 2099 := by
    have h2 : (2 ^ 2098 : Nat) + 2 ^ 2098 = 2 ^ 2099 := by
      rw [Nat.pow_succ]
    omega
  have hlog : (s₁.apply ((m₁ * 2 ^ (e₁ - min e₁ e₂).toNat : Nat) : Int)
      + s₂.apply ((m₂ * 2 ^ (e₂ - min e₁ e₂).toNat : Nat) : Int)).natAbs.log2 ≤ 2098 := by
    rcases Nat.eq_zero_or_pos (s₁.apply ((m₁ * 2 ^ (e₁ - min e₁ e₂).toNat : Nat) : Int)
        + s₂.apply ((m₂ * 2 ^ (e₂ - min e₁ e₂).toNat : Nat) : Int)).natAbs with h0 | h0
    · rw [h0, show Nat.log2 0 = 0 from rfl]
      omega
    · have := (Nat.log2_lt (by omega)).mpr hsum
      omega
  simp only [totalExponent]
  omega

/-- `add` with a finite constant: the shape of the result. -/
theorem add_shape {u : UnpackedFloat} (hu : Canonical u) (hun : u ≠ .notANumber)
    {sc : Sign} {mc : Nat} {ec : Int} {hc : 0 < mc}
    (hcanC : Canonical (.finite sc mc ec hc)) :
    RoundShape (UnpackedFloat.add .binary64 u (.finite sc mc ec hc))
      ∧ UnpackedFloat.add .binary64 u (.finite sc mc ec hc) ≠ .notANumber := by
  obtain ⟨hmc, hloc, hhic, hnc⟩ := canonical_finite_bounds hcanC
  cases hu with
  | notANumber => exact absurd rfl hun
  | infinity s =>
    exact ⟨.canonical (.infinity s), fun hcon => UnpackedFloat.noConfusion hcon⟩
  | zero s =>
    exact ⟨.canonical hcanC, fun hcon => UnpackedFloat.noConfusion hcon⟩
  | subnormal s m hm hmlt =>
    rw [add_finite_unfold]
    exact normalize_shape _ _ _ (add_cap s sc (by omega) hmc (by omega) (by omega) hloc hhic)
  | normal s m e hm hlo hhi helo hehi =>
    rw [add_finite_unfold]
    exact normalize_shape _ _ _ (add_cap s sc hhi hmc helo hehi hloc hhic)

/-- `add` with a zero constant is the identity on keys and shapes. -/
theorem add_zero_key {u : UnpackedFloat} (hu : Canonical u) (hun : u ≠ .notANumber)
    (sc : Sign) :
    key (UnpackedFloat.add .binary64 u (.zero sc)) = key u
      ∧ RoundShape (UnpackedFloat.add .binary64 u (.zero sc))
      ∧ UnpackedFloat.add .binary64 u (.zero sc) ≠ .notANumber := by
  cases hu with
  | notANumber => exact absurd rfl hun
  | infinity s =>
    exact ⟨rfl, .canonical (.infinity s), fun hcon => UnpackedFloat.noConfusion hcon⟩
  | zero s =>
    cases s <;> cases sc <;>
      exact ⟨rfl, .canonical (.zero _), fun hcon => UnpackedFloat.noConfusion hcon⟩
  | subnormal s m hm hmlt =>
    exact ⟨rfl, .canonical (.subnormal s m hm hmlt),
      fun hcon => UnpackedFloat.noConfusion hcon⟩
  | normal s m e hm hlo hhi helo hehi =>
    exact ⟨rfl, .canonical (.normal s m e hm hlo hhi helo hehi),
      fun hcon => UnpackedFloat.noConfusion hcon⟩

/-- `normalize` monotonicity, hypotheses on quantum-scaled values. -/
theorem key_normalize_mono_value {M₁ M₂ E₁ E₂ : Int} (z₁ z₂ : Sign)
    (h : M₁ * 2 ^ (E₁ + 1074).toNat ≤ M₂ * 2 ^ (E₂ + 1074).toNat)
    (hE₁ : -1074 ≤ E₁) (hE₂ : -1074 ≤ E₂) :
    key (UnpackedFloat.normalize .binary64 M₁ E₁ z₁)
      ≤ key (UnpackedFloat.normalize .binary64 M₂ E₂ z₂) := by
  apply key_normalize_mono
  apply int_le_cancel_pow ((min E₁ E₂ + 1074).toNat)
  have h₁ : M₁ * 2 ^ (E₁ - min E₁ E₂).toNat * 2 ^ (min E₁ E₂ + 1074).toNat
      = M₁ * 2 ^ (E₁ + 1074).toNat := by
    rw [Int.mul_assoc, ← int_pow_split]
    have he : (E₁ - min E₁ E₂).toNat + (min E₁ E₂ + 1074).toNat = (E₁ + 1074).toNat := by
      omega
    rw [he]
  have h₂ : M₂ * 2 ^ (E₂ - min E₁ E₂).toNat * 2 ^ (min E₁ E₂ + 1074).toNat
      = M₂ * 2 ^ (E₂ + 1074).toNat := by
    rw [Int.mul_assoc, ← int_pow_split]
    have he : (E₂ - min E₁ E₂).toNat + (min E₁ E₂ + 1074).toNat = (E₂ + 1074).toNat := by
      omega
    rw [he]
  rw [h₁, h₂]
  exact h

/-- The key of the constant, in the aligned-sum value form. -/
theorem key_const_value (sc : Sign) (mc : Nat) (ec : Int) (hc : 0 < mc) :
    sc.apply (mc : Int) * 2 ^ (ec + 1074).toNat = key (.finite sc mc ec hc) := by
  rw [key_finite_cast, sign_apply_mul]
  congr 1

/-- `add` monotonicity, finite against finite. -/
theorem key_add_mono_finite {sa sb : Sign} {ma mb : Nat} {ea eb : Int}
    {hma : 0 < ma} {hmb : 0 < mb} {sc : Sign} {mc : Nat} {ec : Int} {hc : 0 < mc}
    (hloa : -1074 ≤ ea) (hlob : -1074 ≤ eb) (hloc : -1074 ≤ ec)
    (h : key (.finite sa ma ea hma) ≤ key (.finite sb mb eb hmb)) :
    key (UnpackedFloat.add .binary64 (.finite sa ma ea hma) (.finite sc mc ec hc))
      ≤ key (UnpackedFloat.add .binary64 (.finite sb mb eb hmb) (.finite sc mc ec hc)) := by
  rw [add_finite_unfold, add_finite_unfold]
  apply key_normalize_mono_value _ _ _ (by omega) (by omega)
  rw [add_key_value sa ma ea hma sc mc ec hc hloa hloc,
    add_key_value sb mb eb hmb sc mc ec hc hlob hloc]
  omega

/-- `add` of a canonical finite constant is key-monotone on canonical
non-NaN inputs. -/
theorem key_add_mono {a b : UnpackedFloat} (ha : Canonical a) (hb : Canonical b)
    (han : a ≠ .notANumber) (hbn : b ≠ .notANumber)
    {sc : Sign} {mc : Nat} {ec : Int} {hc : 0 < mc}
    (hcanC : Canonical (.finite sc mc ec hc))
    (h : key a ≤ key b) :
    key (UnpackedFloat.add .binary64 a (.finite sc mc ec hc))
      ≤ key (UnpackedFloat.add .binary64 b (.finite sc mc ec hc)) := by
  obtain ⟨hmc, hloc, hhic, hnc⟩ := canonical_finite_bounds hcanC
  have hp := HUGE_pos
  obtain ⟨hth, hcast⟩ := pow2098_facts
  have hself := normalize_canonical_self hcanC
  have hCnn : (UnpackedFloat.finite sc mc ec hc) ≠ .notANumber :=
    fun hcon => UnpackedFloat.noConfusion hcon
  cases ha with
  | notANumber => exact absurd rfl han
  | infinity s =>
    cases s
    · have hsh := add_shape (hc := hc) hb hbn hcanC
      exact (roundShape_key_bounds hsh.1 hsh.2).1
    · by_cases hinf : ∃ t, b = .infinity t
      · obtain ⟨t, rfl⟩ := hinf
        cases t
        · exfalso
          have h' : HUGE ≤ -HUGE := h
          omega
        · exact Int.le_refl _
      · exfalso
        have hsmall := canonical_key_small hb (fun t ht => hinf ⟨t, ht⟩)
        have h' : HUGE ≤ key b := h
        omega
  | zero s =>
    cases hb with
    | notANumber => exact absurd rfl hbn
    | infinity t =>
      cases t
      · exfalso
        have h' : (0 : Int) ≤ -HUGE := h
        omega
      · exact (roundShape_key_bounds (.canonical hcanC) hCnn).2
    | zero t => exact Int.le_refl _
    | subnormal t m hm hmlt =>
      have h' : (0 : Int) ≤ key (.finite t m (-1074 : Int) hm) := h
      calc key (UnpackedFloat.add .binary64 (.zero s) (.finite sc mc ec hc))
          = key (UnpackedFloat.normalize .binary64 (sc.apply mc) ec .positive) := by
            rw [hself]
            rfl
        _ ≤ key (UnpackedFloat.add .binary64 (.finite t m (-1074 : Int) hm)
              (.finite sc mc ec hc)) := by
            rw [add_finite_unfold]
            apply key_normalize_mono_value _ _ _ hloc (by omega)
            rw [key_const_value sc mc ec hc,
              add_key_value t m (-1074 : Int) hm sc mc ec hc (by omega) hloc]
            omega
    | normal t m e hm hlo hhi helo hehi =>
      have h' : (0 : Int) ≤ key (.finite t m e hm) := h
      calc key (UnpackedFloat.add .binary64 (.zero s) (.finite sc mc ec hc))
          = key (UnpackedFloat.normalize .binary64 (sc.apply mc) ec .positive) := by
            rw [hself]
            rfl
        _ ≤ key (UnpackedFloat.add .binary64 (.finite t m e hm) (.finite sc mc ec hc)) := by
            rw [add_finite_unfold]
            apply key_normalize_mono_value _ _ _ hloc (by omega)
            rw [key_const_value sc mc ec hc,
              add_key_value t m e hm sc mc ec hc helo hloc]
            omega
  | subnormal s m hm hmlt =>
    have hcanA : Canonical (.finite s m (-1074 : Int) hm) := .subnormal s m hm hmlt
    cases hb with
    | notANumber => exact absurd rfl hbn
    | infinity t =>
      cases t
      · exfalso
        have hsmall := canonical_key_small hcanA (fun t ht => UnpackedFloat.noConfusion ht)
        have h' : key _ ≤ -HUGE := h
        omega
      · have hsh := add_shape (hc := hc) hcanA
          (fun hcon => UnpackedFloat.noConfusion hcon) hcanC
        exact (roundShape_key_bounds hsh.1 hsh.2).2
    | zero t =>
      have h' : key (.finite s m (-1074 : Int) hm) ≤ (0 : Int) := h
      calc key (UnpackedFloat.add .binary64 (.finite s m (-1074 : Int) hm)
            (.finite sc mc ec hc))
          ≤ key (UnpackedFloat.normalize .binary64 (sc.apply mc) ec .positive) := by
            rw [add_finite_unfold]
            apply key_normalize_mono_value _ _ _ (by omega) hloc
            rw [key_const_value sc mc ec hc,
              add_key_value s m (-1074 : Int) hm sc mc ec hc (by omega) hloc]
            omega
        _ = key (UnpackedFloat.add .binary64 (.zero t) (.finite sc mc ec hc)) := by
            rw [hself]
            rfl
    | subnormal t m' hm' hmlt' =>
      exact key_add_mono_finite (by omega) (by omega) hloc h
    | normal t m' e' hm' hlo' hhi' helo' hehi' =>
      exact key_add_mono_finite (by omega) helo' hloc h
  | normal s m e hm hlo hhi helo hehi =>
    have hcanA : Canonical (.finite s m e hm) := .normal s m e hm hlo hhi helo hehi
    cases hb with
    | notANumber => exact absurd rfl hbn
    | infinity t =>
      cases t
      · exfalso
        have hsmall := canonical_key_small hcanA (fun t ht => UnpackedFloat.noConfusion ht)
        have h' : key _ ≤ -HUGE := h
        omega
      · have hsh := add_shape (hc := hc) hcanA
          (fun hcon => UnpackedFloat.noConfusion hcon) hcanC
        exact (roundShape_key_bounds hsh.1 hsh.2).2
    | zero t =>
      have h' : key (.finite s m e hm) ≤ (0 : Int) := h
      calc key (UnpackedFloat.add .binary64 (.finite s m e hm) (.finite sc mc ec hc))
          ≤ key (UnpackedFloat.normalize .binary64 (sc.apply mc) ec .positive) := by
            rw [add_finite_unfold]
            apply key_normalize_mono_value _ _ _ (by omega) hloc
            rw [key_const_value sc mc ec hc,
              add_key_value s m e hm sc mc ec hc helo hloc]
            omega
        _ = key (UnpackedFloat.add .binary64 (.zero t) (.finite sc mc ec hc)) := by
            rw [hself]
            rfl
    | subnormal t m' hm' hmlt' =>
      exact key_add_mono_finite helo (by omega) hloc h
    | normal t m' e' hm' hlo' hhi' helo' hehi' =>
      exact key_add_mono_finite helo helo' hloc h

/-! ## Comparison bridges: `le`/`lt` against keys -/

theorem le_ne_nan_left {u v : UnpackedFloat} (h : UnpackedFloat.le u v = true) :
    u ≠ .notANumber := by
  intro rfl
  rw [UnpackedFloat.le] at h
  simp [UnpackedFloat.compare] at h

theorem le_ne_nan_right {u v : UnpackedFloat} (h : UnpackedFloat.le u v = true) :
    v ≠ .notANumber := by
  intro rfl
  rw [UnpackedFloat.le] at h
  cases u <;> simp [UnpackedFloat.compare] at h

/-- A true `le` on canonical floats yields the key order. -/
theorem key_of_le {u v : UnpackedFloat} (hu : Canonical u) (hv : Canonical v)
    (h : UnpackedFloat.le u v = true) : key u ≤ key v := by
  have h1 := le_ne_nan_left h
  have h2 := le_ne_nan_right h
  rw [UnpackedFloat.le, compare_eq_key hu hv h1 h2] at h
  rcases Int.lt_trichotomy (key u) (key v) with hk | hk | hk
  · omega
  · omega
  · exfalso
    rw [Int.compare_eq_gt.mpr hk] at h
    simp [Option.any] at h

/-- Key order on canonical non-NaN floats gives a true `le`. -/
theorem le_of_key {u v : UnpackedFloat} (hu : Canonical u) (hv : Canonical v)
    (h1 : u ≠ .notANumber) (h2 : v ≠ .notANumber) (hk : key u ≤ key v) :
    UnpackedFloat.le u v = true := by
  rw [UnpackedFloat.le, compare_eq_key hu hv h1 h2]
  rcases Int.lt_trichotomy (key u) (key v) with hlt | heq | hgt
  · rw [Int.compare_eq_lt.mpr hlt]
    rfl
  · rw [Int.compare_eq_eq.mpr heq]
    rfl
  · omega

theorem lt_ne_nan_left {u v : UnpackedFloat} (h : UnpackedFloat.lt u v = true) :
    u ≠ .notANumber := by
  intro rfl
  rw [UnpackedFloat.lt] at h
  simp [UnpackedFloat.compare] at h

theorem lt_ne_nan_right {u v : UnpackedFloat} (h : UnpackedFloat.lt u v = true) :
    v ≠ .notANumber := by
  intro rfl
  rw [UnpackedFloat.lt] at h
  cases u <;> simp [UnpackedFloat.compare] at h

/-- A true `lt` on canonical floats yields the strict key order. -/
theorem key_of_lt {u v : UnpackedFloat} (hu : Canonical u) (hv : Canonical v)
    (h : UnpackedFloat.lt u v = true) : key u < key v := by
  have h1 := lt_ne_nan_left h
  have h2 := lt_ne_nan_right h
  rw [UnpackedFloat.lt, compare_eq_key hu hv h1 h2] at h
  simp at h
  exact Int.compare_eq_lt.mp h

/-- Strict key order on canonical non-NaN floats gives a true `lt`. -/
theorem lt_of_key {u v : UnpackedFloat} (hu : Canonical u) (hv : Canonical v)
    (h1 : u ≠ .notANumber) (h2 : v ≠ .notANumber) (hk : key u < key v) :
    UnpackedFloat.lt u v = true := by
  rw [UnpackedFloat.lt, compare_eq_key hu hv h1 h2, Int.compare_eq_lt.mpr hk]
  rfl

/-- A strict bound below a canonical float and above zero pins it to a
positive finite value. -/
theorem pos_finite_of_bounds {u : UnpackedFloat} (hu : Canonical u)
    (h0 : UnpackedFloat.lt (.zero .positive) u = true)
    (hInf : UnpackedFloat.lt u (.infinity .positive) = true) :
    ∃ (mc : Nat) (ec : Int) (hc : 0 < mc), u = .finite .positive mc ec hc := by
  cases hu with
  | notANumber =>
    rw [UnpackedFloat.lt] at h0
    simp [UnpackedFloat.compare] at h0
  | infinity s =>
    cases s
    · rw [UnpackedFloat.lt] at h0
      simp [UnpackedFloat.compare] at h0
    · rw [UnpackedFloat.lt] at hInf
      simp [UnpackedFloat.compare, compare] at hInf
  | zero s =>
    rw [UnpackedFloat.lt] at h0
    simp [UnpackedFloat.compare] at h0
  | subnormal t m hm hmlt =>
    cases t
    · rw [UnpackedFloat.lt] at h0
      simp [UnpackedFloat.compare] at h0
    · exact ⟨m, -1074, hm, rfl⟩
  | normal t m e hm hlo hhi helo hehi =>
    cases t
    · rw [UnpackedFloat.lt] at h0
      simp [UnpackedFloat.compare] at h0
    · exact ⟨m, e, hm, rfl⟩

/-- Open infinite bounds on both sides pin a canonical float to zero or a
finite value. -/
theorem finite_or_zero_of_bounds {u : UnpackedFloat} (hu : Canonical u)
    (hLo : UnpackedFloat.lt (.infinity .negative) u = true)
    (hHi : UnpackedFloat.lt u (.infinity .positive) = true) :
    (∃ s, u = .zero s) ∨ ∃ (s : Sign) (m : Nat) (e : Int) (h : 0 < m),
      u = .finite s m e h ∧ Canonical (.finite s m e h) := by
  cases hu with
  | notANumber =>
    rw [UnpackedFloat.lt] at hLo
    simp [UnpackedFloat.compare] at hLo
  | infinity s =>
    cases s
    · rw [UnpackedFloat.lt] at hLo
      simp [UnpackedFloat.compare, compare] at hLo
    · rw [UnpackedFloat.lt] at hHi
      simp [UnpackedFloat.compare, compare] at hHi
  | zero s => exact Or.inl ⟨s, rfl⟩
  | subnormal t m hm hmlt =>
    exact Or.inr ⟨t, m, -1074, hm, rfl, .subnormal t m hm hmlt⟩
  | normal t m e hm hlo hhi helo hehi =>
    exact Or.inr ⟨t, m, e, hm, rfl, .normal t m e hm hlo hhi helo hehi⟩

/-! ## The four monotonicity facts at the `Float` layer -/

theorem decide_eq_true_bool (b : Bool) : decide (b = true) = b := by
  cases b <;> rfl

theorem float_le_unpack (a b : Float) :
    Float.le a b = UnpackedFloat.le a.toModel.unpack b.toModel.unpack :=
  decide_eq_true_bool _

theorem float_lt_unpack (a b : Float) :
    Float.lt a b = UnpackedFloat.lt a.toModel.unpack b.toModel.unpack :=
  decide_eq_true_bool _

/-- The bounds `0 < c` and `c < ∞` pin `c`'s unpacking to a canonical
positive finite value. -/
theorem unpack_pos_finite {c : Float} (h0 : (0 : Float) < c)
    (hInf : c < (1.0 / 0.0 : Float)) :
    ∃ (mc : Nat) (ec : Int) (hc : 0 < mc),
      c.toModel.unpack = .finite .positive mc ec hc
        ∧ Canonical (.finite .positive mc ec hc) := by
  have h0' : Float.lt 0 c = true := h0
  have hI' : Float.lt c (1.0 / 0.0) = true := hInf
  rw [float_lt_unpack,
    show (0 : Float).toModel.unpack = UnpackedFloat.zero .positive from rfl] at h0'
  rw [float_lt_unpack,
    show ((1.0 / 0.0 : Float)).toModel.unpack = UnpackedFloat.infinity .positive from rfl] at hI'
  obtain ⟨mc, ec, hc, hcu⟩ := pos_finite_of_bounds (canonical_unpack _) h0' hI'
  have hcanC : Canonical (.finite .positive mc ec hc) := by
    rw [← hcu]
    exact canonical_unpack _
  exact ⟨mc, ec, hc, hcu, hcanC⟩

/-- The bounds `-∞ < c` and `c < ∞` pin `c`'s unpacking to zero or a
canonical finite value. -/
theorem unpack_finite_or_zero {c : Float} (hLo : (-(1.0 / 0.0) : Float) < c)
    (hHi : c < (1.0 / 0.0 : Float)) :
    (∃ s, c.toModel.unpack = .zero s)
      ∨ ∃ (s : Sign) (m : Nat) (e : Int) (h : 0 < m),
          c.toModel.unpack = .finite s m e h ∧ Canonical (.finite s m e h) := by
  have hL' : Float.lt (-(1.0 / 0.0)) c = true := hLo
  have hH' : Float.lt c (1.0 / 0.0) = true := hHi
  rw [float_lt_unpack,
    show ((-(1.0 / 0.0) : Float)).toModel.unpack = UnpackedFloat.infinity .negative from rfl] at hL'
  rw [float_lt_unpack,
    show ((1.0 / 0.0 : Float)).toModel.unpack = UnpackedFloat.infinity .positive from rfl] at hH'
  exact finite_or_zero_of_bounds (canonical_unpack _) hL' hH'

/-- Multiplying both sides of a `≤` by a positive finite constant. -/
theorem float_le_mul_right {x y c : Float} (hxy : Float.le x y = true)
    (h0 : (0 : Float) < c) (hInf : c < (1.0 / 0.0 : Float)) :
    Float.le (x * c) (y * c) = true := by
  obtain ⟨mc, ec, hc, hcu, hcanC⟩ := unpack_pos_finite h0 hInf
  obtain ⟨hmc, hloc, hhic, hnc⟩ := canonical_finite_bounds hcanC
  rw [float_le_unpack] at hxy
  have hxc : Canonical x.toModel.unpack := canonical_unpack _
  have hyc : Canonical y.toModel.unpack := canonical_unpack _
  have hnnx := le_ne_nan_left hxy
  have hnny := le_ne_nan_right hxy
  have hk := key_of_le hxc hyc hxy
  have hmono := key_mul_mono (hc := hc) hxc hyc hnnx hnny hmc hloc hhic hnc hk
  have hshx := mul_shape (hc := hc) hxc hnnx hmc hloc hhic hnc
  have hshy := mul_shape (hc := hc) hyc hnny hmc hloc hhic hnc
  have hpk := key_unpack_pack_mono hshx.1 hshy.1 hshx.2 hshy.2 hmono
  rw [float_le_unpack]
  have hgx : (x * c).toModel.unpack
      = unpack .binary64 (UnpackedFloat.pack .binary64
          (UnpackedFloat.mul .binary64 x.toModel.unpack (.finite .positive mc ec hc))) := by
    rw [← hcu]
    rfl
  have hgy : (y * c).toModel.unpack
      = unpack .binary64 (UnpackedFloat.pack .binary64
          (UnpackedFloat.mul .binary64 y.toModel.unpack (.finite .positive mc ec hc))) := by
    rw [← hcu]
    rfl
  rw [hgx, hgy]
  exact le_of_key (canonical_unpack _) (canonical_unpack _)
    (unpack_pack_ne_nan hshx.1 hshx.2) (unpack_pack_ne_nan hshy.1 hshy.2) hpk

/-- Dividing both sides of a `≤` by a positive finite constant. -/
theorem float_le_div_right {x y c : Float} (hxy : Float.le x y = true)
    (h0 : (0 : Float) < c) (hInf : c < (1.0 / 0.0 : Float)) :
    Float.le (x / c) (y / c) = true := by
  obtain ⟨mc, ec, hc, hcu, hcanC⟩ := unpack_pos_finite h0 hInf
  obtain ⟨hmc, hloc, hhic, hnc⟩ := canonical_finite_bounds hcanC
  rw [float_le_unpack] at hxy
  have hxc : Canonical x.toModel.unpack := canonical_unpack _
  have hyc : Canonical y.toModel.unpack := canonical_unpack _
  have hnnx := le_ne_nan_left hxy
  have hnny := le_ne_nan_right hxy
  have hk := key_of_le hxc hyc hxy
  have hmono := key_div_mono (hc := hc) hxc hyc hnnx hnny hmc hloc hhic hk
  have hshx := div_shape (hc := hc) hxc hnnx hmc hloc hhic
  have hshy := div_shape (hc := hc) hyc hnny hmc hloc hhic
  have hpk := key_unpack_pack_mono hshx.1 hshy.1 hshx.2 hshy.2 hmono
  rw [float_le_unpack]
  have hgx : (x / c).toModel.unpack
      = unpack .binary64 (UnpackedFloat.pack .binary64
          (UnpackedFloat.div .binary64 x.toModel.unpack (.finite .positive mc ec hc))) := by
    rw [← hcu]
    rfl
  have hgy : (y / c).toModel.unpack
      = unpack .binary64 (UnpackedFloat.pack .binary64
          (UnpackedFloat.div .binary64 y.toModel.unpack (.finite .positive mc ec hc))) := by
    rw [← hcu]
    rfl
  rw [hgx, hgy]
  exact le_of_key (canonical_unpack _) (canonical_unpack _)
    (unpack_pack_ne_nan hshx.1 hshx.2) (unpack_pack_ne_nan hshy.1 hshy.2) hpk

/-- Adding a finite constant to both sides of a `≤`. -/
theorem float_le_add_right {x y c : Float} (hxy : Float.le x y = true)
    (hLo : (-(1.0 / 0.0) : Float) < c) (hHi : c < (1.0 / 0.0 : Float)) :
    Float.le (x + c) (y + c) = true := by
  rw [float_le_unpack] at hxy
  have hxc : Canonical x.toModel.unpack := canonical_unpack _
  have hyc : Canonical y.toModel.unpack := canonical_unpack _
  have hnnx := le_ne_nan_left hxy
  have hnny := le_ne_nan_right hxy
  have hk := key_of_le hxc hyc hxy
  rw [float_le_unpack]
  rcases unpack_finite_or_zero hLo hHi with ⟨sc, hcu⟩ | ⟨sc, mc, ec, hc, hcu, hcanC⟩
  · -- zero constant: keys pass through unchanged
    obtain ⟨hkx, hshx, hnx⟩ := add_zero_key hxc hnnx sc
    obtain ⟨hky, hshy, hny⟩ := add_zero_key hyc hnny sc
    have hpk := key_unpack_pack_mono hshx hshy hnx hny (by omega)
    have hgx : (x + c).toModel.unpack
        = unpack .binary64 (UnpackedFloat.pack .binary64
            (UnpackedFloat.add .binary64 x.toModel.unpack (.zero sc))) := by
      rw [← hcu]
      rfl
    have hgy : (y + c).toModel.unpack
        = unpack .binary64 (UnpackedFloat.pack .binary64
            (UnpackedFloat.add .binary64 y.toModel.unpack (.zero sc))) := by
      rw [← hcu]
      rfl
    rw [hgx, hgy]
    exact le_of_key (canonical_unpack _) (canonical_unpack _)
      (unpack_pack_ne_nan hshx hnx) (unpack_pack_ne_nan hshy hny) hpk
  · have hmono := key_add_mono hxc hyc hnnx hnny hcanC hk
    have hshx := add_shape (hc := hc) hxc hnnx hcanC
    have hshy := add_shape (hc := hc) hyc hnny hcanC
    have hpk := key_unpack_pack_mono hshx.1 hshy.1 hshx.2 hshy.2 hmono
    have hgx : (x + c).toModel.unpack
        = unpack .binary64 (UnpackedFloat.pack .binary64
            (UnpackedFloat.add .binary64 x.toModel.unpack (.finite sc mc ec hc))) := by
      rw [← hcu]
      rfl
    have hgy : (y + c).toModel.unpack
        = unpack .binary64 (UnpackedFloat.pack .binary64
            (UnpackedFloat.add .binary64 y.toModel.unpack (.finite sc mc ec hc))) := by
      rw [← hcu]
      rfl
    rw [hgx, hgy]
    exact le_of_key (canonical_unpack _) (canonical_unpack _)
      (unpack_pack_ne_nan hshx.1 hshx.2) (unpack_pack_ne_nan hshy.1 hshy.2) hpk

/-- An upper infinity bound flips to a lower one under negation. -/
theorem float_neg_bound_lo {c : Float} (h : Float.lt c (1.0 / 0.0) = true) :
    Float.lt (-(1.0 / 0.0)) (-c) = true := by
  rw [float_lt_unpack] at h ⊢
  rw [show ((-(1.0 / 0.0) : Float)).toModel.unpack = UnpackedFloat.infinity .negative from rfl]
  rw [show ((1.0 / 0.0 : Float)).toModel.unpack = UnpackedFloat.infinity .positive from rfl] at h
  rw [show (-c).toModel.unpack = c.toModel.unpack.neg from model_unpack_pack_neg _]
  rw [UnpackedFloat.lt] at h ⊢
  cases hcu : c.toModel.unpack with
  | notANumber =>
    rw [hcu] at h
    simp [UnpackedFloat.compare] at h
  | infinity s =>
    rw [hcu] at h
    cases s
    · simp [UnpackedFloat.neg, UnpackedFloat.compare, compare]
    · simp [UnpackedFloat.compare, compare] at h
  | zero s => cases s <;> simp [UnpackedFloat.neg, UnpackedFloat.compare]
  | finite s m e hm => cases s <;> simp [UnpackedFloat.neg, UnpackedFloat.compare]

/-- A lower infinity bound flips to an upper one under negation. -/
theorem float_neg_bound_hi {c : Float} (h : Float.lt (-(1.0 / 0.0)) c = true) :
    Float.lt (-c) (1.0 / 0.0) = true := by
  rw [float_lt_unpack] at h ⊢
  rw [show ((1.0 / 0.0 : Float)).toModel.unpack = UnpackedFloat.infinity .positive from rfl]
  rw [show ((-(1.0 / 0.0) : Float)).toModel.unpack = UnpackedFloat.infinity .negative from rfl] at h
  rw [show (-c).toModel.unpack = c.toModel.unpack.neg from model_unpack_pack_neg _]
  rw [UnpackedFloat.lt] at h ⊢
  cases hcu : c.toModel.unpack with
  | notANumber =>
    rw [hcu] at h
    simp [UnpackedFloat.compare] at h
  | infinity s =>
    rw [hcu] at h
    cases s
    · simp [UnpackedFloat.compare, compare] at h
    · simp [UnpackedFloat.neg, UnpackedFloat.compare, compare]
  | zero s => cases s <;> simp [UnpackedFloat.neg, UnpackedFloat.compare]
  | finite s m e hm => cases s <;> simp [UnpackedFloat.neg, UnpackedFloat.compare]

/-- Subtracting a finite constant from both sides of a `≤`: IEEE
subtraction is addition of the negation, whose bounds mirror. -/
theorem float_le_sub_right {x y c : Float} (hxy : Float.le x y = true)
    (hLo : (-(1.0 / 0.0) : Float) < c) (hHi : c < (1.0 / 0.0 : Float)) :
    Float.le (x - c) (y - c) = true := by
  have hsub : ∀ z : Float, (z - c) = (z + (-c)) := fun z => float_sub_eq_add_neg z c
  rw [hsub, hsub]
  exact float_le_add_right hxy (float_neg_bound_lo hHi) (float_neg_bound_hi hLo)

/-! ## Order transitivity at the `Float` layer

Unpacking is always canonical and a true strict comparison rules out NaN
on both ends, so the IEEE order chains exactly as the `Int` order on keys
does. -/

theorem float_lt_trans {a b c : Float} (hab : Float.lt a b = true)
    (hbc : Float.lt b c = true) : Float.lt a c = true := by
  rw [float_lt_unpack] at hab hbc ⊢
  have hk := Int.lt_trans
    (key_of_lt (canonical_unpack _) (canonical_unpack _) hab)
    (key_of_lt (canonical_unpack _) (canonical_unpack _) hbc)
  exact lt_of_key (canonical_unpack _) (canonical_unpack _)
    (lt_ne_nan_left hab) (lt_ne_nan_right hbc) hk

theorem float_lt_of_lt_of_le {a b c : Float} (hab : Float.lt a b = true)
    (hbc : Float.le b c = true) : Float.lt a c = true := by
  rw [float_lt_unpack] at hab ⊢
  rw [float_le_unpack] at hbc
  have hk := Int.lt_of_lt_of_le
    (key_of_lt (canonical_unpack _) (canonical_unpack _) hab)
    (key_of_le (canonical_unpack _) (canonical_unpack _) hbc)
  exact lt_of_key (canonical_unpack _) (canonical_unpack _)
    (lt_ne_nan_left hab) (le_ne_nan_right hbc) hk

theorem float_lt_of_le_of_lt {a b c : Float} (hab : Float.le a b = true)
    (hbc : Float.lt b c = true) : Float.lt a c = true := by
  rw [float_le_unpack] at hab
  rw [float_lt_unpack] at hbc ⊢
  have hk := Int.lt_of_le_of_lt
    (key_of_le (canonical_unpack _) (canonical_unpack _) hab)
    (key_of_lt (canonical_unpack _) (canonical_unpack _) hbc)
  exact lt_of_key (canonical_unpack _) (canonical_unpack _)
    (le_ne_nan_left hab) (lt_ne_nan_right hbc) hk

/-! ## Totality at the `Float` layer

IEEE comparison is total except at NaN, where every comparison is false.
A branch condition that came back false therefore says something about the
reverse comparison only once NaN is ruled out — which the infinity bounds
a `number` binder emits do. -/

/-- A float strictly inside the infinities is not NaN. -/
theorem unpack_ne_nan {c : Float} (hLo : (-(1.0 / 0.0) : Float) < c)
    (hHi : c < (1.0 / 0.0 : Float)) : c.toModel.unpack ≠ .notANumber := by
  rcases unpack_finite_or_zero hLo hHi with ⟨s, h⟩ | ⟨s, m, e, hm, h, _⟩ <;>
    rw [h] <;> intro hc <;> cases hc

/-- A false `<` between two non-NaN floats is the reverse `≤`. -/
theorem float_le_of_not_lt {x y : Float}
    (hxLo : (-(1.0 / 0.0) : Float) < x) (hxHi : x < (1.0 / 0.0 : Float))
    (hyLo : (-(1.0 / 0.0) : Float) < y) (hyHi : y < (1.0 / 0.0 : Float))
    (h : Float.lt x y = false) : Float.le y x = true := by
  have hxn := unpack_ne_nan hxLo hxHi
  have hyn := unpack_ne_nan hyLo hyHi
  rw [float_le_unpack]
  refine le_of_key (canonical_unpack _) (canonical_unpack _) hyn hxn ?_
  by_cases hk : key y.toModel.unpack ≤ key x.toModel.unpack
  · exact hk
  · exfalso
    have hlt : key x.toModel.unpack < key y.toModel.unpack := by omega
    have hc := lt_of_key (canonical_unpack _) (canonical_unpack _) hxn hyn hlt
    rw [float_lt_unpack] at h
    -- `canonical_unpack` fixes its argument in the unpack-of-bits spelling,
    -- so the two comparisons are joined by `trans`, which unifies up to
    -- definitional equality, rather than by rewriting.
    exact Bool.noConfusion (hc.symm.trans h)

end Js.Number.FloatFacts
