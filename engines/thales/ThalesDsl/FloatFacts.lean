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
-/

namespace ThalesDsl.FloatFacts

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

end ThalesDsl.FloatFacts
