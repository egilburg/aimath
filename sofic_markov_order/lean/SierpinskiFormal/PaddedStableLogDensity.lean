import SierpinskiFormal.BooleanWordCesaro
import SierpinskiFormal.MatrixWordLogDensityBridge

/-! # Logarithmic density from stability of a padded digit language

No linear representation is required by this transfer theorem: the
Boolean double-limit property of the padded digit kernel suffices.
-/

noncomputable section
open Filter Topology
open scoped BigOperators

namespace IndependentZeroBlocks

/-- Membership in a natural-number predicate, read on padded little-endian words. -/
def paddedPredicateBool (S : ℕ → Prop) (b : ℕ) (w : List (Fin b)) : Bool := by
  classical
  exact decide (S (Nat.ofDigits b (w.map Fin.val)))

theorem boolIndicator_paddedPredicateBool (S : ℕ → Prop) (b : ℕ)
    (w : List (Fin b)) :
    boolIndicator (paddedPredicateBool S b w) =
      predicateIndicator S (Nat.ofDigits b (w.map Fin.val)) := by
  classical
  simp [paddedPredicateBool, boolIndicator, predicateIndicator]

/-- Stability of the padded digit language in all left and right contexts. -/
def HasStablePaddedDigitKernel (S : ℕ → Prop) (b : ℕ) : Prop :=
  HasBooleanDoubleLimitProperty (fun x y : List (Fin b) ↦
    paddedPredicateBool S b (x ++ y))

theorem exists_padded_digit_word (b : ℕ) (hb : 2 ≤ b) (q : ℕ) :
    ∃ w : List (Fin b), Nat.ofDigits b (w.map Fin.val) = q := by
  obtain ⟨w, _, hw⟩ := exists_fin_digit_word_of_lt_pow b hb q q
    ((Nat.lt_two_pow_self (n := q)).trans_le (Nat.pow_le_pow_left hb q))
  exact ⟨w, hw⟩

/-- Uniform words of a fixed length, followed by a fixed high context,
enumerate exactly one radix block. -/
theorem radixContextProportion_eq_padded_uniformIidWordAverage
    (S : ℕ → Prop) (b : ℕ) (hb : 2 ≤ b) (q r : ℕ)
    (v : List (Fin b)) (hv : Nat.ofDigits b (v.map Fin.val) = q) :
    radixContextProportion S b q r =
      @uniformIidWordAverage (Fin b) inferInstance inferInstance ⟨⟨0, by omega⟩⟩
        (booleanWordIndicator (fun w ↦ paddedPredicateBool S b (w ++ v))) r := by
  letI : Nonempty (Fin b) := ⟨⟨0, by omega⟩⟩
  rw [uniformIidWordAverage_eq_tuple_sum]
  rw [show Fintype.card (Fin b) = b by simp]
  have hsum :
      (∑ x : Fin r → Fin b,
        booleanWordIndicator (fun w ↦ paddedPredicateBool S b (w ++ v)) (List.ofFn x)) =
      ∑ t : Fin (b ^ r), predicateIndicator S (q * b ^ r + t.val) := by
    apply Fintype.sum_equiv (radixTupleEquiv b hb r)
    intro x
    rw [booleanWordIndicator_apply, boolIndicator_paddedPredicateBool]
    congr 1
    simp [List.map_append, Nat.ofDigits_append, hv, radixTupleEquiv]
    ring
  rw [hsum]
  have hfinSum : (∑ t : Fin (b ^ r), predicateIndicator S (q * b ^ r + t.val)) =
      ∑ t ∈ Finset.range (b ^ r), predicateIndicator S (q * b ^ r + t) := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro t ht
    simp [Finset.mem_range.mp ht]
  rw [hfinSum, ← intervalPredicateCount_cast_eq_sum_indicator]
  unfold radixContextProportion
  rw [Nat.cast_pow, div_eq_mul_inv]
  ring

/-- A stable padded digit language has all fixed-context Cesàro frequencies. -/
theorem HasStablePaddedDigitKernel.hasAllFixedContextCesaroMeans
    {S : ℕ → Prop} {b : ℕ} (hS : HasStablePaddedDigitKernel S b) (hb : 2 ≤ b) :
    HasAllFixedContextCesaroMeans S b := by
  letI : Nonempty (Fin b) := ⟨⟨0, by omega⟩⟩
  intro q _hq
  obtain ⟨v, hv⟩ := exists_padded_digit_word b hb q
  let f : List (Fin b) → Bool := fun w ↦ paddedPredicateBool S b (w ++ v)
  have hDLP : HasBooleanDoubleLimitProperty (fun w z ↦ f (z ++ w)) := by
    intro x y row col a c hrow hcol ha hc
    have hh := hS y (fun i ↦ x i ++ v) col row c a
    have he : c = a := hh
      (by intro i; simpa [f, List.append_assoc] using hcol i)
      (by intro i; simpa [f, List.append_assoc] using hrow i) hc ha
    exact he.symm
  obtain ⟨a, ha⟩ := exists_tendsto_boolean_uniform_iid_word_cesaro f hDLP
  refine ⟨a, ?_⟩
  have heq : realCesaroMean (radixContextProportion S b q) =
      uniformIidWordCesaro (booleanWordIndicator f) := by
    funext N
    unfold realCesaroMean uniformIidWordCesaro
    simp only [smul_eq_mul, inv_mul_eq_div]
    congr 1
    apply Finset.sum_congr rfl
    intro r hr
    exact radixContextProportion_eq_padded_uniformIidWordAverage S b hb q r v hv
  rw [heq]
  exact ha

/-- Every stable padded digit language has a standard logarithmic density. -/
theorem HasStablePaddedDigitKernel.exists_standardLogDensity
    {S : ℕ → Prop} {b : ℕ} (hS : HasStablePaddedDigitKernel S b) (hb : 2 ≤ b) :
    ∃ δ : ℝ, HasPredicateStandardLogDensity S δ :=
  hasPredicateStandardLogDensity_of_allFixedContextCesaro S b hb
    (hS.hasAllFixedContextCesaroMeans hb)

end IndependentZeroBlocks
