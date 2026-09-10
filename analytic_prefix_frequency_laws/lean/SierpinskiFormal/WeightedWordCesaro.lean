import SierpinskiFormal.BooleanWordCesaro

/-! # Explicit weighted word averages for stable Boolean predicates

The finite positive source law is kept visible as a weighted translation
operator. This supplies the scalar Cesaro-existence input in the renewal
argument without an implicit transfer from pathwise expectations.
-/

noncomputable section
open Filter Set Function
open scoped Topology BigOperators BoundedContinuousFunction

namespace IndependentZeroBlocks

variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
variable [Fintype A] [Nonempty A]

def weightedLetterAverage (p : A → ℝ) :
    BoundedWordFunction A →L[ℝ] BoundedWordFunction A :=
  ∑ a, p a • wordRightTranslateCLM [a]

@[simp] theorem weightedLetterAverage_apply (p : A → ℝ)
    (f : BoundedWordFunction A) (z : List A) :
    weightedLetterAverage p f z = ∑ a, p a * f (z ++ [a]) := by
  simp [weightedLetterAverage, wordRightTranslateCLM, wordRightTranslate,
    appendWordRight]

theorem weightedLetterAverage_norm_le (p : A → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) :
    ‖weightedLetterAverage p‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  rw [BoundedContinuousFunction.norm_le_of_nonempty]
  intro z
  rw [weightedLetterAverage_apply]
  calc
    ‖∑ a, p a * f (z ++ [a])‖ ≤ ∑ a, ‖p a * f (z ++ [a])‖ := norm_sum_le _ _
    _ ≤ ∑ a, p a * ‖f‖ := by
      apply Finset.sum_le_sum
      intro a _
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hp a)]
      exact mul_le_mul_of_nonneg_left
        (BoundedContinuousFunction.norm_coe_le_norm f (z ++ [a])) (hp a)
    _ = 1 * ‖f‖ := by rw [← Finset.sum_mul, hp1]

theorem weightedLetterAverage_lipschitz (p : A → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) :
    LipschitzWith 1 (weightedLetterAverage p) := by
  apply LipschitzWith.mk_one
  intro f g
  simpa only [dist_eq_norm, map_sub, one_mul] using
    (weightedLetterAverage p).le_of_opNorm_le
      (weightedLetterAverage_norm_le p hp hp1) (f - g)

theorem mapsTo_weightedLetterAverage (p : A → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1)
    (C : Set (BoundedWordFunction A)) (hC : Convex ℝ C)
    (htranslate : ∀ (a : A) {f}, f ∈ C → wordRightTranslate [a] f ∈ C) :
    MapsTo (weightedLetterAverage p) C C := by
  intro f hf
  change (∑ a, p a • wordRightTranslateCLM [a]) f ∈ C
  rw [ContinuousLinearMap.sum_apply]
  apply hC.sum_mem
  · intro a _
    exact hp a
  · exact hp1
  · intro a _
    exact htranslate a hf

/-- Recursion for an actual weighted IID extension, with a fixed left
context. The recursion enumerates every word once with its product weight. -/
def weightedWordExtensionAverage (p : A → ℝ)
    (f : BoundedWordFunction A) : ℕ → List A → ℝ
  | 0, z => f z
  | n + 1, z => ∑ a, p a * weightedWordExtensionAverage p f n (z ++ [a])

theorem iterate_weightedLetterAverage_apply (p : A → ℝ)
    (f : BoundedWordFunction A) (n : ℕ) (z : List A) :
    ((weightedLetterAverage p)^[n] f) z =
      weightedWordExtensionAverage p f n z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', weightedLetterAverage_apply]
      simp only [weightedWordExtensionAverage, ih]

def weightedIidWordCesaro (p : A → ℝ) (f : BoundedWordFunction A) (N : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, weightedWordExtensionAverage p f n []

theorem birkhoffAverage_apply_empty_eq_weightedIidWordCesaro
    (p : A → ℝ) (f : BoundedWordFunction A) (N : ℕ) :
    (birkhoffAverage ℝ (weightedLetterAverage p) id N f) [] =
      weightedIidWordCesaro p f N := by
  rw [birkhoffAverage, birkhoffSum, BoundedContinuousFunction.smul_apply,
    BoundedContinuousFunction.sum_apply]
  simp only [id_eq, iterate_weightedLetterAverage_apply,
    weightedIidWordCesaro, smul_eq_mul]

/-- The full bounded-function mean converges for every finite probability
law and every stable Boolean word predicate. -/
theorem exists_tendsto_boolean_weighted_word_mean
    (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1)
    (q : List A → Bool)
    (hDLP : HasBooleanDoubleLimitProperty (fun w z ↦ q (z ++ w))) :
    ∃ a : BoundedWordFunction A, Tendsto
      (fun N ↦ birkhoffAverage ℝ (weightedLetterAverage p) id N
        (booleanWordIndicator q)) atTop (𝓝 a) := by
  have hDLP' : HasBooleanDoubleLimitProperty (booleanWordRow q) := hDLP
  obtain ⟨hcompact, hcount⟩ :=
    booleanRowClosure_weakly_compact_and_countable (booleanWordRow q) hDLP'
  have hcompact' : IsCompact (toWeakSpace ℝ C(Ultrafilter (List A), ℝ) ''
      extendedBooleanWordRowClosure q) := by
    simpa only [extendedBooleanWordRowClosure, booleanWordRowClosure,
      booleanRowExtensionClosure] using hcompact
  have hcount' : (extendedBooleanWordRowClosure q).Countable := by
    simpa only [extendedBooleanWordRowClosure, booleanWordRowClosure,
      booleanRowExtensionClosure] using hcount
  let K := boundedBooleanWordRowClosure q
  let C := closedConvexHull ℝ K
  have hKcompact := isCompact_boundedBooleanWordRowClosure_of_extended q hcompact'
  have hKcount := countable_boundedBooleanWordRowClosure_of_extended q hcount'
  have hKne : K.Nonempty :=
    ⟨booleanWordIndicator q, booleanWordIndicator_mem_boundedBooleanWordRowClosure q⟩
  have hCcompact : IsCompact (toWeakSpace ℝ (BoundedWordFunction A) '' C) :=
    IndependentZeroBlocks.Set.Countable.isCompact_toWeakSpace_image_closedConvexHull
      hKcount hKne 1
      (fun f hf ↦ norm_le_one_of_mem_boundedBooleanWordRowClosure q hf) hKcompact
  exact exists_tendsto_birkhoffAverage_of_compact_convex_invariant
    (weightedLetterAverage p) (weightedLetterAverage_lipschitz p hp hp1)
    (booleanWordIndicator q) C hCcompact (convex_closedConvexHull (𝕜 := ℝ) (s := K))
    (subset_closedConvexHull (booleanWordIndicator_mem_boundedBooleanWordRowClosure q))
    (mapsTo_weightedLetterAverage p hp hp1 C (convex_closedConvexHull (𝕜 := ℝ) (s := K))
      (fun a _ hf ↦ mapsTo_wordRightTranslate_closedConvexHull q a hf))

theorem exists_tendsto_boolean_weighted_iid_word_cesaro
    (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1)
    (q : List A → Bool)
    (hDLP : HasBooleanDoubleLimitProperty (fun w z ↦ q (z ++ w))) :
    ∃ L : ℝ, Tendsto (weightedIidWordCesaro p (booleanWordIndicator q)) atTop (𝓝 L) := by
  obtain ⟨a, ha⟩ := exists_tendsto_boolean_weighted_word_mean p hp hp1 q hDLP
  refine ⟨a [], ?_⟩
  have heval := ((BoundedContinuousFunction.evalCLM ℝ ([] : List A)).continuous.continuousAt.tendsto).comp ha
  simpa only [Function.comp_def, BoundedContinuousFunction.evalCLM_apply,
    birkhoffAverage_apply_empty_eq_weightedIidWordCesaro] using heval

end IndependentZeroBlocks
