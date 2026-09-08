import SierpinskiFormal.WeakMeanErgodic
import Mathlib.Topology.List
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Convex.Combination

/-!
# IID word averages from a compact translation hull

This file proves the analytic IID stage under an explicit weak compactness
hypothesis on a convex translation-invariant hull.  It does not assert that
the hull exists for recognizable-series support indicators.
-/

noncomputable section

open Filter Finset Function
open scoped Topology BigOperators BoundedContinuousFunction

namespace IndependentZeroBlocks

section CompactInvariantAverages

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A contraction has convergent Cesaro averages at a point contained in a
weakly compact convex invariant set. -/
theorem exists_tendsto_birkhoffAverage_of_compact_convex_invariant
    (T : E →L[ℝ] E) (hT : LipschitzWith 1 T) (x : E) (C : Set E)
    (hCcompact : IsCompact (toWeakSpace ℝ E '' C))
    (hCconvex : Convex ℝ C) (hx : x ∈ C) (hTC : Set.MapsTo T C C) :
    ∃ a : E, Tendsto (birkhoffAverage ℝ T id · x) atTop (𝓝 a) := by
  have hiter : ∀ n : ℕ, T^[n] x ∈ C := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact hTC ih
  apply exists_tendsto_birkhoffAverage_of_weakly_compact T hT x
    (toWeakSpace ℝ E '' C) hCcompact
  filter_upwards [eventually_ne_atTop 0] with n hn
  refine ⟨birkhoffAverage ℝ T id n x, ?_, rfl⟩
  rw [birkhoffAverage, birkhoffSum, Finset.smul_sum]
  apply hCconvex.sum_mem
  · intro k hk
    positivity
  · simp [hn]
  · intro k hk
    exact hiter k

end CompactInvariantAverages

section Words

variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A]

/-- Bounded real functions on finite words, with the supremum norm. -/
abbrev BoundedWordFunction (A : Type*) [TopologicalSpace A] := List A →ᵇ ℝ

/-- Appending a fixed word on the right, as a continuous map on the discrete
word space. -/
def appendWordRight (w : List A) : C(List A, List A) :=
  ⟨fun z ↦ z ++ w, continuous_of_discreteTopology⟩

/-- Right translation of a bounded word function. -/
def wordRightTranslate (w : List A) (f : BoundedWordFunction A) :
    BoundedWordFunction A :=
  f.compContinuous (appendWordRight w)

@[simp] theorem wordRightTranslate_apply (w z : List A)
    (f : BoundedWordFunction A) :
    wordRightTranslate w f z = f (z ++ w) := rfl

/-- Right translation is a continuous linear contraction. -/
def wordRightTranslateCLM (w : List A) :
    BoundedWordFunction A →L[ℝ] BoundedWordFunction A :=
  ({
    toFun := wordRightTranslate w
    map_add' := by
      intro f g
      ext z
      rfl
    map_smul' := by
      intro c f
      ext z
      rfl
  } : BoundedWordFunction A →ₗ[ℝ] BoundedWordFunction A).mkContinuous 1 (fun f ↦ by
    change ‖f.compContinuous (appendWordRight w)‖ ≤ 1 * ‖f‖
    simpa using BoundedContinuousFunction.norm_compContinuous_le f (appendWordRight w))

@[simp] theorem wordRightTranslateCLM_apply (w : List A)
    (f : BoundedWordFunction A) :
    wordRightTranslateCLM w f = wordRightTranslate w f := rfl

theorem wordRightTranslateCLM_norm_le (w : List A) :
    ‖wordRightTranslateCLM (A := A) w‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖f.compContinuous (appendWordRight w)‖ ≤ 1 * ‖f‖
  simpa using BoundedContinuousFunction.norm_compContinuous_le f (appendWordRight w)

/-- The translation convention preserves chronological concatenation. -/
theorem wordRightTranslate_append (u v : List A)
    (f : BoundedWordFunction A) :
    wordRightTranslate u (wordRightTranslate v f) =
      wordRightTranslate (u ++ v) f := by
  ext z
  simp only [wordRightTranslate_apply, List.append_assoc]

/-- The uniform one-letter averaging operator. -/
def uniformLetterAverage [Fintype A] [Nonempty A] :
    BoundedWordFunction A →L[ℝ] BoundedWordFunction A :=
  (Fintype.card A : ℝ)⁻¹ •
    ∑ a : A, wordRightTranslateCLM (A := A) [a]

@[simp] theorem uniformLetterAverage_apply [Fintype A] [Nonempty A]
    (f : BoundedWordFunction A) :
    uniformLetterAverage (A := A) f =
      (Fintype.card A : ℝ)⁻¹ •
        ∑ a : A, wordRightTranslate [a] f := by
  simp [uniformLetterAverage]

/-- Recursive expectation after appending `n` independent uniform letters to
a fixed left context.  The recursion appends the next chronological letter
on the right. -/
def uniformWordExtensionAverage [Fintype A] [Nonempty A]
    (q : BoundedWordFunction A) : ℕ → List A → ℝ
  | 0, z => q z
  | n + 1, z => (Fintype.card A : ℝ)⁻¹ •
      ∑ a : A, uniformWordExtensionAverage q n (z ++ [a])

/-- Uniform expectation of a bounded function on words of exact length `n`. -/
def uniformIidWordAverage [Fintype A] [Nonempty A]
    (q : BoundedWordFunction A) (n : ℕ) : ℝ :=
  uniformWordExtensionAverage q n []

/-- Cesaro mean of the uniform exact-word-length expectations. -/
def uniformIidWordCesaro [Fintype A] [Nonempty A]
    (q : BoundedWordFunction A) (N : ℕ) : ℝ :=
  (N : ℝ)⁻¹ • ∑ n ∈ Finset.range N, uniformIidWordAverage q n

/-- Iterating the letter operator appends IID letters in chronological order. -/
theorem iterate_uniformLetterAverage_apply [Fintype A] [Nonempty A]
    (q : BoundedWordFunction A) (n : ℕ) (z : List A) :
    ((uniformLetterAverage (A := A))^[n] q) z =
      uniformWordExtensionAverage q n z := by
  induction n generalizing z with
  | zero => simp [uniformWordExtensionAverage]
  | succ n ih =>
      rw [Function.iterate_succ_apply', uniformLetterAverage_apply]
      rw [BoundedContinuousFunction.smul_apply,
        BoundedContinuousFunction.sum_apply]
      simp only [wordRightTranslate_apply, ih, uniformWordExtensionAverage]

theorem birkhoffAverage_apply_empty_eq_uniformIidWordCesaro
    [Fintype A] [Nonempty A]
    (q : BoundedWordFunction A) (N : ℕ) :
    (birkhoffAverage ℝ (uniformLetterAverage (A := A)) id N q) [] =
      uniformIidWordCesaro q N := by
  rw [birkhoffAverage, birkhoffSum, BoundedContinuousFunction.smul_apply,
    BoundedContinuousFunction.sum_apply]
  simp only [id_eq, iterate_uniformLetterAverage_apply,
    uniformIidWordAverage, uniformIidWordCesaro]

theorem uniformLetterAverage_norm_le [Fintype A] [Nonempty A] :
    ‖uniformLetterAverage (A := A)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  rw [BoundedContinuousFunction.norm_le_of_nonempty]
  intro z
  rw [uniformLetterAverage_apply]
  rw [BoundedContinuousFunction.smul_apply,
    BoundedContinuousFunction.sum_apply]
  simp only [wordRightTranslate_apply]
  change ‖(Fintype.card A : ℝ)⁻¹ • ∑ a : A, f (z ++ [a])‖ ≤ 1 * ‖f‖
  calc
    ‖(Fintype.card A : ℝ)⁻¹ • ∑ a : A, f (z ++ [a])‖ =
        ‖(Fintype.card A : ℝ)⁻¹‖ * ‖∑ a : A, f (z ++ [a])‖ :=
      norm_smul _ _
    _ ≤ ‖(Fintype.card A : ℝ)⁻¹‖ * ∑ a : A, ‖f (z ++ [a])‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
    _ ≤ ‖(Fintype.card A : ℝ)⁻¹‖ * ∑ _a : A, ‖f‖ := by
      gcongr with a
      exact BoundedContinuousFunction.norm_coe_le_norm f (z ++ [a])
    _ = 1 * ‖f‖ := by
      rw [norm_inv, Real.norm_natCast]
      simp [Fintype.card_ne_zero]

theorem uniformLetterAverage_lipschitz [Fintype A] [Nonempty A] :
    LipschitzWith 1 (uniformLetterAverage (A := A)) := by
  apply LipschitzWith.mk_one
  intro f g
  simpa only [dist_eq_norm, map_sub, one_mul] using
    (uniformLetterAverage (A := A)).le_of_opNorm_le
      (uniformLetterAverage_norm_le (A := A)) (f - g)

/-- A convex set invariant under one-letter right translations is invariant
under the uniform letter average. -/
theorem mapsTo_uniformLetterAverage [Fintype A] [Nonempty A]
    (C : Set (BoundedWordFunction A)) (hCconvex : Convex ℝ C)
    (htranslate : ∀ (a : A) {f}, f ∈ C → wordRightTranslate [a] f ∈ C) :
    Set.MapsTo (uniformLetterAverage (A := A)) C C := by
  intro f hf
  rw [uniformLetterAverage_apply, Finset.smul_sum]
  apply hCconvex.sum_mem
  · intro a ha
    positivity
  · simp [Fintype.card_ne_zero]
  · intro a ha
    exact htranslate a hf

/-- Conditional IID Cesaro theorem.  If a bounded word function belongs to a
convex one-letter-translation-invariant set whose image in the weak topology
is compact, then its uniform IID word-length probabilities have a Cesaro
limit. -/
theorem exists_tendsto_uniform_iid_word_cesaro [Fintype A] [Nonempty A]
    (q : BoundedWordFunction A) (C : Set (BoundedWordFunction A))
    (hCcompact : IsCompact (toWeakSpace ℝ (BoundedWordFunction A) '' C))
    (hCconvex : Convex ℝ C) (hq : q ∈ C)
    (htranslate : ∀ (a : A) {f}, f ∈ C → wordRightTranslate [a] f ∈ C) :
    ∃ L : ℝ, Tendsto (uniformIidWordCesaro q) atTop (𝓝 L) := by
  obtain ⟨a, ha⟩ :=
    exists_tendsto_birkhoffAverage_of_compact_convex_invariant
      (uniformLetterAverage (A := A))
      (uniformLetterAverage_lipschitz (A := A)) q C hCcompact hCconvex hq
      (mapsTo_uniformLetterAverage C hCconvex htranslate)
  refine ⟨a [], ?_⟩
  have heval :=
    ((BoundedContinuousFunction.evalCLM ℝ ([] : List A)).continuous.continuousAt.tendsto).comp ha
  simpa only [Function.comp_def, BoundedContinuousFunction.evalCLM_apply,
    birkhoffAverage_apply_empty_eq_uniformIidWordCesaro] using heval

end Words

end IndependentZeroBlocks
