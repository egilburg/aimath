import SierpinskiFormal.BlockAnalyticTransforms
import SierpinskiFormal.BlockGapExpectation
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! # Analytic transforms equal expectations under the actual IID path law -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter MeasureTheory Set Topology
open scoped BigOperators BoundedContinuousFunction
namespace IndependentZeroBlocks

variable {A J : Type*} [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype A] [DecidableEq A] [Nonempty A]
  [TopologicalSpace A] [DiscreteTopology A] [BorelSpace A] [Fintype J]

theorem blockMixtureFunctional_eq_integral (P : FiniteProbabilityWeights A)
    (hp : ∀ a, 0 < P.weight a) (h : List A) (hh : h ≠ [])
    (f : List (NonMarkerBlock h) →ᵇ ℂ) :
    blockMixtureFunctional h (fun a ↦ (P.weight a : ℂ)) f =
      ∫ ω, f (subtypeListOfGap h (initialMarkerGap (endoMarkerBlock h)
        (iidBlockPath h.length ω))) ∂P.iidMeasure := by
  unfold blockMixtureFunctional
  rw [Sierpinski.wordMixtureFunctional_apply _ _
    (finiteL1Norm_nonMarkerBlock_ofReal_lt_one P.weight hp P.sum_eq_one h)]
  rw [integral_initialBlockGap P h.length (List.length_pos_iff.mpr hh) (endoMarkerBlock h)
    (blockLaw_weight_pos P hp h.length _) (fun u ↦ f (subtypeListOfGap h u))]
  rw [← (nonMarkerListEquivGap h).tsum_eq
    (fun u : GapWords (endoMarkerBlock h) ↦
      ((P.blockLaw h.length).weight (endoMarkerBlock h) *
        wordWeight (P.blockLaw h.length).weight u.1 : ℝ) • f (subtypeListOfGap h u))]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro u
  have hu : subtypeListOfGap h ((nonMarkerListEquivGap h) u) = u :=
    (nonMarkerListEquivGap h).symm_apply_apply u
  rw [hu]
  rw [← complexWordWeight_gapOfSubtypeList]
  have hweight : complexBlockWeight (fun a ↦ (P.weight a : ℂ)) h =
      (fun c ↦ (blockWeight P.weight h.length c : ℂ)) :=
    funext (complexBlockWeight_ofReal P.weight h)
  rw [hweight, complexWordWeight_ofReal]
  change (blockWeight P.weight h.length (endoMarkerBlock h) : ℂ) *
      ((wordWeight (R := ℝ) (blockWeight P.weight h.length) (gapOfSubtypeList h u).1 : ℂ) * f u) =
    ((blockWeight P.weight h.length (endoMarkerBlock h) *
      wordWeight (blockWeight P.weight h.length) (gapOfSubtypeList h u).1 : ℝ) : ℂ) * f u
  rw [Complex.ofReal_mul, mul_assoc]

theorem bounded_eval_exp {I : Type*} [TopologicalSpace I]
    (f : I →ᵇ ℂ) (u : I) :
    (NormedSpace.exp f) u = Complex.exp (f u) := by
  let ev : (I →ᵇ ℂ) →+* ℂ :=
    { toFun := fun g ↦ g u
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have hev : Continuous ev := (BoundedContinuousFunction.evalCLM ℂ u).continuous
  simpa only [ev, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, ← Complex.exp_eq_exp_ℂ] using
    NormedSpace.map_exp ev hev f

theorem blockComplexMixedMoment_eq_integral (P : FiniteProbabilityWeights A)
    (hp : ∀ a, 0 < P.weight a) (h : List A) (hh : h ≠ [])
    (m : J → BlockBranchCoefficients h)
    (hm : ∀ j s ξ u v, (m j s ξ u v : ℝ) ∈ Icc (0 : ℝ) 1) (k : J → ℕ) :
    blockComplexMixedMoment h m hm k (fun a ↦ (P.weight a : ℂ)) =
      ∫ ω, ((∏ j, blockMarkerBranch h.length (endoMarkerBlock h) (m j) P.weight
        (initialMarkerGap (endoMarkerBlock h) (iidBlockPath h.length ω)) ^ k j : ℝ) : ℂ) ∂P.iidMeasure := by
  rw [blockComplexMixedMoment, blockMixtureFunctional_eq_integral P hp h hh]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ω
  have hu : gapOfSubtypeList h (subtypeListOfGap h
      (initialMarkerGap (endoMarkerBlock h) (iidBlockPath h.length ω))) =
      initialMarkerGap (endoMarkerBlock h) (iidBlockPath h.length ω) :=
    (nonMarkerListEquivGap h).apply_symm_apply _
  simp only [BoundedContinuousFunction.prod_apply, BoundedContinuousFunction.pow_apply,
    uniformBlockBranch_ofReal h _ _ P.weight hp P.sum_eq_one, hu,
    Complex.ofReal_prod, Complex.ofReal_pow]

theorem blockComplexExpTransform_eq_integral (P : FiniteProbabilityWeights A)
    (hp : ∀ a, 0 < P.weight a) (h : List A) (hh : h ≠ [])
    (m : J → BlockBranchCoefficients h)
    (hm : ∀ j s ξ u v, (m j s ξ u v : ℝ) ∈ Icc (0 : ℝ) 1) (t : J → ℂ) :
    blockComplexExpTransform h m hm (fun a ↦ (P.weight a : ℂ)) t =
      ∫ ω, Complex.exp (∑ j, t j *
        (blockMarkerBranch h.length (endoMarkerBlock h) (m j) P.weight
          (initialMarkerGap (endoMarkerBlock h) (iidBlockPath h.length ω)) : ℂ)) ∂P.iidMeasure := by
  rw [blockComplexExpTransform, blockMixtureFunctional_eq_integral P hp h hh]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ω
  have hu : gapOfSubtypeList h (subtypeListOfGap h
      (initialMarkerGap (endoMarkerBlock h) (iidBlockPath h.length ω))) =
      initialMarkerGap (endoMarkerBlock h) (iidBlockPath h.length ω) :=
    (nonMarkerListEquivGap h).apply_symm_apply _
  simp only [bounded_eval_exp, BoundedContinuousFunction.sum_apply,
    BoundedContinuousFunction.smul_apply, smul_eq_mul,
    uniformBlockBranch_ofReal h _ _ P.weight hp P.sum_eq_one, hu]

def normalizedIIDLaw (p : A → ℝ) (hp : ∀ a, 0 < p a) : FiniteProbabilityWeights A where
  weight := normalizedRealWeights p
  nonneg a := (normalizedRealWeights_pos p hp a).le
  sum_eq_one := sum_normalizedRealWeights p hp

theorem normalizedBlockMixedMoment_eq_integral (h : List A) (hh : h ≠ [])
    (m : J → BlockBranchCoefficients h)
    (hm : ∀ j s ξ u v, (m j s ξ u v : ℝ) ∈ Icc (0 : ℝ) 1)
    (k : J → ℕ) (p : A → ℝ) (hp : ∀ a, 0 < p a) :
    normalizedBlockMixedMoment h m hm k p =
      ∫ ω, ∏ j, normalizedBlockBranch h (m j) (hm j) p
        (initialMarkerGap (endoMarkerBlock h) (iidBlockPath h.length ω)) ^ k j
        ∂(normalizedIIDLaw p hp).iidMeasure := by
  unfold normalizedBlockMixedMoment
  rw [normalizedComplexWeights_complexify]
  change (blockComplexMixedMoment h m hm k (fun a ↦ (normalizedRealWeights p a : ℂ))).re = _
  have he := blockComplexMixedMoment_eq_integral (normalizedIIDLaw p hp)
    (normalizedRealWeights_pos p hp) h hh m hm k
  rw [integral_complex_ofReal] at he
  have hr := congrArg Complex.re he
  simpa only [normalizedIIDLaw, Complex.ofReal_re, normalizedBlockBranch_eq h _ _ p hp] using hr

end IndependentZeroBlocks
