import SierpinskiFormal.StationaryFiberMeasures
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Barycenters of countable fiber measures

The Radon--Nikodym weights of a countable fiber decomposition define an
almost-everywhere convex barycenter.  This file establishes measurability,
integrability, norm and convex-hull control, and scalar product-test formulas.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal BigOperators

namespace IndependentZeroBlocks
section CountableFiberBarycenter

variable {X K E : Type*} [MeasurableSpace X] [MeasurableSpace K]
  [MeasurableSingletonClass K] [Countable K]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The pointwise barycenter obtained from the Radon--Nikodym weights of the
countable fibers of `ν`. -/
noncomputable def countableFiberBarycenter
    (ν : Measure (X × K)) (μ : Measure X) (j : K → E) : X → E :=
  fun x => ∑' k : K, (countableFiberDensity ν μ k x).toReal • j k

/-- For a bounded `j`, the series defining the countable-fiber barycenter is
summable almost everywhere. -/
theorem summable_countableFiberBarycenter_ae
    (ν : Measure (X × K)) [IsFiniteMeasure ν]
    (μ : Measure X) [SigmaFinite μ] (hν : ν.fst = μ)
    (j : K → E) (C : ℝ) (hj : ∀ k, ‖j k‖ ≤ C) :
    ∀ᵐ x ∂μ, Summable
      (fun k : K => (countableFiberDensity ν μ k x).toReal • j k) := by
  filter_upwards [tsum_countableFiberDensity_eq_one_ae ν μ hν] with x hx
  have hs : Summable
      (fun k : K => (countableFiberDensity ν μ k x).toReal) := by
    apply ENNReal.summable_toReal
    rw [hx]
    exact ENNReal.one_ne_top
  apply Summable.of_norm_bounded (hs.mul_right C)
  intro k
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  exact mul_le_mul_of_nonneg_left (hj k) ENNReal.toReal_nonneg

/-- The countable-fiber barycenter is strongly measurable modulo `μ`.
Finite partial sums converge almost everywhere because the RN weights sum to
one. -/
theorem aestronglyMeasurable_countableFiberBarycenter
    (ν : Measure (X × K)) [IsFiniteMeasure ν]
    (μ : Measure X) [SigmaFinite μ] (hν : ν.fst = μ)
    (j : K → E) (C : ℝ) (hj : ∀ k, ‖j k‖ ≤ C) :
    AEStronglyMeasurable (countableFiberBarycenter ν μ j) μ := by
  let term : K → X → E := fun k x =>
    (countableFiberDensity ν μ k x).toReal • j k
  let partialSum : Finset K → X → E :=
    fun s x => ∑ k ∈ s, term k x
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (f := partialSum) (g := countableFiberBarycenter ν μ j)
  · intro s
    exact s.aestronglyMeasurable_fun_sum fun k _ =>
      (measurable_countableFiberDensity ν μ k).ennreal_toReal
        |>.aestronglyMeasurable.smul_const _
  · filter_upwards
      [summable_countableFiberBarycenter_ae ν μ hν j C hj] with x hx
    exact hx.hasSum

omit [CompleteSpace E] in
/-- A bounded fiber map gives the same almost-everywhere norm bound on its
barycenter. -/
theorem norm_countableFiberBarycenter_le_ae
    (ν : Measure (X × K)) [IsFiniteMeasure ν]
    (μ : Measure X) [SigmaFinite μ] (hν : ν.fst = μ)
    (j : K → E) (C : ℝ) (hj : ∀ k, ‖j k‖ ≤ C) :
    ∀ᵐ x ∂μ, ‖countableFiberBarycenter ν μ j x‖ ≤ C := by
  filter_upwards [tsum_countableFiberDensity_eq_one_ae ν μ hν] with x hx
  simp only [Pi.one_apply] at hx
  let a : K → ℝ := fun k => (countableFiberDensity ν μ k x).toReal
  let term : K → E := fun k => a k • j k
  have hatop : ∑' k : K, countableFiberDensity ν μ k x ≠ ∞ := by
    rw [hx]
    exact ENNReal.one_ne_top
  have ha : Summable a := ENNReal.summable_toReal hatop
  have hag : Summable (fun k : K => a k * C) := ha.mul_right C
  have hterm : ∀ k : K, ‖term k‖ ≤ a k * C := by
    intro k
    dsimp [term, a]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact mul_le_mul_of_nonneg_left (hj k) ENNReal.toReal_nonneg
  have hnorm : Summable (fun k : K => ‖term k‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hag
  have hatsum : ∑' k : K, a k = 1 := by
    change (∑' k : K, (countableFiberDensity ν μ k x).toReal) = 1
    rw [← ENNReal.tsum_toReal_eq
      (ENNReal.ne_top_of_tsum_ne_top hatop), hx, ENNReal.toReal_one]
  calc
    ‖countableFiberBarycenter ν μ j x‖ = ‖∑' k : K, term k‖ := rfl
    _ ≤ ∑' k : K, ‖term k‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' k : K, a k * C := hnorm.tsum_le_tsum hterm hag
    _ = (∑' k : K, a k) * C := ha.tsum_mul_right C
    _ = C := by rw [hatsum, one_mul]

end CountableFiberBarycenter

section BarycenterHull

variable {X K E : Type*} [MeasurableSpace X] [MeasurableSpace K]
  [MeasurableSingletonClass K] [Countable K]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The discrete measure with prescribed nonnegative real singleton
weights. -/
noncomputable def countableWeightMeasure (a : K → ℝ) : Measure K :=
  Measure.sum (fun k : K ↦ ENNReal.ofReal (a k) • Measure.dirac k)

theorem countableWeightMeasure_isProbability
    (a : K → ℝ) (ha : ∀ k, 0 ≤ a k) (hsum : ∑' k : K, a k = 1) :
    IsProbabilityMeasure (countableWeightMeasure a) := by
  have hasum : Summable a := by
    by_contra hn
    have hz := tsum_eq_zero_of_not_summable hn
    rw [hsum] at hz
    norm_num at hz
  constructor
  simp only [countableWeightMeasure, Measure.sum_apply _ MeasurableSet.univ,
    Measure.smul_apply, Measure.dirac_apply' _ MeasurableSet.univ,
    Set.indicator_of_mem (Set.mem_univ _), Pi.one_apply, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg ha hasum]
  simp [hsum]

theorem integral_countableWeightMeasure_eq_tsum
    (a : K → ℝ) (ha : ∀ k, 0 ≤ a k) (hsum : ∑' k : K, a k = 1)
    (j : K → E) (C : ℝ) (hj : ∀ k, ‖j k‖ ≤ C) :
    ∫ k, j k ∂countableWeightMeasure a = ∑' k : K, a k • j k := by
  letI : IsProbabilityMeasure (countableWeightMeasure a) :=
    countableWeightMeasure_isProbability a ha hsum
  have hjint : Integrable j (countableWeightMeasure a) := by
    refine ⟨AEStronglyMeasurable.of_discrete,
      HasFiniteIntegral.of_bounded (C := C) ?_⟩
    exact Filter.Eventually.of_forall hj
  change (∫ k, j k ∂Measure.sum
      (fun k : K ↦ ENNReal.ofReal (a k) • Measure.dirac k)) = _
  rw [integral_sum_measure hjint]
  apply tsum_congr
  intro k
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (ha k)]

/-- A countable convex combination belongs to the closed convex hull of its
range. -/
theorem tsum_smul_mem_closedConvexHull_range
    (a : K → ℝ) (ha : ∀ k, 0 ≤ a k) (hsum : ∑' k : K, a k = 1)
    (j : K → E) (C : ℝ) (hj : ∀ k, ‖j k‖ ≤ C) :
    (∑' k : K, a k • j k) ∈ closedConvexHull ℝ (Set.range j) := by
  letI : IsProbabilityMeasure (countableWeightMeasure a) :=
    countableWeightMeasure_isProbability a ha hsum
  rw [← integral_countableWeightMeasure_eq_tsum a ha hsum j C hj]
  apply (convex_closedConvexHull (𝕜 := ℝ) (s := Set.range j)).integral_mem
    (isClosed_closedConvexHull (𝕜 := ℝ) (s := Set.range j))
  · exact Filter.Eventually.of_forall fun k ↦
      (subset_closedConvexHull (𝕜 := ℝ) (s := Set.range j))
        (Set.mem_range_self k)
  · refine ⟨AEStronglyMeasurable.of_discrete,
      HasFiniteIntegral.of_bounded (C := C) ?_⟩
    exact Filter.Eventually.of_forall hj

/-- The RN barycenter lies in the closed convex hull of the fiber image
almost everywhere. -/
theorem countableFiberBarycenter_mem_closedConvexHull_ae
    (ν : Measure (X × K)) [IsFiniteMeasure ν]
    (μ : Measure X) [SigmaFinite μ] (hν : ν.fst = μ)
    (j : K → E) (C : ℝ) (hj : ∀ k, ‖j k‖ ≤ C) :
    ∀ᵐ x ∂μ,
      countableFiberBarycenter ν μ j x ∈ closedConvexHull ℝ (Set.range j) := by
  filter_upwards [tsum_countableFiberDensityReal_eq_one_ae ν μ hν] with x hx
  exact tsum_smul_mem_closedConvexHull_range
    (fun k ↦ countableFiberDensityReal ν μ k x)
    (fun k ↦ countableFiberDensityReal_nonneg ν μ k x) hx j C hj

/-- On a finite source measure, a bounded countable-fiber barycenter is
Bochner integrable. -/
theorem integrable_countableFiberBarycenter
    (ν : Measure (X × K)) [IsFiniteMeasure ν]
    (μ : Measure X) [SigmaFinite μ] [IsFiniteMeasure μ] (hν : ν.fst = μ)
    (j : K → E) (C : ℝ) (hj : ∀ k, ‖j k‖ ≤ C) :
    Integrable (countableFiberBarycenter ν μ j) μ :=
  ⟨aestronglyMeasurable_countableFiberBarycenter ν μ hν j C hj,
    HasFiniteIntegral.of_bounded
      (norm_countableFiberBarycenter_le_ae ν μ hν j C hj)⟩

/-- The scalar contribution of one RN fiber can be integrated either on the
source or on the corresponding singleton fiber of the product measure. -/
theorem integral_countableFiberDensityReal_mul_eq_integral_restrict_fiber
    (ν : Measure (X × K)) [IsFiniteMeasure ν]
    (μ : Measure X) [SigmaFinite μ] (hν : ν.fst = μ)
    (j : K → E) (φ : E →L[ℝ] ℝ) (a : X → ℝ) (ha : Measurable a)
    (k : K) :
    (∫ x, a x * (countableFiberDensityReal ν μ k x * φ (j k)) ∂μ) =
      ∫ z, a z.1 * φ (j z.2) ∂
        ν.restrict ((Prod.snd : X × K → K) ⁻¹' ({k} : Set K)) := by
  let ξ := ν.restrict ((Prod.snd : X × K → K) ⁻¹' ({k} : Set K))
  letI : IsFiniteMeasure (countableFiberMeasure ν k) := by
    dsimp [countableFiberMeasure]
    infer_instance
  have hlt : ∀ᵐ x ∂μ, countableFiberDensity ν μ k x < ⊤ :=
    Measure.rnDeriv_lt_top (countableFiberMeasure ν k) μ
  have hdensity := withDensity_rnDeriv_countableFiberMeasure hν k
  have hwd := integral_withDensity_eq_integral_toReal_smul
    (measurable_countableFiberDensity ν μ k) hlt
    (fun x ↦ a x * φ (j k))
  have hmap :
      (∫ x, a x * φ (j k) ∂countableFiberMeasure ν k) =
        ∫ z, a z.1 * φ (j k) ∂ξ := by
    rw [countableFiberMeasure, Measure.fst]
    apply MeasureTheory.integral_map measurable_fst.aemeasurable
    exact (ha.mul_const _).aestronglyMeasurable
  calc
    (∫ x, a x * (countableFiberDensityReal ν μ k x * φ (j k)) ∂μ) =
        ∫ x, (countableFiberDensity ν μ k x).toReal •
          (a x * φ (j k)) ∂μ := by
            apply integral_congr_ae
            filter_upwards with x
            simp [countableFiberDensityReal, mul_assoc, mul_comm, mul_left_comm]
    _ = ∫ x, a x * φ (j k) ∂
          μ.withDensity (countableFiberDensity ν μ k) := hwd.symm
    _ = ∫ x, a x * φ (j k) ∂countableFiberMeasure ν k := by
      change (∫ x, a x * φ (j k) ∂
        μ.withDensity ((countableFiberMeasure ν k).rnDeriv μ)) = _
      rw [hdensity]
    _ = ∫ z, a z.1 * φ (j k) ∂ξ := hmap
    _ = ∫ z, a z.1 * φ (j z.2) ∂ξ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem
        ((measurableSet_singleton k).preimage measurable_snd)] with z hz
      have hz' : z.2 = k := by
        simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hz
      rw [hz']

/-- A bounded scalar test multiplied by one fiber weight is integrable. -/
theorem integrable_countableFiberDensityReal_mul
    (ν : Measure (X × K)) [IsFiniteMeasure ν]
    (μ : Measure X) [SigmaFinite μ] (hν : ν.fst = μ)
    (j : K → E) (φ : E →L[ℝ] ℝ) (a : X → ℝ) (ha : Measurable a)
    (A : ℝ) (ha_bound : ∀ x, |a x| ≤ A) (k : K) :
    Integrable
      (fun x => a x * (countableFiberDensityReal ν μ k x * φ (j k))) μ := by
  letI : IsFiniteMeasure (countableFiberMeasure ν k) := by
    dsimp [countableFiberMeasure]
    infer_instance
  have hlt : ∀ᵐ x ∂μ, countableFiberDensity ν μ k x < ⊤ :=
    Measure.rnDeriv_lt_top (countableFiberMeasure ν k) μ
  have hg : Integrable (fun x => a x * φ (j k))
      (countableFiberMeasure ν k) := by
    refine ⟨(ha.mul_const _).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (C := A * |φ (j k)|) ?_⟩
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (ha_bound x) (abs_nonneg _)
  have hg' : Integrable (fun x => a x * φ (j k))
      (μ.withDensity (countableFiberDensity ν μ k)) := by
    change Integrable (fun x => a x * φ (j k))
      (μ.withDensity ((countableFiberMeasure ν k).rnDeriv μ))
    rw [withDensity_rnDeriv_countableFiberMeasure hν k]
    exact hg
  have hweighted := (integrable_withDensity_iff
    (measurable_countableFiberDensity ν μ k) hlt).mp hg'
  apply hweighted.congr
  filter_upwards with x
  simp [countableFiberDensityReal, mul_assoc, mul_comm, mul_left_comm]

end BarycenterHull

section FiberKernelIntegration

variable {X K : Type*} [MeasurableSpace X] [MeasurableSpace K]
  [MeasurableSingletonClass K] [Countable K]

/-- Integrating one weighted scalar fiber on `X` equals integrating the
kernel over the corresponding singleton fiber of `ν`. -/
theorem integral_countableFiberDensityReal_mul_kernel
    (ν : Measure (X × K)) [IsFiniteMeasure ν]
    (μ : Measure X) [SigmaFinite μ] (hν : ν.fst = μ)
    (b : X → K → ℝ) (hb : Measurable fun z : X × K => b z.1 z.2)
    (k : K) :
    (∫ x, countableFiberDensityReal ν μ k x * b x k ∂μ) =
      ∫ z, b z.1 z.2 ∂
        ν.restrict ((Prod.snd : X × K → K) ⁻¹' ({k} : Set K)) := by
  let ξ := ν.restrict ((Prod.snd : X × K → K) ⁻¹' ({k} : Set K))
  letI : IsFiniteMeasure (countableFiberMeasure ν k) := by
    dsimp [countableFiberMeasure]
    infer_instance
  have hbk : Measurable (fun x : X => b x k) :=
    hb.comp (measurable_id.prodMk measurable_const)
  have hlt : ∀ᵐ x ∂μ, countableFiberDensity ν μ k x < ⊤ :=
    Measure.rnDeriv_lt_top (countableFiberMeasure ν k) μ
  have hwd := integral_withDensity_eq_integral_toReal_smul
    (measurable_countableFiberDensity ν μ k) hlt (fun x ↦ b x k)
  have hmap : (∫ x, b x k ∂countableFiberMeasure ν k) =
      ∫ z, b z.1 k ∂ξ := by
    rw [countableFiberMeasure, Measure.fst]
    apply MeasureTheory.integral_map measurable_fst.aemeasurable
    exact hbk.aestronglyMeasurable
  calc
    (∫ x, countableFiberDensityReal ν μ k x * b x k ∂μ) =
        ∫ x, (countableFiberDensity ν μ k x).toReal • b x k ∂μ := by
          apply integral_congr_ae
          filter_upwards with x
          rfl
    _ = ∫ x, b x k ∂μ.withDensity (countableFiberDensity ν μ k) := hwd.symm
    _ = ∫ x, b x k ∂countableFiberMeasure ν k := by
      change (∫ x, b x k ∂
        μ.withDensity ((countableFiberMeasure ν k).rnDeriv μ)) = _
      rw [withDensity_rnDeriv_countableFiberMeasure hν k]
    _ = ∫ z, b z.1 k ∂ξ := hmap
    _ = ∫ z, b z.1 z.2 ∂ξ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem
        ((measurableSet_singleton k).preimage measurable_snd)] with z hz
      have hz' : z.2 = k := by
        simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hz
      rw [hz']

theorem integrable_countableFiberDensityReal_mul_kernel
    (ν : Measure (X × K)) [IsFiniteMeasure ν]
    (μ : Measure X) [SigmaFinite μ] (hν : ν.fst = μ)
    (b : X → K → ℝ) (hb : Measurable fun z : X × K => b z.1 z.2)
    (B : ℝ) (hb_bound : ∀ x k, |b x k| ≤ B) (k : K) :
    Integrable (fun x => countableFiberDensityReal ν μ k x * b x k) μ := by
  letI : IsFiniteMeasure (countableFiberMeasure ν k) := by
    dsimp [countableFiberMeasure]
    infer_instance
  have hbk : Measurable (fun x : X => b x k) :=
    hb.comp (measurable_id.prodMk measurable_const)
  have hlt : ∀ᵐ x ∂μ, countableFiberDensity ν μ k x < ⊤ :=
    Measure.rnDeriv_lt_top (countableFiberMeasure ν k) μ
  have hg : Integrable (fun x : X => b x k) (countableFiberMeasure ν k) :=
    ⟨hbk.aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := B)
      (Filter.Eventually.of_forall fun x ↦ by
        simpa only [Real.norm_eq_abs] using hb_bound x k)⟩
  have hg' : Integrable (fun x : X => b x k)
      (μ.withDensity (countableFiberDensity ν μ k)) := by
    change Integrable (fun x : X => b x k)
      (μ.withDensity ((countableFiberMeasure ν k).rnDeriv μ))
    rw [withDensity_rnDeriv_countableFiberMeasure hν k]
    exact hg
  have hweighted := (integrable_withDensity_iff
    (measurable_countableFiberDensity ν μ k) hlt).mp hg'
  apply hweighted.congr
  filter_upwards with x
  simp [countableFiberDensityReal, mul_comm]

/-- Countable-fiber Fubini formula for a bounded measurable scalar kernel. -/
theorem integral_tsum_countableFiberDensityReal_mul_kernel
    (ν : Measure (X × K)) [IsFiniteMeasure ν]
    (μ : Measure X) [SigmaFinite μ] [IsFiniteMeasure μ] (hν : ν.fst = μ)
    (b : X → K → ℝ) (hb : Measurable fun z : X × K => b z.1 z.2)
    (B : ℝ) (hB : 0 ≤ B) (hb_bound : ∀ x k, |b x k| ≤ B) :
    (∫ x, ∑' k : K, countableFiberDensityReal ν μ k x * b x k ∂μ) =
      ∫ z, b z.1 z.2 ∂ν := by
  let term : K → X → ℝ := fun k x =>
    countableFiberDensityReal ν μ k x * b x k
  let partialSum : Finset K → X → ℝ := fun s x => ∑ k ∈ s, term k x
  have htermInt : ∀ k, Integrable (term k) μ := fun k ↦
    integrable_countableFiberDensityReal_mul_kernel ν μ hν b hb B hb_bound k
  have hweights := tsum_countableFiberDensityReal_eq_one_ae ν μ hν
  have hpartialMeas : ∀ s, AEStronglyMeasurable (partialSum s) μ := by
    intro s
    apply s.aestronglyMeasurable_fun_sum
    intro k _
    exact (htermInt k).aestronglyMeasurable
  have hpartialBound : ∀ s, ∀ᵐ x ∂μ, ‖partialSum s x‖ ≤ B := by
    intro s
    filter_upwards [hweights] with x hx
    simp only [Pi.one_apply] at hx
    have hwsum : Summable (fun k : K => countableFiberDensityReal ν μ k x) := by
      by_contra hn
      have hz := tsum_eq_zero_of_not_summable hn
      rw [hx] at hz
      norm_num at hz
    have hpartialWeight :
        ∑ k ∈ s, countableFiberDensityReal ν μ k x ≤ 1 := by
      rw [← hx]
      exact hwsum.sum_le_tsum s
        (fun k _ ↦ countableFiberDensityReal_nonneg ν μ k x)
    calc
      ‖partialSum s x‖ ≤ ∑ k ∈ s, ‖term k x‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ s, countableFiberDensityReal ν μ k x * B := by
        apply Finset.sum_le_sum
        intro k _
        dsimp [term]
        change |countableFiberDensityReal ν μ k x * b x k| ≤ _
        rw [abs_mul,
          abs_of_nonneg (countableFiberDensityReal_nonneg ν μ k x)]
        exact mul_le_mul_of_nonneg_left (hb_bound x k)
          (countableFiberDensityReal_nonneg ν μ k x)
      _ = (∑ k ∈ s, countableFiberDensityReal ν μ k x) * B := by
        rw [Finset.sum_mul]
      _ ≤ 1 * B := mul_le_mul_of_nonneg_right hpartialWeight hB
      _ = B := one_mul B
  have hpartialLimit : ∀ᵐ x ∂μ,
      Tendsto (fun s : Finset K ↦ partialSum s x) atTop
        (nhds (∑' k : K, term k x)) := by
    filter_upwards [hweights] with x hx
    simp only [Pi.one_apply] at hx
    have hw : Summable (fun k : K => countableFiberDensityReal ν μ k x) := by
      by_contra hn
      have hz := tsum_eq_zero_of_not_summable hn
      rw [hx] at hz
      norm_num at hz
    have hs : Summable (fun k : K => term k x) := by
      apply Summable.of_norm_bounded (hw.mul_right B)
      intro k
      dsimp [term]
      rw [abs_mul,
        abs_of_nonneg (countableFiberDensityReal_nonneg ν μ k x)]
      exact mul_le_mul_of_nonneg_left (hb_bound x k)
        (countableFiberDensityReal_nonneg ν μ k x)
    exact hs.hasSum
  have hboundInt : Integrable (fun _ : X => B) μ := integrable_const B
  have hleftLimit := tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (l := (atTop : Filter (Finset K))) (fun _ : X ↦ B)
    (Filter.Eventually.of_forall hpartialMeas)
    (Filter.Eventually.of_forall hpartialBound) hboundInt hpartialLimit
  have hdecomp := restrict_sum_countable_fibers ν
  let ξ : K → Measure (X × K) := fun k ↦
    ν.restrict ((Prod.snd : X × K → K) ⁻¹' ({k} : Set K))
  change ν = Measure.sum ξ at hdecomp
  have hbInt : Integrable (fun z : X × K => b z.1 z.2) ν :=
    ⟨hb.aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := B)
      (Filter.Eventually.of_forall fun z ↦ by
        simpa only [Real.norm_eq_abs] using hb_bound z.1 z.2)⟩
  have hbIntSum : Integrable (fun z : X × K => b z.1 z.2) (Measure.sum ξ) := by
    rw [← hdecomp]
    exact hbInt
  have hright := hasSum_integral_measure hbIntSum
  rw [← hdecomp] at hright
  have hpartialIntegral : (fun s : Finset K => ∫ x, partialSum s x ∂μ) =
      (fun s : Finset K => ∑ k ∈ s, ∫ x, term k x ∂μ) := by
    funext s
    exact integral_finset_sum s (fun k _ ↦ htermInt k)
  have hfiniteIntegrals :
      (fun s : Finset K => ∑ k ∈ s, ∫ x, term k x ∂μ) =
      (fun s : Finset K => ∑ k ∈ s, ∫ z, b z.1 z.2 ∂ξ k) := by
    funext s
    apply Finset.sum_congr rfl
    intro k _
    exact integral_countableFiberDensityReal_mul_kernel ν μ hν b hb k
  rw [hpartialIntegral, hfiniteIntegrals] at hleftLimit
  exact tendsto_nhds_unique hleftLimit hright

end FiberKernelIntegration

section BarycenterPairings

variable {X K E : Type*} [MeasurableSpace X] [MeasurableSpace K]
  [MeasurableSingletonClass K] [Countable K]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Product tests against a fixed continuous linear functional pass through
the countable-fiber barycenter. -/
theorem integral_mul_apply_countableFiberBarycenter_eq
    (ν : Measure (X × K)) [IsFiniteMeasure ν]
    (μ : Measure X) [SigmaFinite μ] [IsFiniteMeasure μ] (hν : ν.fst = μ)
    (j : K → E) (C : ℝ) (hC : 0 ≤ C) (hj : ∀ k, ‖j k‖ ≤ C)
    (φ : E →L[ℝ] ℝ) (a : X → ℝ) (ha : Measurable a)
    (A : ℝ) (hA : 0 ≤ A) (ha_bound : ∀ x, |a x| ≤ A) :
    (∫ x, a x * φ (countableFiberBarycenter ν μ j x) ∂μ) =
      ∫ z, a z.1 * φ (j z.2) ∂ν := by
  let b : X → K → ℝ := fun x k => a x * φ (j k)
  have hb : Measurable (fun z : X × K => b z.1 z.2) := by
    exact (ha.comp measurable_fst).mul
      ((measurable_of_countable (fun k : K => φ (j k))).comp measurable_snd)
  have hφj : ∀ k, |φ (j k)| ≤ ‖φ‖ * C := by
    intro k
    calc
      |φ (j k)| = ‖φ (j k)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖φ‖ * ‖j k‖ := φ.le_opNorm (j k)
      _ ≤ ‖φ‖ * C := mul_le_mul_of_nonneg_left (hj k) (norm_nonneg φ)
  have hb_bound : ∀ x k, |b x k| ≤ A * (‖φ‖ * C) := by
    intro x k
    dsimp [b]
    rw [abs_mul]
    exact mul_le_mul (ha_bound x) (hφj k) (abs_nonneg _) hA
  have hpoint : ∀ᵐ x ∂μ,
      a x * φ (countableFiberBarycenter ν μ j x) =
        ∑' k : K, countableFiberDensityReal ν μ k x * b x k := by
    filter_upwards
      [summable_countableFiberBarycenter_ae ν μ hν j C hj] with x hx
    have hsφ : Summable (fun k : K =>
        φ (countableFiberDensityReal ν μ k x • j k)) :=
      hx.map φ φ.continuous
    calc
      a x * φ (countableFiberBarycenter ν μ j x) =
          a x * ∑' k : K,
            φ (countableFiberDensityReal ν μ k x • j k) := by
              rw [countableFiberBarycenter, φ.map_tsum hx]
              rfl
      _ = ∑' k : K,
          a x * φ (countableFiberDensityReal ν μ k x • j k) :=
            (hsφ.tsum_mul_left (a x)).symm
      _ = ∑' k : K,
          countableFiberDensityReal ν μ k x * b x k := by
            apply tsum_congr
            intro k
            simp only [map_smul, smul_eq_mul]
            dsimp [b]
            ring
  calc
    (∫ x, a x * φ (countableFiberBarycenter ν μ j x) ∂μ) =
        ∫ x, ∑' k : K,
          countableFiberDensityReal ν μ k x * b x k ∂μ :=
      integral_congr_ae hpoint
    _ = ∫ z, b z.1 z.2 ∂ν :=
      integral_tsum_countableFiberDensityReal_mul_kernel ν μ hν b hb
        (A * (‖φ‖ * C))
        (mul_nonneg hA (mul_nonneg (norm_nonneg φ) hC)) hb_bound
    _ = ∫ z, a z.1 * φ (j z.2) ∂ν := rfl

/-- A bounded measurable field of continuous linear functionals pairs with
the fiber barycenter exactly as it pairs with the original product measure.
The explicit kernel-measurability assumption avoids separability assumptions
on the dual space. -/
theorem integral_apply_countableFiberBarycenter_eq
    (ν : Measure (X × K)) [IsFiniteMeasure ν]
    (μ : Measure X) [SigmaFinite μ] [IsFiniteMeasure μ] (hν : ν.fst = μ)
    (j : K → E) (C : ℝ) (hC : 0 ≤ C) (hj : ∀ k, ‖j k‖ ≤ C)
    (η : X → (E →L[ℝ] ℝ))
    (hηkernel : Measurable fun z : X × K => η z.1 (j z.2))
    (D : ℝ) (hD : 0 ≤ D) (hη_bound : ∀ x, ‖η x‖ ≤ D) :
    (∫ x, η x (countableFiberBarycenter ν μ j x) ∂μ) =
      ∫ z, η z.1 (j z.2) ∂ν := by
  let b : X → K → ℝ := fun x k => η x (j k)
  have hb_bound : ∀ x k, |b x k| ≤ D * C := by
    intro x k
    calc
      |b x k| = ‖η x (j k)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖η x‖ * ‖j k‖ := (η x).le_opNorm (j k)
      _ ≤ D * C := mul_le_mul (hη_bound x) (hj k) (norm_nonneg _) hD
  have hpoint : ∀ᵐ x ∂μ,
      η x (countableFiberBarycenter ν μ j x) =
        ∑' k : K, countableFiberDensityReal ν μ k x * b x k := by
    filter_upwards
      [summable_countableFiberBarycenter_ae ν μ hν j C hj] with x hx
    calc
      η x (countableFiberBarycenter ν μ j x) =
          ∑' k : K, η x (countableFiberDensityReal ν μ k x • j k) := by
            rw [countableFiberBarycenter, (η x).map_tsum hx]
            rfl
      _ = ∑' k : K,
          countableFiberDensityReal ν μ k x * b x k := by
            apply tsum_congr
            intro k
            simp [b]
  calc
    (∫ x, η x (countableFiberBarycenter ν μ j x) ∂μ) =
        ∫ x, ∑' k : K,
          countableFiberDensityReal ν μ k x * b x k ∂μ :=
      integral_congr_ae hpoint
    _ = ∫ z, b z.1 z.2 ∂ν :=
      integral_tsum_countableFiberDensityReal_mul_kernel ν μ hν b hηkernel
        (D * C) (mul_nonneg hD hC) hb_bound
    _ = ∫ z, η z.1 (j z.2) ∂ν := rfl

/-- The variable-dual pairing identity with an almost-everywhere operator
norm bound.  The field is truncated to zero on the exceptional set; the
first-marginal identity transports that null set from `μ` to `ν`. -/
theorem integral_apply_countableFiberBarycenter_eq_of_ae_bound
    (ν : Measure (X × K)) [IsFiniteMeasure ν]
    (μ : Measure X) [SigmaFinite μ] [IsFiniteMeasure μ] (hν : ν.fst = μ)
    (j : K → E) (C : ℝ) (hC : 0 ≤ C) (hj : ∀ k, ‖j k‖ ≤ C)
    (η : X → (E →L[ℝ] ℝ)) (hη : StronglyMeasurable η)
    (hηkernel : Measurable fun z : X × K => η z.1 (j z.2))
    (D : ℝ) (hD : 0 ≤ D) (hη_bound : ∀ᵐ x ∂μ, ‖η x‖ ≤ D) :
    (∫ x, η x (countableFiberBarycenter ν μ j x) ∂μ) =
      ∫ z, η z.1 (j z.2) ∂ν := by
  let η' : X → (E →L[ℝ] ℝ) := fun x =>
    if ‖η x‖ ≤ D then η x else 0
  have hnorm : Measurable (fun x => ‖η x‖) := hη.norm.measurable
  have hboundSet : MeasurableSet {x : X | ‖η x‖ ≤ D} :=
    measurableSet_le hnorm measurable_const
  have hη'kernel : Measurable fun z : X × K => η' z.1 (j z.2) := by
    have heq : (fun z : X × K => η' z.1 (j z.2)) =
        (fun z => if ‖η z.1‖ ≤ D then η z.1 (j z.2) else 0) := by
      funext z
      by_cases hz : ‖η z.1‖ ≤ D <;> simp [η', hz]
    rw [heq]
    exact hηkernel.ite (hboundSet.preimage measurable_fst)
      (measurable_const : Measurable (fun _ : X × K => (0 : ℝ)))
  have hη'_bound : ∀ x, ‖η' x‖ ≤ D := by
    intro x
    by_cases hx : ‖η x‖ ≤ D
    · simp [η', hx]
    · simp [η', hx, hD]
  have hη'_eq_η_ae : η' =ᵐ[μ] η := by
    filter_upwards [hη_bound] with x hx
    simp [η', hx]
  have hη'_eq_η_fst_ae :
      (fun z : X × K => η' z.1) =ᵐ[ν] fun z => η z.1 := by
    have hμ : ∀ᵐ x ∂ν.fst, ‖η x‖ ≤ D := by
      rw [hν]
      exact hη_bound
    change ∀ᵐ x ∂Measure.map (Prod.fst : X × K → X) ν,
      ‖η x‖ ≤ D at hμ
    have hνbound := (ae_map_iff measurable_fst.aemeasurable hboundSet).mp hμ
    filter_upwards [hνbound] with z hz
    simp [η', hz]
  have htruncated := integral_apply_countableFiberBarycenter_eq
    ν μ hν j C hC hj η' hη'kernel D hD hη'_bound
  calc
    (∫ x, η x (countableFiberBarycenter ν μ j x) ∂μ) =
        ∫ x, η' x (countableFiberBarycenter ν μ j x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hη'_eq_η_ae] with x hx
      rw [hx]
    _ = ∫ z, η' z.1 (j z.2) ∂ν := htruncated
    _ = ∫ z, η z.1 (j z.2) ∂ν := by
      apply integral_congr_ae
      filter_upwards [hη'_eq_η_fst_ae] with z hz
      rw [hz]

end BarycenterPairings

end IndependentZeroBlocks
