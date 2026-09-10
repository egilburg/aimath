import SierpinskiFormal.StationaryBooleanMean
import SierpinskiFormal.CommonContextLogDensity

/-! # Actual prefix frequencies and the expectation of their random limit

This scalar interface evaluates the accepted contextual stationary theorem at
the empty word. The limit need not be constant. Bounded convergence identifies
its mean with any independently established limit of the expected frequencies.
-/

noncomputable section
open Filter Set MeasureTheory Topology
open scoped BigOperators

namespace IndependentZeroBlocks

variable {Ω A : Type*}

/-- The average of a Boolean event on chronological prefixes of one sample. -/
def stationaryBooleanFrequency (letter : Ω → A) (T : Ω → Ω)
    (q : List A → Bool) (N : ℕ) (x : Ω) : ℝ :=
  realCesaroMean (fun n ↦ boolIndicator (q (stationaryPrefix letter T n x))) N

theorem stationaryBooleanFrequency_mem_Icc (letter : Ω → A) (T : Ω → Ω)
    (q : List A → Bool) (N : ℕ) (x : Ω) :
    stationaryBooleanFrequency letter T q N x ∈ Icc (0 : ℝ) 1 := by
  have hb (w : List A) : boolIndicator (q w) ∈ Icc (0 : ℝ) 1 := by
    cases q w <;> norm_num [boolIndicator]
  refine ⟨realCesaroMean_nonneg (fun n ↦ (hb _).1) N, ?_⟩
  by_cases hN : N = 0
  · simp [stationaryBooleanFrequency, realCesaroMean, hN]
  · exact realCesaroMean_le_one (fun n ↦ (hb _).2) (Nat.pos_of_ne_zero hN)

section Stationary

variable [MeasurableSpace Ω] [TopologicalSpace A] [DiscreteTopology A]
  [Fintype A] [Nonempty A] [DecidableEq A]
  [MeasurableSpace A] [MeasurableSingletonClass A] [BorelSpace A]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [MeasurableSpace Ω] [Fintype A] [Nonempty A] [DecidableEq A]
  [MeasurableSpace A] [MeasurableSingletonClass A] [BorelSpace A] in
theorem stationaryBooleanFrequency_eq_contextual (letter : Ω → A) (T : Ω → Ω)
    (q : List A → Bool) (N : ℕ) (x : Ω) :
    stationaryBooleanFrequency letter T q N x =
      stationaryWordCesaro letter T (booleanWordIndicator q) N x [] := by
  simp [stationaryBooleanFrequency, stationaryWordCesaro_apply,
    realCesaroMean, div_eq_mul_inv, mul_comm]

theorem stationaryBooleanFrequency_aestronglyMeasurable
    (letter : Ω → A) (hletter : Measurable letter)
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (q : List A → Bool) (N : ℕ) :
    AEStronglyMeasurable (stationaryBooleanFrequency letter T q N) μ := by
  have hm := (BoundedContinuousFunction.evalCLM ℝ ([] : List A)).continuous.comp_aestronglyMeasurable
    (stationaryWordCesaro_aestronglyMeasurable letter hletter T hT
      (booleanWordIndicator q) N)
  simpa only [Function.comp_def, BoundedContinuousFunction.evalCLM_apply,
    ← stationaryBooleanFrequency_eq_contextual] using hm

theorem integrable_stationaryBooleanFrequency
    (letter : Ω → A) (hletter : Measurable letter)
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (q : List A → Bool) (N : ℕ) :
    Integrable (stationaryBooleanFrequency letter T q N) μ := by
  apply (integrable_const (1 : ℝ)).mono'
    (stationaryBooleanFrequency_aestronglyMeasurable letter hletter T hT q N)
  exact Eventually.of_forall fun x ↦ by
    have hx := stationaryBooleanFrequency_mem_Icc letter T q N x
    simpa [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2

/-- Stable Boolean prefix events have an integrable, potentially random limit.
The scalar averages converge almost surely and in L1, and their expectations
converge to the expectation of that same limit. -/
theorem exists_stationaryBooleanFrequency_limit
    (letter : Ω → A) (hletter : Measurable letter)
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (q : List A → Bool)
    (hDLP : HasBooleanDoubleLimitProperty (fun w z ↦ q (z ++ w))) :
    ∃ L : Ω → ℝ, Integrable L μ ∧
      (∀ᵐ x ∂μ, L x ∈ Icc (0 : ℝ) 1) ∧
      (∀ᵐ x ∂μ, Tendsto (fun N ↦ stationaryBooleanFrequency letter T q N x)
        atTop (𝓝 (L x))) ∧
      Tendsto (fun N ↦ ∫ x, ‖stationaryBooleanFrequency letter T q N x - L x‖ ∂μ)
        atTop (𝓝 0) ∧
      Tendsto (fun N ↦ ∫ x, stationaryBooleanFrequency letter T q N x ∂μ)
        atTop (𝓝 (∫ x, L x ∂μ)) := by
  obtain ⟨a, _, ha⟩ := exists_stationaryBooleanWordCesaro_mean_and_ae_limit
    letter hletter T hT q hDLP
  let L : Ω → ℝ := fun x ↦ a x []
  have hLm : AEStronglyMeasurable L μ :=
    (BoundedContinuousFunction.evalCLM ℝ ([] : List A)).continuous.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable a)
  have hpoint : ∀ᵐ x ∂μ, Tendsto
      (fun N ↦ stationaryBooleanFrequency letter T q N x) atTop (𝓝 (L x)) := by
    filter_upwards [ha] with x hx
    simpa only [Function.comp_def, BoundedContinuousFunction.evalCLM_apply,
      ← stationaryBooleanFrequency_eq_contextual] using
      ((BoundedContinuousFunction.evalCLM ℝ ([] : List A)).continuous.tendsto (a x)).comp hx
  have hIcc : ∀ᵐ x ∂μ, L x ∈ Icc (0 : ℝ) 1 := by
    filter_upwards [hpoint] with x hx
    exact isClosed_Icc.mem_of_tendsto hx (Eventually.of_forall fun N ↦
      stationaryBooleanFrequency_mem_Icc letter T q N x)
  have hLb : ∀ᵐ x ∂μ, ‖L x‖ ≤ (1 : ℝ) := by
    filter_upwards [hIcc] with x hx
    simpa [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2
  have hLi : Integrable L μ := (integrable_const (1 : ℝ)).mono' hLm hLb
  have hfm (N : ℕ) := stationaryBooleanFrequency_aestronglyMeasurable
    letter hletter T hT q N
  have hfb (N : ℕ) : ∀ᵐ x ∂μ,
      ‖stationaryBooleanFrequency letter T q N x‖ ≤ (1 : ℝ) :=
    Eventually.of_forall fun x ↦ by
      have hx := stationaryBooleanFrequency_mem_Icc letter T q N x
      simpa [Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2
  refine ⟨L, hLi, hIcc, hpoint, ?_, ?_⟩
  · have hdm (N : ℕ) := ((hfm N).sub hLm).norm
    have hdb (N : ℕ) : ∀ᵐ x ∂μ,
        ‖‖stationaryBooleanFrequency letter T q N x - L x‖‖ ≤ (2 : ℝ) := by
      filter_upwards [hfb N, hLb] with x hx hLx
      rw [norm_norm]
      exact (norm_sub_le _ _).trans (by linarith)
    have hzero : ∀ᵐ x ∂μ, Tendsto
        (fun N ↦ ‖stationaryBooleanFrequency letter T q N x - L x‖)
        atTop (𝓝 0) := by
      filter_upwards [hpoint] with x hx
      simpa using (hx.sub_const (L x)).norm
    simpa using tendsto_integral_of_dominated_convergence
      (fun _ : Ω ↦ (2 : ℝ)) hdm (integrable_const _) hdb hzero
  · exact tendsto_integral_of_dominated_convergence
      (fun _ : Ω ↦ (1 : ℝ)) hfm (integrable_const _) hfb hpoint

end Stationary
end IndependentZeroBlocks
