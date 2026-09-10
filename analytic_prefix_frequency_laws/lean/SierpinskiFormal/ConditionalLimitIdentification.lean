import Mathlib.Probability.Martingale.Convergence

/-! # Identifying a pathwise limit from conditional averages

This interface separates the probability argument from the algebraic boundary
calculation. The conditional averages of the original bounded observables must
be proved to converge; determination of the pathwise limit is a conclusion.
-/

noncomputable section
open Filter MeasureTheory Topology

namespace IndependentZeroBlocks

variable {Ω : Type*} [m₀ : MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A bounded a.s. limit commutes with conditioning when the conditional
averages have a specified bounded measurable pointwise limit. -/
theorem conditional_limit_identification
    {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    (f : ℕ → Ω → ℝ) (L g : Ω → ℝ) (C : ℝ)
    (hf : ∀ N, Integrable (f N) μ)
    (hfb : ∀ N, ∀ᵐ ω ∂μ, ‖f N ω‖ ≤ C)
    (hL : ∀ᵐ ω ∂μ, Tendsto (fun N ↦ f N ω) atTop (𝓝 (L ω)))
    (hg : StronglyMeasurable[m] g) (hgi : Integrable g μ)
    (hcond : ∀ᵐ ω ∂μ,
      Tendsto (fun N ↦ (μ[f N | m]) ω) atTop (𝓝 (g ω))) :
    μ[L | m] =ᵐ[μ] g := by
  have hcb (N : ℕ) : ∀ᵐ ω ∂μ, ‖(μ[f N | m]) ω‖ ≤ C :=
    ae_bdd_norm_condExp_of_ae_bdd_norm (hfb N)
  have heq : μ[L | m] =ᵐ[μ] μ[g | m] := by
    apply tendsto_condExp_unique f (fun N ↦ μ[f N | m]) L g hf
      (fun _ ↦ integrable_condExp) hL hcond
      (fun _ ↦ C) (integrable_const C) (fun _ ↦ C) (integrable_const C)
      hfb hcb
    intro N
    exact (condExp_condExp_of_le (μ := μ) (f := f N) (le_refl m) hm).symm
  exact heq.trans (condExp_of_stronglyMeasurable hm hg hgi).eventuallyEq

/-- Conditional finite-prefix calculations determine the actual pathwise
limit, provided the filtration generates all events and the calculated
conditional limits themselves converge. No determinism of `L` is assumed. -/
theorem pathwise_limit_of_conditional_averages
    (ℱ : Filtration ℕ m₀) (hgenerate : (⨆ n, ℱ n) = m₀)
    (f : ℕ → Ω → ℝ) (L B : Ω → ℝ) (g : ℕ → Ω → ℝ) (C : ℝ)
    (hf : ∀ N, Integrable (f N) μ)
    (hfb : ∀ N, ∀ᵐ ω ∂μ, ‖f N ω‖ ≤ C)
    (hLi : Integrable L μ) (hLm : StronglyMeasurable L)
    (hL : ∀ᵐ ω ∂μ, Tendsto (fun N ↦ f N ω) atTop (𝓝 (L ω)))
    (hgm : ∀ n, StronglyMeasurable[ℱ n] (g n))
    (hgi : ∀ n, Integrable (g n) μ)
    (hcond : ∀ n, ∀ᵐ ω ∂μ,
      Tendsto (fun N ↦ (μ[f N | ℱ n]) ω) atTop (𝓝 (g n ω)))
    (hB : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ g n ω) atTop (𝓝 (B ω))) :
    L =ᵐ[μ] B := by
  have heq : ∀ᵐ ω ∂μ, ∀ n, (μ[L | ℱ n]) ω = g n ω :=
    ae_all_iff.mpr fun n ↦ conditional_limit_identification (ℱ.le n)
      f L (g n) C hf hfb hL (hgm n) (hgi n) (hcond n)
  have hLm' : StronglyMeasurable[⨆ n, ℱ n] L := by rwa [hgenerate]
  filter_upwards [hLi.tendsto_ae_condExp hLm', heq, hB] with ω hω heω hBω
  exact tendsto_nhds_unique (hω.congr (fun n ↦ heω n)) hBω

end IndependentZeroBlocks
