import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

/-! # Conditioning a finite observed parameter and a family of future values -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace IndependentZeroBlocks

variable {Ω I : Type*} [m₀ : MeasurableSpace Ω]
  [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem condExp_finite_parameter {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    (X : Ω → I) (hX : Measurable[m] X)
    (Y : I → Ω → ℝ) (c : I → ℝ)
    (hY : ∀ i, Integrable (Y i) μ)
    (hcond : ∀ i, μ[Y i | m] =ᵐ[μ] fun _ ↦ c i) :
    μ[fun ω ↦ Y (X ω) ω | m] =ᵐ[μ] fun ω ↦ c (X ω) := by
  classical
  let s : I → Set Ω := fun i ↦ X ⁻¹' {i}
  let f : I → Ω → ℝ := fun i ↦ (s i).indicator (Y i)
  have hs (i : I) : MeasurableSet[m] (s i) := hX (measurableSet_singleton i)
  have hfi (i : I) : Integrable (f i) μ := (hY i).indicator (hm _ (hs i))
  have hsum : (∑ i, f i) = (fun ω ↦ Y (X ω) ω) := by
    funext ω
    simp [f, s, Set.indicator]
  have hci (i : I) : μ[f i | m] =ᵐ[μ] (s i).indicator (fun _ ↦ c i) := by
    exact (condExp_indicator (hY i) (hs i)).trans (hcond i).indicator
  rw [← hsum]
  apply (condExp_finsetSum (fun i _ ↦ hfi i) m).trans
  have hall : ∀ᵐ ω ∂μ, ∀ i, (μ[f i | m]) ω = (s i).indicator (fun _ ↦ c i) ω :=
    ae_all_iff.mpr hci
  filter_upwards [hall] with ω hω
  simp only [Finset.sum_apply]
  simp [hω, s, Set.indicator]

end IndependentZeroBlocks
