import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.AEMeasurable

/-! # The distribution of a countably indexed pathwise boundary value

This is only the measure-theoretic transfer. Its application must establish
the actual boundary variable and the almost-sure pathwise identity.
-/

noncomputable section
open MeasureTheory

namespace IndependentZeroBlocks

variable {Ω I Y : Type*} [MeasurableSpace Ω] [MeasurableSpace I]
  [Countable I] [MeasurableSingletonClass I]
  [MeasurableSpace Y] [MeasurableSingletonClass Y]

/-- Equal branch values automatically merge under the Dirac mixture. The
index need not be recoverable from the observed limit. -/
theorem map_eq_countable_boundary_mixture
    (μ : Measure Ω) (U : Ω → I) (D : I → Y) (L : Ω → Y)
    (hU : Measurable U) (hL : L =ᵐ[μ] fun ω ↦ D (U ω)) :
    μ.map L = Measure.sum (fun i ↦ μ (U ⁻¹' {i}) • Measure.dirac (D i)) := by
  have hD : Measurable D := measurable_of_countable D
  rw [Measure.map_congr hL]
  change μ.map (D ∘ U) = _
  rw [← Measure.map_map hD hU, Measure.map_eq_sum μ U hU,
    Measure.map_sum hD.aemeasurable]
  congr 1
  funext i
  rw [Measure.map_smul, Measure.map_dirac]

end IndependentZeroBlocks
