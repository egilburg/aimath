import SierpinskiFormal.ModuleBlockAtomicLaw
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! # Exact expectations over the common initial block gap -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter MeasureTheory Set Topology
open scoped BigOperators
namespace IndependentZeroBlocks

variable {A : Type*} [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype A] [DecidableEq A] [Nonempty A]
  [TopologicalSpace A] [DiscreteTopology A] [BorelSpace A]

theorem iid_initialBlockGap_law (P : FiniteProbabilityWeights A)
    (ell : ℕ) (hell : 0 < ell) (e : Fin ell → A)
    (he : 0 < (P.blockLaw ell).weight e) :
    P.iidMeasure.map (fun ω ↦ initialMarkerGap e (iidBlockPath ell ω)) =
      Measure.sum (fun u : GapWords e ↦
        ENNReal.ofReal ((P.blockLaw ell).weight e *
          wordWeight (P.blockLaw ell).weight u.1) • Measure.dirac u) := by
  rw [show (fun ω ↦ initialMarkerGap e (iidBlockPath ell ω)) =
      initialMarkerGap e ∘ iidBlockPath ell from rfl,
    ← Measure.map_map (measurable_initialMarkerGap e) (measurable_iidBlockPath ell),
    (measurePreserving_iidBlockPath P ell hell).map_eq]
  rw [map_eq_countable_boundary_mixture (P.blockLaw ell).iidMeasure (initialMarkerGap e) id
    (initialMarkerGap e) (measurable_initialMarkerGap e) Filter.EventuallyEq.rfl]
  simp only [iidMeasure_initialMarkerGap (P.blockLaw ell) e he, id_eq]

theorem integral_initialBlockGap (P : FiniteProbabilityWeights A)
    (ell : ℕ) (hell : 0 < ell) (e : Fin ell → A)
    (he : 0 < (P.blockLaw ell).weight e) (F : GapWords e → ℂ) :
    (∫ ω, F (initialMarkerGap e (iidBlockPath ell ω)) ∂P.iidMeasure) =
      ∑' u : GapWords e, ((P.blockLaw ell).weight e *
        wordWeight (P.blockLaw ell).weight u.1 : ℝ) • F u := by
  have hU : Measurable (fun ω : ℕ → A ↦ initialMarkerGap e (iidBlockPath ell ω)) :=
    (measurable_initialMarkerGap e).comp (measurable_iidBlockPath ell)
  rw [← integral_map (μ := P.iidMeasure) hU.aemeasurable
      (measurable_of_countable F).aestronglyMeasurable,
    iid_initialBlockGap_law P ell hell e he,
    integral_sum_dirac (fun _ ↦ ENNReal.ofReal_ne_top)]
  apply tsum_congr
  intro u
  rw [ENNReal.toReal_ofReal (mul_nonneg he.le
    (wordWeight_nonneg _ (P.blockLaw ell).nonneg u.1))]

theorem joint_initialBlockGap_law {J : Type*} [Fintype J]
    (P : FiniteProbabilityWeights A) (ell : ℕ) (hell : 0 < ell)
    (e : Fin ell → A) (he : 0 < (P.blockLaw ell).weight e)
    (D : J → GapWords e → ℝ) :
    P.iidMeasure.map (fun ω j ↦ D j (initialMarkerGap e (iidBlockPath ell ω))) =
      Measure.sum (fun u : GapWords e ↦
        ENNReal.ofReal ((P.blockLaw ell).weight e * wordWeight (P.blockLaw ell).weight u.1) •
          Measure.dirac (fun j ↦ D j u)) := by
  let F : GapWords e → (J → ℝ) := fun u j ↦ D j u
  have hF : Measurable F := measurable_of_countable F
  have hU : Measurable (fun ω : ℕ → A ↦ initialMarkerGap e (iidBlockPath ell ω)) :=
    (measurable_initialMarkerGap e).comp (measurable_iidBlockPath ell)
  rw [show (fun ω j ↦ D j (initialMarkerGap e (iidBlockPath ell ω))) =
      F ∘ (fun ω ↦ initialMarkerGap e (iidBlockPath ell ω)) from rfl,
    ← Measure.map_map hF hU, iid_initialBlockGap_law P ell hell e he,
    Measure.map_sum hF.aemeasurable]
  congr 1
  funext u
  rw [Measure.map_smul, Measure.map_dirac]

end IndependentZeroBlocks
