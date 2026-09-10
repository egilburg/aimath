import SierpinskiFormal.GroupFlowAtomic
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Countable probability measures and finite group orbits

This file connects a Borel probability on a countable flow to the atomic
mass-function maximum principle in `GroupFlowAtomic`.
-/

noncomputable section

open scoped BigOperators ENNReal
open Set MeasureTheory

namespace IndependentZeroBlocks

variable {G X D : Type*} [Group G] [MulAction G X]
variable [MeasurableSpace X] [MeasurableSingletonClass X] [Countable X]

/-- The real mass of the singleton atom at `x`. -/
def measureAtomMass (μ : Measure X) (x : X) : ℝ := (μ {x}).toReal

theorem measureAtomMass_nonneg (μ : Measure X) (x : X) :
    0 ≤ measureAtomMass μ x := ENNReal.toReal_nonneg

/-- On a countable measurable space, the real singleton masses of a
probability measure have sum one. -/
theorem hasSum_measureAtomMass_one (μ : Measure X) [IsProbabilityMeasure μ] :
    HasSum (measureAtomMass μ) 1 := by
  have htsum : (∑' x : X, μ {x}) = μ Set.univ := by
    simpa only [Set.indicator_of_mem (Set.mem_univ _)] using
      Measure.tsum_indicator_apply_singleton μ Set.univ MeasurableSet.univ
  have hfinite : (∑' x : X, μ {x}) ≠ ∞ := by
    rw [htsum]
    simp
  have hs : HasSum (fun x : X ↦ (μ {x}).toReal)
      (∑' x : X, (μ {x}).toReal) := ENNReal.hasSum_toReal hfinite
  have heq : (∑' x : X, (μ {x}).toReal) = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun x ↦ measure_ne_top μ {x}), htsum]
    simp
  change HasSum (fun x : X ↦ (μ {x}).toReal) 1
  simpa only [heq] using hs

section FiniteOrbit

variable [Fintype D] [Nonempty D]
variable (step : D → G) (weight : D → ℝ) (μ : Measure X)

/-- A countable stationary probability has a nonempty finite invariant orbit.
The stationarity premise is pointwise, which is exactly what equality of a
measure with the weighted sum of its step pushforwards gives on singletons. -/
theorem exists_invariant_finite_orbit_finset_of_stationary_probability
    [IsProbabilityMeasure μ]
    (hweight : ∀ d, 0 < weight d) (hweight_one : ∑ d, weight d = 1)
    (hgenerate : Subgroup.closure (Set.range step) = ⊤)
    (hstationary : IsStationaryMass step weight (measureAtomMass μ)) :
    ∃ (F : Finset X), F.Nonempty ∧
      (∀ g : G, Set.MapsTo (fun x : X ↦ g • x) (F : Set X) F) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ x ∈ F, measureAtomMass μ x = c := by
  obtain ⟨y, hyfin, hypos, hyconst⟩ :=
    exists_finite_uniform_orbit_of_stationary_probability step weight
      (measureAtomMass μ) hweight hweight_one hgenerate hstationary
      (measureAtomMass_nonneg μ) (hasSum_measureAtomMass_one μ)
  let F : Finset X := hyfin.toFinset
  refine ⟨F, ?_, ?_, measureAtomMass μ y, hypos, ?_⟩
  · rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have : y ∈ F := hyfin.mem_toFinset.mpr (MulAction.mem_orbit_self y)
    simpa [hempty] using this
  · intro g x hx
    have hx' : x ∈ MulAction.orbit G y := hyfin.mem_toFinset.mp hx
    exact hyfin.mem_toFinset.mpr (MulAction.mem_orbit_of_mem_orbit g hx')
  · intro x hx
    exact hyconst x (hyfin.mem_toFinset.mp hx)

end FiniteOrbit

end IndependentZeroBlocks
