import SierpinskiFormal.CountableGroupFlowAtomic
import SierpinskiFormal.GroupFlowProbability
import Mathlib.Topology.Algebra.MulAction
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
# Countably supported stationary probability measures on group flows

The interface here is deliberately pointwise: stationarity is asserted for
the real masses of singletons.  This is the exact output needed from any
construction of a countable weighted measure average, and it avoids choosing
an enumeration of the law.
-/

noncomputable section

open scoped BigOperators ENNReal
open Set MeasureTheory

namespace IndependentZeroBlocks

variable {G X D : Type*} [Group G] [MulAction G X]
variable [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
variable [MeasurableSingletonClass X] [Countable X]
variable [ContinuousConstSMul G X]

/-- Pointwise stationarity of a measure for a countably supported law. -/
def IsCountableStationaryMeasure (step : D → G) (weight : D → ℝ)
    (μ : Measure X) : Prop :=
  IsCountableStationaryMass step weight (measureAtomMass μ)

/-- A countably supported positive generating stationary probability is
invariant under every group element. -/
theorem countable_groupActionMeasure_invariant_of_pointwise_stationary
    (step : D → G) (weight : D → ℝ)
    (hweight : ∀ d, 0 < weight d) (hweight_sum : HasSum weight 1)
    (hgenerate : Subgroup.closure (Set.range step) = ⊤)
    (μ : Measure X) [IsProbabilityMeasure μ]
    (hstationary : IsCountableStationaryMeasure step weight μ) :
    ∀ g : G, Measure.map (fun x : X ↦ g • x) μ = μ := by
  have hinvariant := countable_stationary_mass_invariant step weight
    (measureAtomMass μ) hweight hweight_sum hgenerate hstationary
    (hasSum_measureAtomMass_one μ).summable (measureAtomMass_nonneg μ)
  intro g
  apply Measure.ext_of_singleton
  intro x
  rw [Measure.map_apply (continuous_const_smul g).measurable
    (measurableSet_singleton x)]
  have hpreimage : (fun y : X ↦ g • y) ⁻¹' {x} = {g⁻¹ • x} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      calc
        y = g⁻¹ • (g • y) := by simp
        _ = g⁻¹ • x := congrArg (g⁻¹ • ·) h
    · intro h
      rw [h, smul_smul]
      simp
  rw [hpreimage]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) (measure_ne_top μ _)).mp
  exact hinvariant g⁻¹ x

/-- The positive part of a countably supported stationary probability
contains a nonempty finite orbit invariant under the whole group. -/
theorem countable_exists_invariant_finite_orbit_finset_of_stationary_probability
    (step : D → G) (weight : D → ℝ) (μ : Measure X)
    [IsProbabilityMeasure μ]
    (hweight : ∀ d, 0 < weight d) (hweight_sum : HasSum weight 1)
    (hgenerate : Subgroup.closure (Set.range step) = ⊤)
    (hstationary : IsCountableStationaryMeasure step weight μ) :
    ∃ (F : Finset X), F.Nonempty ∧
      (∀ g : G, Set.MapsTo (fun x : X ↦ g • x) (F : Set X) F) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ x ∈ F, measureAtomMass μ x = c := by
  obtain ⟨y, hyfin, hypos, hyconst⟩ :=
    countable_exists_finite_uniform_orbit_of_stationary_probability
      step weight (measureAtomMass μ) hweight hweight_sum hgenerate hstationary
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

/-- Combined measure-level consequence used by compact-flow applications. -/
theorem countable_stationary_probability_invariant_and_finite_orbit
    (step : D → G) (weight : D → ℝ) (μ : Measure X)
    [IsProbabilityMeasure μ]
    (hweight : ∀ d, 0 < weight d) (hweight_sum : HasSum weight 1)
    (hgenerate : Subgroup.closure (Set.range step) = ⊤)
    (hstationary : IsCountableStationaryMeasure step weight μ) :
    (∀ g : G, Measure.map (fun x : X ↦ g • x) μ = μ) ∧
      ∃ (F : Finset X), F.Nonempty ∧
        (∀ g : G, Set.MapsTo (fun x : X ↦ g • x) (F : Set X) F) := by
  refine ⟨countable_groupActionMeasure_invariant_of_pointwise_stationary
    step weight hweight hweight_sum hgenerate μ hstationary, ?_⟩
  obtain ⟨F, hFne, hFinv, _⟩ :=
    countable_exists_invariant_finite_orbit_finset_of_stationary_probability
      step weight μ hweight hweight_sum hgenerate hstationary
  exact ⟨F, hFne, hFinv⟩

end IndependentZeroBlocks
