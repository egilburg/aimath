import SierpinskiFormal.GroupFlowStationaryState
import SierpinskiFormal.GroupFlowProbability
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Metrizable.Urysohn

/-!
# Stationary measures on countable compact group flows

This file joins the compact-state construction, the Riesz representation
theorem, and the discrete atomic maximum principle.  It supplies the finite
invariant orbit needed by the Boolean group-flow application.
-/

noncomputable section

open Filter Set Topology MeasureTheory
open scoped BigOperators ENNReal

namespace IndependentZeroBlocks

variable {G X D : Type*} [Group G] [MulAction G X]
variable [TopologicalSpace X] [CompactSpace X] [T2Space X]
variable [MeasurableSpace X] [BorelSpace X] [HasOuterApproxClosed X]
variable [MeasurableSingletonClass X] [Countable X]
variable [ContinuousConstSMul G X]
variable [Fintype D] [Nonempty D]

/-- A group element acting on a compact flow, packaged as a continuous
self-map. -/
def groupActionContinuousMap (g : G) : C(X, X) :=
  ⟨fun x ↦ g • x, continuous_const_smul g⟩

@[simp] theorem groupActionContinuousMap_apply (g : G) (x : X) :
    groupActionContinuousMap (X := X) g x = g • x := rfl

/-- The Markov operator of a finite law acting on a compact group flow. -/
abbrev groupActionAverage (step : D → G) (weight : D → ℝ) :=
  finiteMapAverage X (fun d ↦ groupActionContinuousMap (X := X) (step d)) weight

/-- Every starting point gives a stationary state as a cluster point of its
Cesaro state orbit. -/
theorem exists_stationary_group_action_state_isMapClusterPt
    (step : D → G) (weight : D → ℝ)
    (hweight : ∀ d, 0 ≤ weight d) (hweight_one : ∑ d, weight d = 1)
    (x₀ : X) :
    ∃ L : PositiveNormalizedState X,
      pullbackState X (groupActionAverage (X := X) step weight)
          (finiteMapAverage_isMarkov X _ weight hweight hweight_one) L = L ∧
      MapClusterPt L atTop
        (stateCesaro X (groupActionAverage (X := X) step weight)
          (finiteMapAverage_isMarkov X _ weight hweight hweight_one)
          (evaluationState X x₀)) := by
  letI : Nonempty X := ⟨x₀⟩
  exact exists_stationary_state_isMapClusterPt X
    (groupActionAverage (X := X) step weight)
    (finiteMapAverage_isMarkov X _ weight hweight hweight_one)
    (evaluationState X x₀)

/-- A fixed state for the group-action average yields the corresponding
stationary Riesz measure. -/
theorem stateRieszMeasure_eq_groupActionMeasureAverage
    (step : D → G) (weight : D → ℝ)
    (hweight : ∀ d, 0 ≤ weight d) (hweight_one : ∑ d, weight d = 1)
    (L : PositiveNormalizedState X)
    (hfixed : pullbackState X (groupActionAverage (X := X) step weight)
      (finiteMapAverage_isMarkov X _ weight hweight hweight_one) L = L) :
    stateRieszMeasure X L =
      finiteMapMeasureAverage X
        (fun d ↦ groupActionContinuousMap (X := X) (step d)) weight
        (stateRieszMeasure X L) :=
  stateRieszMeasure_eq_finiteMapMeasureAverage X _ weight hweight
    hweight_one L hfixed

/-- Equality with the weighted sum of group-action pushforwards is exactly
pointwise stationarity of singleton masses. -/
theorem isStationaryMass_measureAtomMass_of_groupActionMeasureAverage
    (step : D → G) (weight : D → ℝ) (hweight : ∀ d, 0 ≤ weight d)
    (μ : Measure X) [IsProbabilityMeasure μ]
    (hμ : μ = finiteMapMeasureAverage X
      (fun d ↦ groupActionContinuousMap (X := X) (step d)) weight μ) :
    IsStationaryMass step weight (measureAtomMass μ) := by
  intro x
  have hsingleton := congrArg (fun ν : Measure X ↦ ν {x}) hμ
  have hmap : ∀ d,
      Measure.map (groupActionContinuousMap (X := X) (step d)) μ {x} =
        μ {(step d)⁻¹ • x} := by
    intro d
    change Measure.map (fun y : X ↦ step d • y) μ {x} = _
    rw [Measure.map_apply
      (continuous_const_smul (step d)).measurable (measurableSet_singleton x)]
    congr 1
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      calc
        y = (step d)⁻¹ • (step d • y) := by simp
        _ = (step d)⁻¹ • x := congrArg ((step d)⁻¹ • ·) h
    · intro h
      rw [h, smul_smul]
      simp
  change (μ {x}).toReal = ∑ d, weight d * (μ {(step d)⁻¹ • x}).toReal
  unfold finiteMapMeasureAverage at hsingleton
  change μ {x} =
    (∑ d, ENNReal.ofReal (weight d) •
      Measure.map (groupActionContinuousMap (X := X) (step d)) μ) {x} at hsingleton
  rw [Measure.finset_sum_apply] at hsingleton
  simp_rw [Measure.smul_apply, hmap] at hsingleton
  have hre := congrArg ENNReal.toReal hsingleton
  have hfinite : ∀ d,
      ENNReal.ofReal (weight d) • μ {(step d)⁻¹ • x} ≠ ⊤ := by
    intro d
    simp only [smul_eq_mul]
    exact ne_of_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ _))
  rw [ENNReal.toReal_sum (fun d _ ↦ hfinite d)] at hre
  simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal, hweight] using hre

/-- For a generating positive law, stationarity of the measure average
upgrades to invariance under every group element. -/
theorem groupActionMeasure_invariant_of_measureAverage
    (step : D → G) (weight : D → ℝ) (hweight : ∀ d, 0 < weight d)
    (hweight_one : ∑ d, weight d = 1)
    (hgenerate : Subgroup.closure (Set.range step) = ⊤)
    (μ : Measure X) [IsProbabilityMeasure μ]
    (hμ : μ = finiteMapMeasureAverage X
      (fun d ↦ groupActionContinuousMap (X := X) (step d)) weight μ) :
    ∀ g : G, Measure.map (fun x : X ↦ g • x) μ = μ := by
  have hstationary : IsStationaryMass step weight (measureAtomMass μ) :=
    isStationaryMass_measureAtomMass_of_groupActionMeasureAverage
      (X := X) step weight (fun d ↦ (hweight d).le) μ hμ
  have hinvariant := stationary_mass_invariant step weight (measureAtomMass μ)
    hweight hweight_one hgenerate hstationary
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

/-- The complete compact-countable mechanism: a positive finite law whose
support generates the group has a nonempty finite invariant orbit in every
countable compact group flow. -/
theorem exists_invariant_finite_orbit_finset_of_compact_group_flow
    (step : D → G) (weight : D → ℝ)
    (hweight : ∀ d, 0 < weight d) (hweight_one : ∑ d, weight d = 1)
    (hgenerate : Subgroup.closure (Set.range step) = ⊤) (x₀ : X) :
    ∃ (L : PositiveNormalizedState X) (F : Finset X),
      MapClusterPt L atTop
        (stateCesaro X (groupActionAverage (X := X) step weight)
          (finiteMapAverage_isMarkov X _ weight (fun d ↦ (hweight d).le)
            hweight_one) (evaluationState X x₀)) ∧
      (∀ g : G, Measure.map (fun x : X ↦ g • x) (stateRieszMeasure X L) =
        stateRieszMeasure X L) ∧
      F.Nonempty ∧
      (∀ g : G, Set.MapsTo (fun x : X ↦ g • x) (F : Set X) F) := by
  letI : Nonempty X := ⟨x₀⟩
  obtain ⟨L, hfixed, hcluster⟩ :=
    exists_stationary_group_action_state_isMapClusterPt
      (X := X) step weight (fun d ↦ (hweight d).le) hweight_one x₀
  let μ := stateRieszMeasure X L
  have hμ := stateRieszMeasure_eq_groupActionMeasureAverage
    (X := X) step weight (fun d ↦ (hweight d).le) hweight_one L hfixed
  have hstationary : IsStationaryMass step weight (measureAtomMass μ) :=
    isStationaryMass_measureAtomMass_of_groupActionMeasureAverage
      (X := X) step weight (fun d ↦ (hweight d).le) μ hμ
  have hmeasureInvariant : ∀ g : G,
      Measure.map (fun x : X ↦ g • x) μ = μ :=
    groupActionMeasure_invariant_of_measureAverage
      (X := X) step weight hweight hweight_one hgenerate μ hμ
  obtain ⟨F, hFnonempty, hFinvariant, _⟩ :=
    exists_invariant_finite_orbit_finset_of_stationary_probability
      step weight μ hweight hweight_one hgenerate hstationary
  exact ⟨L, F, hcluster, hmeasureInvariant, hFnonempty, hFinvariant⟩

end IndependentZeroBlocks
