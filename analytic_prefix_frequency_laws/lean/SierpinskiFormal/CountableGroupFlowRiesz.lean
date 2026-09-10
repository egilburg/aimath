import SierpinskiFormal.CountableGroupFlowStationary
import SierpinskiFormal.GroupFlowStationaryMeasure
import Mathlib.Topology.Metrizable.Urysohn

/-!
# Riesz bridge for countably supported stationary states

This file converts the scalar `tsum` identity for a positive normalized
state into pointwise stationarity of its singleton masses.  Construction of
the averaged operator is deliberately separated: an operator proof only has
to establish `IsCountableStationaryState` below.
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

/-- The scalar stationarity identity required of a state for a countably
supported group law. -/
def IsCountableStationaryState (step : D → G) (weight : D → ℝ)
    (L : PositiveNormalizedState X) : Prop :=
  ∀ f : C(X, ℝ), L.1 f =
    ∑' d, weight d * L.1 (f.comp (groupActionContinuousMap (X := X) (step d)))

/-- The countable weighted sum of group-action pushforwards. -/
def countableGroupActionMeasureAverage (step : D → G) (weight : D → ℝ)
    (μ : Measure X) : Measure X :=
  Measure.sum fun d ↦ ENNReal.ofReal (weight d) •
    Measure.map (groupActionContinuousMap (X := X) (step d)) μ

/-- A scalar-stationary state has a Riesz measure equal to the countable
weighted sum of its step pushforwards. -/
theorem stateRieszMeasure_eq_countableGroupActionMeasureAverage
    (step : D → G) (weight : D → ℝ)
    (hweight : ∀ d, 0 ≤ weight d) (hweight_sum : HasSum weight 1)
    (L : PositiveNormalizedState X)
    (hstationary : IsCountableStationaryState step weight L) :
    stateRieszMeasure X L =
      countableGroupActionMeasureAverage step weight (stateRieszMeasure X L) := by
  let μ := stateRieszMeasure X L
  let ν := countableGroupActionMeasureAverage step weight μ
  letI : IsFiniteMeasure ν := by
    constructor
    have hsum : (∑' d, ENNReal.ofReal (weight d)) = 1 := by
      rw [← ENNReal.ofReal_tsum_of_nonneg hweight hweight_sum.summable,
        hweight_sum.tsum_eq]
      norm_num
    change ν Set.univ < ∞
    rw [show ν Set.univ = ∑' d, ENNReal.ofReal (weight d) by
      simp [ν, countableGroupActionMeasureAverage, Measure.sum_apply,
        Measure.smul_apply, Measure.map_apply,
        (groupActionContinuousMap (X := X) _).continuous.measurable]]
    rw [hsum]
    exact ENNReal.one_lt_top
  change μ = ν
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  let fc : C(X, ℝ) := f.toContinuousMap
  change (∫ x, fc x ∂μ) = ∫ x, fc x ∂ν
  rw [integral_stateRieszMeasure X L fc]
  rw [hstationary fc]
  let m : D → Measure X := fun d ↦ ENNReal.ofReal (weight d) •
    Measure.map (groupActionContinuousMap (X := X) (step d)) μ
  have hν : ν = Measure.sum m := rfl
  have hfm : Integrable (fun x ↦ fc x) (Measure.sum m) := by
    rw [← hν]
    exact f.integrable ν
  calc
    (∑' d, weight d * L.1
      (fc.comp (groupActionContinuousMap (X := X) (step d)))) =
        ∑' d, ∫ x, fc x ∂m d := by
      apply tsum_congr
      intro d
      rw [MeasureTheory.integral_smul_measure]
      rw [ENNReal.toReal_ofReal (hweight d)]
      simp only [smul_eq_mul]
      congr 1
      calc
        L.1 (fc.comp (groupActionContinuousMap (X := X) (step d))) =
            ∫ x, fc (step d • x) ∂μ := by
              simpa using (integral_stateRieszMeasure X L
                (fc.comp (groupActionContinuousMap (X := X) (step d)))).symm
        _ = ∫ x, fc ((groupActionContinuousMap (X := X) (step d)) x) ∂μ := by
          rfl
        _ = ∫ x, fc x ∂Measure.map
            (groupActionContinuousMap (X := X) (step d)) μ := by
          rw [MeasureTheory.integral_map
            (groupActionContinuousMap (X := X) (step d)).continuous.measurable.aemeasurable
            fc.continuous.aestronglyMeasurable]
    _ = ∫ x, fc x ∂Measure.sum m :=
      (MeasureTheory.integral_sum_measure hfm).symm
    _ = ∫ x, fc x ∂ν := by rw [hν]

/-- The Riesz measure of a scalar-stationary state satisfies the singleton
mass equation used by the countable atomic maximum principle. -/
theorem stateRieszMeasure_isCountableStationaryMeasure
    (step : D → G) (weight : D → ℝ)
    (hweight : ∀ d, 0 ≤ weight d) (hweight_sum : HasSum weight 1)
    (L : PositiveNormalizedState X)
    (hstationary : IsCountableStationaryState step weight L) :
    IsCountableStationaryMeasure step weight (stateRieszMeasure X L) := by
  let μ := stateRieszMeasure X L
  have hμ : μ = countableGroupActionMeasureAverage step weight μ :=
    stateRieszMeasure_eq_countableGroupActionMeasureAverage
      step weight hweight hweight_sum L hstationary
  intro x
  have hx := congrArg (fun ν : Measure X ↦ ν {x}) hμ
  have hx' : μ {x} = ∑' d, ENNReal.ofReal (weight d) *
      μ {(step d)⁻¹ • x} := by
    calc
      μ {x} = countableGroupActionMeasureAverage step weight μ {x} := hx
      _ = ∑' d, (ENNReal.ofReal (weight d) •
          Measure.map (groupActionContinuousMap (X := X) (step d)) μ) {x} :=
        MeasureTheory.Measure.sum_apply _ (measurableSet_singleton x)
      _ = ∑' d, ENNReal.ofReal (weight d) * μ {(step d)⁻¹ • x} := by
        apply tsum_congr
        intro d
        rw [Measure.smul_apply]
        congr 1
        rw [Measure.map_apply
          (groupActionContinuousMap (X := X) (step d)).continuous.measurable
          (measurableSet_singleton x)]
        congr 1
        ext y
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        constructor
        · intro h
          calc
            y = (step d)⁻¹ • (step d • y) := by simp
            _ = (step d)⁻¹ • x := congrArg ((step d)⁻¹ • ·) h
        · intro h
          rw [h]
          change step d • ((step d)⁻¹ • x) = x
          simp
  change (μ {x}).toReal = ∑' d, weight d * (μ {(step d)⁻¹ • x}).toReal
  have hre := congrArg ENNReal.toReal hx'
  rw [ENNReal.tsum_toReal_eq (fun d ↦ by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ _))] at hre
  simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal, hweight] using hre

end IndependentZeroBlocks
