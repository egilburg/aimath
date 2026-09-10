import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false

namespace IndependentZeroBlocks

open Filter Set Topology
open MeasureTheory CompactlySupported CompactlySupportedContinuousMap

/-- Uniformly bounded, pointwise-convergent continuous real functions
converge after integration against any finite measure. -/
theorem tendsto_integral_continuousMap_of_pointwise_of_uniform_bound
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (mu : Measure X) [IsFiniteMeasure mu]
    (u : ℕ → C(X, ℝ)) (v : C(X, ℝ)) (C : ℝ)
    (hbound : ∀ n x, ‖u n x‖ ≤ C)
    (hpointwise : ∀ x, Tendsto (fun n ↦ u n x) atTop (nhds (v x))) :
    Tendsto (fun n ↦ ∫ x, u n x ∂mu) atTop (nhds (∫ x, v x ∂mu)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ : X ↦ C)
  · intro n
    exact (u n).continuous.aestronglyMeasurable
  · exact integrable_const C
  · intro n
    exact Filter.Eventually.of_forall (hbound n)
  · exact Filter.Eventually.of_forall hpointwise

/-- A positive continuous linear functional on `C(X, ℝ)` sends every
uniformly norm-bounded pointwise-convergent sequence with continuous limit
to a convergent scalar sequence. -/
theorem tendsto_positiveFunctional_continuousMap_of_pointwise
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (phi : C(X, ℝ) →L[ℝ] ℝ)
    (hphi : ∀ f : C(X, ℝ), 0 ≤ f → 0 ≤ phi f)
    (u : ℕ → C(X, ℝ)) (v : C(X, ℝ)) (C : ℝ)
    (hbound : ∀ n, ‖u n‖ ≤ C)
    (hpointwise : ∀ x, Tendsto (fun n ↦ u n x) atTop (nhds (v x))) :
    Tendsto (fun n ↦ phi (u n)) atTop (nhds (phi v)) := by
  let Lambda : C_c(X, ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun f ↦ phi f.toContinuousMap
      map_add' := fun f g ↦ by
        change phi (f.toContinuousMap + g.toContinuousMap) = _
        exact phi.map_add f.toContinuousMap g.toContinuousMap
      map_smul' := fun r f ↦ by
        change phi (r • f.toContinuousMap) = r • phi f.toContinuousMap
        exact phi.map_smul r f.toContinuousMap }
  have hLambda : ∀ f : C_c(X, ℝ), 0 ≤ f → 0 ≤ Lambda f := by
    intro f hf
    apply hphi f.toContinuousMap
    intro x
    exact hf x
  let LambdaPos : C_c(X, ℝ) →ₚ[ℝ] ℝ := PositiveLinearMap.mk₀ Lambda hLambda
  let mu : Measure X := RealRMK.rieszMeasure LambdaPos
  letI : IsFiniteMeasure mu := IsFiniteMeasure.mk (by
    dsimp [mu, RealRMK.rieszMeasure]
    rw [Content.measure_apply _ MeasurableSet.univ]
    exact Content.outerMeasure_lt_top_of_isCompact _ isCompact_univ)
  have hboundPoint (n : ℕ) (x : X) : ‖u n x‖ ≤ C :=
    (ContinuousMap.norm_coe_le_norm (u n) x).trans (hbound n)
  have hmu : Tendsto (fun n ↦ ∫ x, u n x ∂mu) atTop
      (nhds (∫ x, v x ∂mu)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ : X ↦ C)
    · intro n
      exact (u n).continuous.aestronglyMeasurable
    · exact integrable_const C
    · intro n
      exact Filter.Eventually.of_forall (hboundPoint n)
    · exact Filter.Eventually.of_forall hpointwise
  have hrepr (f : C(X, ℝ)) : ∫ x, f x ∂mu = phi f := by
    let f' : C_c(X, ℝ) := CompactlySupportedContinuousMap.continuousMapEquiv f
    calc
      ∫ x, f x ∂mu = ∫ x, f' x ∂mu := by rfl
      _ = LambdaPos f' := by
        simpa only [mu] using RealRMK.integral_rieszMeasure LambdaPos f'
      _ = phi f'.toContinuousMap := by rfl
      _ = phi f := congrArg phi (ContinuousMap.ext fun _ ↦ rfl)
  simpa only [hrepr] using hmu

/-- The same conclusion holds for every functional supplied as a difference
of two positive continuous linear functionals. This isolates the exact
Jordan-decomposition input needed to cover an arbitrary dual functional. -/
theorem tendsto_sub_positiveFunctionals_continuousMap_of_pointwise
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (phiPos phiNeg : C(X, ℝ) →L[ℝ] ℝ)
    (hphiPos : ∀ f : C(X, ℝ), 0 ≤ f → 0 ≤ phiPos f)
    (hphiNeg : ∀ f : C(X, ℝ), 0 ≤ f → 0 ≤ phiNeg f)
    (u : ℕ → C(X, ℝ)) (v : C(X, ℝ)) (C : ℝ)
    (hbound : ∀ n, ‖u n‖ ≤ C)
    (hpointwise : ∀ x, Tendsto (fun n ↦ u n x) atTop (nhds (v x))) :
    Tendsto (fun n ↦ (phiPos - phiNeg) (u n)) atTop
      (nhds ((phiPos - phiNeg) v)) := by
  have hpos := tendsto_positiveFunctional_continuousMap_of_pointwise
    phiPos hphiPos u v C hbound hpointwise
  have hneg := tendsto_positiveFunctional_continuousMap_of_pointwise
    phiNeg hphiNeg u v C hbound hpointwise
  simpa using hpos.sub hneg

end IndependentZeroBlocks
