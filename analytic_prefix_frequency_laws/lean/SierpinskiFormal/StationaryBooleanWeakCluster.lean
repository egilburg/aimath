import SierpinskiFormal.StationaryBooleanDuality
import SierpinskiFormal.StationarySourceBridge
import Mathlib.Topology.Metrizable.Urysohn

/-!
# Uniform pathwise convergence for stable Boolean word predicates

The paired Boolean compacta provide the weak Bochner cluster required by the
skew mean and maximal theorems.  The conclusion holds for every stationary
finite-alphabet source, and convergence is in the norm of bounded word
functions: all fixed left contexts are controlled simultaneously.
-/

noncomputable section

set_option maxSynthPendingDepth 4
set_option maxHeartbeats 2000000

open Function Set Filter Topology MeasureTheory
open scoped ENNReal BigOperators BoundedContinuousFunction

namespace IndependentZeroBlocks

section Canonical

variable {A : Type*} [Fintype A] [Nonempty A] [DecidableEq A]
  [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [MeasurableSingletonClass A] [BorelSpace A]
  {μ : Measure (ℕ → A)} [IsProbabilityMeasure μ]

/-- The actual stationary Boolean prefix averages have a weak `L¹` cluster.
There is no compactness or dual-representation premise in this conclusion. -/
theorem exists_weak_mapClusterPt_stationaryBooleanWordCesaro
    (q : List A → Bool)
    (hDLP : HasBooleanDoubleLimitProperty (fun w z ↦ q (z ++ w)))
    (hshift : MeasurePreserving digitShift μ μ) :
    ∃ a : Lp (BoundedWordFunction A) 1 μ,
      MapClusterPt (toWeakSpace ℝ (Lp (BoundedWordFunction A) 1 μ) a) atTop
        (fun N => toWeakSpace ℝ (Lp (BoundedWordFunction A) 1 μ)
          (birkhoffAverage ℝ
            (stationaryWordSkewL1CLM digitHead measurable_digitHead digitShift hshift)
            id N (Lp.const 1 μ (booleanWordIndicator q)))) := by
  letI : Countable (BooleanWordRawRightCompactum q) :=
    booleanWordRawRightCompactum_countable q hDLP
  borelize ↥(BooleanWordRawRightCompactum q)
  let j := booleanWordRawRightOrbitLift q hDLP
  let g := stationaryBooleanRawRightContinuousMap q
  have hj : ∀ k, ‖j k‖ ≤ 1 :=
    norm_booleanWordRawRightOrbitLift_le_one q hDLP
  have hjweak : ∀ φ : BooleanWordRightOrbitSpan q →L[ℝ] ℝ,
      Continuous (fun k => φ (j k)) := by
    intro φ
    exact (WeakBilin.eval_continuous (topDualPairing ℝ
      (BooleanWordRightOrbitSpan q)).flip φ).comp
        (continuous_toWeakSpace_booleanWordRawRightOrbitLift q hDLP)
  obtain ⟨L, hL⟩ := exists_mapClusterPt_empiricalGraphState (μ := μ) g
  have hc := mapClusterPt_graphCesaroLp_of_empiricalGraphState_cluster
    j 1 zero_le_one hj hjweak g L hL
      (booleanWordRightOrbitSpan_exists_dualFieldPairing q hDLP)
  let a := fiberBarycenterLp (μ := μ)
    (stateRieszMeasure ((ℕ → A) × BooleanWordRawRightCompactum q) L)
    (stateRieszMeasure_fst_eq_of_mapClusterPt_empiricalGraphState g L hL)
    j 1 hj
  let ι : Lp (BooleanWordRightOrbitSpan q) 1 μ →L[ℝ]
      Lp (BoundedWordFunction A) 1 μ :=
    (Submodule.subtypeL (R := ℝ) (BooleanWordRightOrbitSpan q)).compLpL 1 μ
  refine ⟨ι a, ?_⟩
  apply (mapClusterPt_atTop_succ_iff _ _).mp
  have hp := MapClusterPt.continuousAt_comp
    (WeakSpace.map ι).continuous.continuousAt hc
  have heq : (fun N => (WeakSpace.map ι)
      (toWeakSpace ℝ (Lp (BooleanWordRightOrbitSpan q) 1 μ)
        (graphCesaroLp (μ := μ) j 1 hj g N))) =
      (fun N => toWeakSpace ℝ (Lp (BoundedWordFunction A) 1 μ)
        (birkhoffAverage ℝ
          (stationaryWordSkewL1CLM digitHead measurable_digitHead digitShift hshift)
          id (N + 1) (Lp.const 1 μ (booleanWordIndicator q)))) := by
    funext N
    change toWeakSpace ℝ _
      (stationaryBooleanRawRightGraphCesaroLp (μ := μ) q hDLP N) = _
    rw [stationaryBooleanRawRightGraphCesaroLp_eq_birkhoffAverage q hDLP hshift]
  change MapClusterPt _ atTop (fun N => (WeakSpace.map ι)
    (toWeakSpace ℝ (Lp (BooleanWordRightOrbitSpan q) 1 μ)
      (graphCesaroLp (μ := μ) j 1 hj g N))) at hp
  rw [heq] at hp
  exact hp

end Canonical

end IndependentZeroBlocks
