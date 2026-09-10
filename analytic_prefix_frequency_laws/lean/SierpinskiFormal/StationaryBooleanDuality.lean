import SierpinskiFormal.StationaryPairedCompacta
import SierpinskiFormal.StationaryL1Duality

/-! # The concrete dual representation for a stable Boolean orbit span -/

noncomputable section

set_option maxSynthPendingDepth 3

open Set Filter Topology MeasureTheory
open scoped ENNReal BoundedContinuousFunction

namespace IndependentZeroBlocks

variable {X A : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [HasOuterApproxClosed X]
  [TopologicalSpace A] [DiscreteTopology A] [Countable A]
  {μ : Measure X} [IsProbabilityMeasure μ] [μ.WeaklyRegular]

theorem booleanWordRightOrbitSpan_exists_dualFieldPairing
    (q : List A → Bool)
    (hDLP : HasBooleanDoubleLimitProperty (fun w z ↦ q (z ++ w)))
    (Λ : Lp (BooleanWordRightOrbitSpan q) 1 μ →L[ℝ] ℝ) :
    ∃ η : Lp ((BooleanWordRightOrbitSpan q) →L[ℝ] ℝ) ∞ μ,
      Λ = dualFieldPairing μ η := by
  letI : Countable (BooleanWordLeftCompactum q) :=
    booleanWordLeftCompactum_countable q hDLP
  borelize ↥(BooleanWordLeftCompactum q)
  exact exists_dualFieldPairing_of_isometricContinuousMapEmbedding
    (booleanWordRightOrbitNormingLI q) Λ

end IndependentZeroBlocks
