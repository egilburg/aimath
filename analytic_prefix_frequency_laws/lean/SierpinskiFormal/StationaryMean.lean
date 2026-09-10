import SierpinskiFormal.StationaryL1Skew
import SierpinskiFormal.RecognizableSupportCompactness

/-!
# Compact-hull inputs for stationary word means

This file assembles all hypotheses of the representation-free stationary
mean argument which are currently formalizable in Mathlib.  For a Boolean
word predicate with the double-limit property, its pathwise prefix averages
lie in one weakly compact convex hull and form a uniformly integrable family
in Bochner `L¹`.

The remaining implication from these two facts to weak compactness in
Bochner `L¹` is the specialized Diestel theorem recorded in the project
checkpoint; it is not asserted here.
-/

noncomputable section

open Filter Set Topology MeasureTheory
open scoped ENNReal Topology BoundedContinuousFunction

namespace IndependentZeroBlocks

section BooleanHull

variable {Ω A : Type*} [MeasurableSpace Ω]
  [TopologicalSpace A] [DiscreteTopology A]
  [Fintype A] [Nonempty A] [DecidableEq A]
  [MeasurableSpace A] [MeasurableSingletonClass A]
  {μ : Measure Ω}

/-- The norm-closed convex hull of the bounded Boolean translation closure. -/
def booleanWordCompactHull (q : List A → Bool) :
    Set (BoundedWordFunction A) :=
  closedConvexHull ℝ (boundedBooleanWordRowClosure q)

theorem convex_booleanWordCompactHull (q : List A → Bool) :
    Convex ℝ (booleanWordCompactHull q) :=
  convex_closedConvexHull (𝕜 := ℝ) (s := boundedBooleanWordRowClosure q)

theorem booleanWordIndicator_mem_compactHull (q : List A → Bool) :
    booleanWordIndicator q ∈ booleanWordCompactHull q :=
  subset_closedConvexHull
    (booleanWordIndicator_mem_boundedBooleanWordRowClosure q)

theorem mapsTo_wordRightTranslate_booleanWordCompactHull
    (q : List A → Bool) (a : A) :
    Set.MapsTo (wordRightTranslate [a])
      (booleanWordCompactHull q) (booleanWordCompactHull q) :=
  mapsTo_wordRightTranslate_closedConvexHull q a

/-- Every positive pathwise prefix average lies in the one common Boolean
translation hull. -/
theorem stationaryBooleanWordCesaro_mem_compactHull
    (letter : Ω → A) (T : Ω → Ω) (q : List A → Bool)
    {N : ℕ} (hN : N ≠ 0) (x : Ω) :
    stationaryWordCesaro letter T (booleanWordIndicator q) N x ∈
      booleanWordCompactHull q := by
  exact stationaryWordCesaro_mem letter T (booleanWordIndicator q)
    (booleanWordCompactHull q) (convex_booleanWordCompactHull q)
    (booleanWordIndicator_mem_compactHull q)
    (mapsTo_wordRightTranslate_booleanWordCompactHull q) hN x

/-- The common Boolean translation hull is weakly compact under the
double-limit property. -/
theorem isCompact_toWeakSpace_image_booleanWordCompactHull
    (q : List A → Bool)
    (hDLP : HasBooleanDoubleLimitProperty (fun w z => q (z ++ w))) :
    IsCompact (toWeakSpace ℝ (BoundedWordFunction A) ''
      booleanWordCompactHull q) := by
  have hDLP' : HasBooleanDoubleLimitProperty (booleanWordRow q) := by
    change HasBooleanDoubleLimitProperty (fun w z ↦ q (z ++ w))
    exact hDLP
  obtain ⟨hcompact, hcount⟩ :=
    booleanRowClosure_weakly_compact_and_countable (booleanWordRow q) hDLP'
  let K := boundedBooleanWordRowClosure q
  have hKcompact : IsCompact (toWeakSpace ℝ (BoundedWordFunction A) '' K) :=
    isCompact_boundedBooleanWordRowClosure_of_extended q (by
      simpa only [extendedBooleanWordRowClosure, booleanWordRowClosure,
        booleanRowExtensionClosure] using hcompact)
  have hKcount : K.Countable :=
    countable_boundedBooleanWordRowClosure_of_extended q (by
      simpa only [extendedBooleanWordRowClosure, booleanWordRowClosure,
        booleanRowExtensionClosure] using hcount)
  have hKne : K.Nonempty :=
    ⟨booleanWordIndicator q,
      booleanWordIndicator_mem_boundedBooleanWordRowClosure q⟩
  exact IndependentZeroBlocks.Set.Countable.isCompact_toWeakSpace_image_closedConvexHull
    hKcount hKne 1
    (fun f hf => norm_le_one_of_mem_boundedBooleanWordRowClosure q hf)
    hKcompact

/-- The pathwise Boolean prefix averages are uniformly integrable in
Bochner `L¹`. -/
theorem uniformIntegrable_one_stationaryBooleanWordCesaro
    [IsFiniteMeasure μ]
    (letter : Ω → A) (hletter : Measurable letter)
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (q : List A → Bool) :
    UniformIntegrable
      (stationaryWordCesaro letter T (booleanWordIndicator q)) 1 μ :=
  uniformIntegrable_one_stationaryWordCesaro
    letter hletter T hT (booleanWordIndicator q)

end BooleanHull

end IndependentZeroBlocks
