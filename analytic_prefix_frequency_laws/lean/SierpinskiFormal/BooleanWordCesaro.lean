import SierpinskiFormal.CountableWeakKrein
import SierpinskiFormal.IidCompactWordAverages
import SierpinskiFormal.BooleanWeakCompactness

/-!
# IID Cesaro convergence from a countable compact Boolean row closure

This file transfers the compact/countable ultrafilter-extension closure of a
Boolean word kernel to bounded word functions, applies the countable Krein
theorem, and checks one-letter translation invariance.
-/

noncomputable section

open Filter Set Topology
open scoped Topology BoundedContinuousFunction

namespace IndependentZeroBlocks

section PureRestriction

variable (Y : Type*) [TopologicalSpace Y] [DiscreteTopology Y] [Nonempty Y]

/-- Restriction of a continuous function on the ultrafilter compactification
to the original points. -/
def restrictToPure : C(Ultrafilter Y, ℝ) →L[ℝ] (Y →ᵇ ℝ) :=
  ({
    toFun := fun f ↦ BoundedContinuousFunction.mkOfDiscrete
      (fun y ↦ f (pure y)) (2 * ‖f‖) (fun x y ↦ by
        exact ContinuousMap.dist_le_two_norm f (pure x) (pure y))
    map_add' := by
      intro f g
      ext y
      rfl
    map_smul' := by
      intro c f
      ext y
      rfl
  } : C(Ultrafilter Y, ℝ) →ₗ[ℝ] (Y →ᵇ ℝ)).mkContinuous 1 (fun f ↦ by
    rw [BoundedContinuousFunction.norm_le_of_nonempty]
    intro y
    simpa using ContinuousMap.norm_coe_le_norm f (pure y))

@[simp] theorem restrictToPure_apply (f : C(Ultrafilter Y, ℝ)) (y : Y) :
    restrictToPure Y f y = f (pure y) := rfl

@[simp] theorem restrictToPure_booleanUltrafilterExtension (g : Y → Bool) :
    restrictToPure Y (booleanUltrafilterExtension g) =
      BoundedContinuousFunction.mkOfDiscrete (fun y ↦ boolIndicator (g y)) 1 (by
        intro x y
        cases hx : g x <;> cases hy : g y <;>
          norm_num [boolIndicator, Real.dist_eq, hx, hy]) := by
  ext y
  simp

end PureRestriction

section BooleanWords

variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
  [Fintype A] [Nonempty A]

/-- The bounded real indicator associated with a Boolean word predicate. -/
def booleanWordIndicator (q : List A → Bool) : BoundedWordFunction A :=
  BoundedContinuousFunction.mkOfDiscrete (fun w ↦ boolIndicator (q w)) 1 (by
    intro x y
    cases hx : q x <;> cases hy : q y <;>
      norm_num [boolIndicator, Real.dist_eq, hx, hy])

omit [Fintype A] [Nonempty A] in
@[simp] theorem booleanWordIndicator_apply (q : List A → Bool) (w : List A) :
    booleanWordIndicator q w = boolIndicator (q w) := rfl

/-- Rows are right translates of the original word predicate. -/
def booleanWordRow (q : List A → Bool) (w z : List A) : Bool :=
  q (z ++ w)

/-- Pointwise closure of the Boolean right-translation rows. -/
def booleanWordRowClosure (q : List A → Bool) : Set (List A → Bool) :=
  closure (Set.range (booleanWordRow q))

/-- Real bounded functions obtained from the Boolean row closure. -/
def boundedBooleanWordRowClosure (q : List A → Bool) :
    Set (BoundedWordFunction A) :=
  booleanWordIndicator '' booleanWordRowClosure q

/-- Continuous ultrafilter extensions of the Boolean row closure. -/
def extendedBooleanWordRowClosure (q : List A → Bool) :
    Set C(Ultrafilter (List A), ℝ) :=
  booleanUltrafilterExtension '' booleanWordRowClosure q

omit [Fintype A] in
theorem restrictToPure_image_extendedBooleanWordRowClosure (q : List A → Bool) :
    restrictToPure (List A) '' extendedBooleanWordRowClosure q =
      boundedBooleanWordRowClosure q := by
  ext f
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    refine ⟨g, hg, ?_⟩
    ext z
    simp [booleanWordIndicator]
  · rintro ⟨g, hg, rfl⟩
    refine ⟨booleanUltrafilterExtension g, ⟨g, hg, rfl⟩, ?_⟩
    ext z
    simp [booleanWordIndicator]

omit [Fintype A] [Nonempty A] in
/-- The original Boolean indicator belongs to its row closure. -/
theorem booleanWordIndicator_mem_boundedBooleanWordRowClosure (q : List A → Bool) :
    booleanWordIndicator q ∈ boundedBooleanWordRowClosure q := by
  refine ⟨booleanWordRow q [], subset_closure ⟨[], rfl⟩, ?_⟩
  ext z
  simp [booleanWordRow, booleanWordIndicator]

omit [Fintype A] in
/-- Weak compactness transfers from ultrafilter extensions to restriction at
the original word coordinates. -/
theorem isCompact_boundedBooleanWordRowClosure_of_extended
    (q : List A → Bool)
    (hcompact : IsCompact (toWeakSpace ℝ C(Ultrafilter (List A), ℝ) ''
      extendedBooleanWordRowClosure q)) :
    IsCompact (toWeakSpace ℝ (BoundedWordFunction A) ''
      boundedBooleanWordRowClosure q) := by
  have himage := hcompact.image
    (WeakSpace.map (restrictToPure (List A))).continuous
  rw [← restrictToPure_image_extendedBooleanWordRowClosure q]
  convert himage using 1
  ext f
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨toWeakSpace ℝ C(Ultrafilter (List A), ℝ) g, ⟨g, hg, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨restrictToPure (List A) g, ⟨g, hg, rfl⟩, rfl⟩

omit [Fintype A] in
/-- Countability also transfers through restriction at pure points. -/
theorem countable_boundedBooleanWordRowClosure_of_extended
    (q : List A → Bool)
    (hcount : (extendedBooleanWordRowClosure q).Countable) :
    (boundedBooleanWordRowClosure q).Countable := by
  rw [← restrictToPure_image_extendedBooleanWordRowClosure q]
  exact hcount.image _

omit [Fintype A] in
theorem norm_le_one_of_mem_boundedBooleanWordRowClosure
    (q : List A → Bool) {f : BoundedWordFunction A}
    (hf : f ∈ boundedBooleanWordRowClosure q) : ‖f‖ ≤ 1 := by
  obtain ⟨g, hg, rfl⟩ := hf
  rw [BoundedContinuousFunction.norm_le_of_nonempty]
  intro z
  cases hz : g z <;> norm_num [booleanWordIndicator, boolIndicator, hz]

/-- Shift a Boolean row by appending a letter to its input coordinate. -/
def booleanWordRowShift (a : A) (g : List A → Bool) (z : List A) : Bool :=
  g (z ++ [a])

omit [TopologicalSpace A] [DiscreteTopology A] [Fintype A] [Nonempty A] in
theorem continuous_booleanWordRowShift (a : A) :
    Continuous (booleanWordRowShift (A := A) a) := by
  rw [continuous_pi_iff]
  intro z
  exact continuous_apply (z ++ [a])

omit [TopologicalSpace A] [DiscreteTopology A] [Fintype A] [Nonempty A] in
theorem mapsTo_booleanWordRowShift_range (q : List A → Bool) (a : A) :
    Set.MapsTo (booleanWordRowShift a)
      (Set.range (booleanWordRow q)) (Set.range (booleanWordRow q)) := by
  rintro _ ⟨w, rfl⟩
  refine ⟨[a] ++ w, ?_⟩
  funext z
  simp [booleanWordRowShift, booleanWordRow, List.append_assoc]

omit [TopologicalSpace A] [DiscreteTopology A] [Fintype A] [Nonempty A] in
theorem mapsTo_booleanWordRowShift_closure (q : List A → Bool) (a : A) :
    Set.MapsTo (booleanWordRowShift a)
      (booleanWordRowClosure q) (booleanWordRowClosure q) := by
  exact (mapsTo_booleanWordRowShift_range q a).closure
    (continuous_booleanWordRowShift a)

omit [Fintype A] [Nonempty A] in
/-- The bounded real row closure is invariant under one-letter right
translation. -/
theorem mapsTo_wordRightTranslate_boundedBooleanWordRowClosure
    (q : List A → Bool) (a : A) :
    Set.MapsTo (wordRightTranslate [a])
      (boundedBooleanWordRowClosure q) (boundedBooleanWordRowClosure q) := by
  rintro _ ⟨g, hg, rfl⟩
  refine ⟨booleanWordRowShift a g,
    mapsTo_booleanWordRowShift_closure q a hg, ?_⟩
  ext z
  simp [wordRightTranslate, appendWordRight, booleanWordIndicator, booleanWordRowShift]

omit [Fintype A] [Nonempty A] in
/-- The compact convex hull produced by countable Krein is invariant under
one-letter translations. -/
theorem mapsTo_wordRightTranslate_closedConvexHull
    (q : List A → Bool) (a : A) :
    Set.MapsTo (wordRightTranslate [a])
      (closedConvexHull ℝ (boundedBooleanWordRowClosure q))
      (closedConvexHull ℝ (boundedBooleanWordRowClosure q)) := by
  intro f hf
  have hpre : f ∈ (wordRightTranslateCLM (A := A) [a]) ⁻¹'
      closedConvexHull ℝ (boundedBooleanWordRowClosure q) :=
    closedConvexHull_min
      (fun g hg ↦ by
        show wordRightTranslate [a] g ∈
          closedConvexHull ℝ (boundedBooleanWordRowClosure q)
        exact subset_closedConvexHull
          (mapsTo_wordRightTranslate_boundedBooleanWordRowClosure q a hg))
      ((convex_closedConvexHull (𝕜 := ℝ)
        (s := boundedBooleanWordRowClosure q)).linear_preimage
          (wordRightTranslateCLM (A := A) [a]).toLinearMap)
      ((isClosed_closedConvexHull (𝕜 := ℝ)
        (s := boundedBooleanWordRowClosure q)).preimage
          (wordRightTranslateCLM (A := A) [a]).continuous)
      hf
  exact hpre

/-- IID Cesaro convergence follows from compactness and countability of the
ultrafilter-extension row closure. -/
theorem exists_tendsto_boolean_uniform_iid_word_cesaro_of_extended_closure
    (q : List A → Bool)
    (hcompact : IsCompact (toWeakSpace ℝ C(Ultrafilter (List A), ℝ) ''
      extendedBooleanWordRowClosure q))
    (hcount : (extendedBooleanWordRowClosure q).Countable) :
    ∃ L : ℝ, Tendsto (uniformIidWordCesaro (booleanWordIndicator q)) atTop (𝓝 L) := by
  let K := boundedBooleanWordRowClosure q
  let C := closedConvexHull ℝ K
  have hKcompact : IsCompact (toWeakSpace ℝ (BoundedWordFunction A) '' K) :=
    isCompact_boundedBooleanWordRowClosure_of_extended q hcompact
  have hKcount : K.Countable :=
    countable_boundedBooleanWordRowClosure_of_extended q hcount
  have hKne : K.Nonempty :=
    ⟨booleanWordIndicator q,
      booleanWordIndicator_mem_boundedBooleanWordRowClosure q⟩
  have hCcompact : IsCompact (toWeakSpace ℝ (BoundedWordFunction A) '' C) :=
    IndependentZeroBlocks.Set.Countable.isCompact_toWeakSpace_image_closedConvexHull
      hKcount hKne 1
      (fun f hf ↦ norm_le_one_of_mem_boundedBooleanWordRowClosure q hf)
      hKcompact
  apply exists_tendsto_uniform_iid_word_cesaro
    (booleanWordIndicator q) C hCcompact
    (convex_closedConvexHull (𝕜 := ℝ) (s := K))
    (subset_closedConvexHull
      (s := K) (booleanWordIndicator_mem_boundedBooleanWordRowClosure q))
  intro a f hf
  exact mapsTo_wordRightTranslate_closedConvexHull q a hf

/-- A Boolean word predicate with the double-limit property has a convergent
uniform IID word-length Cesaro density. -/
theorem exists_tendsto_boolean_uniform_iid_word_cesaro
    (q : List A → Bool)
    (hDLP : HasBooleanDoubleLimitProperty (fun w z ↦ q (z ++ w))) :
    ∃ L : ℝ, Tendsto (uniformIidWordCesaro (booleanWordIndicator q)) atTop (𝓝 L) := by
  have hDLP' : HasBooleanDoubleLimitProperty (booleanWordRow q) := by
    change HasBooleanDoubleLimitProperty (fun w z ↦ q (z ++ w))
    exact hDLP
  obtain ⟨hcompact, hcount⟩ :=
    booleanRowClosure_weakly_compact_and_countable (booleanWordRow q) hDLP'
  apply exists_tendsto_boolean_uniform_iid_word_cesaro_of_extended_closure
    q
  · simpa only [extendedBooleanWordRowClosure, booleanWordRowClosure,
      booleanRowExtensionClosure] using hcompact
  · simpa only [extendedBooleanWordRowClosure, booleanWordRowClosure,
      booleanRowExtensionClosure] using hcount

end BooleanWords

end IndependentZeroBlocks
