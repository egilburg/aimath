import SierpinskiFormal.BooleanWordCesaro
import SierpinskiFormal.GroupBooleanFlow
import SierpinskiFormal.BooleanWeakCompactness
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry

set_option autoImplicit false

/-!
# Paired compacta for stable Boolean word kernels

The left-profile compactum is the pointwise closure of
`w ↦ q (z ++ w)`. Its coordinate functions form a separable Banach space.
Restriction to the dense original profiles is an isometry onto the closed
span of the actual right translates of `q` in bounded word functions.
-/

noncomputable section

open Set Filter Topology
open scoped Topology BoundedContinuousFunction

namespace IndependentZeroBlocks

variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A]

/-- The left profile based at `z`: its `w` coordinate is the kernel value
`q (z ++ w)`. -/
def booleanWordLeftProfile (q : List A → Bool) (z w : List A) : Bool :=
  q (z ++ w)

/-- Pointwise closure of all left profiles. -/
def booleanWordLeftProfileClosure (q : List A → Bool) :
    Set (List A → Bool) :=
  closure (Set.range (booleanWordLeftProfile q))

/-- The compact left-profile space. -/
abbrev BooleanWordLeftCompactum (q : List A → Bool) :=
  booleanWordLeftProfileClosure q

instance booleanWordLeftCompactum_compactSpace (q : List A → Bool) :
    CompactSpace (BooleanWordLeftCompactum q) :=
  isCompact_iff_compactSpace.mp isClosed_closure.isCompact

instance booleanWordLeftCompactum_nonempty (q : List A → Bool) :
    Nonempty (BooleanWordLeftCompactum q) :=
  ⟨⟨booleanWordLeftProfile q [], subset_closure ⟨[], rfl⟩⟩⟩

/-- The original left profile as a point of its compact closure. -/
def booleanWordLeftProfilePoint (q : List A → Bool) (z : List A) :
    BooleanWordLeftCompactum q :=
  ⟨booleanWordLeftProfile q z, subset_closure ⟨z, rfl⟩⟩

@[simp] theorem booleanWordLeftProfilePoint_apply
    (q : List A → Bool) (z w : List A) :
    (booleanWordLeftProfilePoint q z).1 w = q (z ++ w) := rfl

/-- Original left profiles are dense in their defining closure. -/
theorem denseRange_booleanWordLeftProfilePoint (q : List A → Bool) :
    DenseRange (booleanWordLeftProfilePoint q) := by
  intro k
  rw [closure_subtype]
  have himage :
      ((fun x : BooleanWordLeftCompactum q ↦ (x : List A → Bool)) ''
        Set.range (booleanWordLeftProfilePoint q)) =
        Set.range (booleanWordLeftProfile q) := by
    ext g
    constructor
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      exact ⟨z, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨booleanWordLeftProfilePoint q z, ⟨z, rfl⟩, rfl⟩
  rw [himage]
  exact k.property

/-- Under the transposed double-limit property, the compact left-profile
space is countable. -/
theorem booleanWordLeftCompactum_countable [Countable A]
    (q : List A → Bool)
    (hDLP : HasBooleanDoubleLimitProperty (fun w z ↦ q (z ++ w))) :
    Countable (BooleanWordLeftCompactum q) := by
  let B : List A → List A → Bool := booleanWordLeftProfile q
  have hB : HasBooleanDoubleLimitProperty B := by
    intro z w rowLimit columnLimit rowOuter columnOuter
      hrow hcolumn hrowOuter hcolumnOuter
    exact (hDLP w z columnLimit rowLimit columnOuter rowOuter
      hcolumn hrow hcolumnOuter hrowOuter).symm
  have hext : (booleanRowExtensionClosure B).Countable :=
    booleanRowExtensionClosure_countable B hB
  have hpre :
      booleanUltrafilterExtension ⁻¹' booleanRowExtensionClosure B =
        closure (Set.range B) := by
    ext g
    simp only [booleanRowExtensionClosure, Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨h, hh, heq⟩
      have : h = g := booleanUltrafilterExtension_injective heq
      simpa [this] using hh
    · intro hg
      exact ⟨g, hg, rfl⟩
  have hclosure : (closure (Set.range B)).Countable := by
    rw [← hpre]
    exact hext.preimage booleanUltrafilterExtension_injective
  exact Set.countable_coe_iff.mpr (by
    simpa [BooleanWordLeftCompactum, booleanWordLeftProfileClosure, B] using hclosure)

/-- The real coordinate function on the left compactum. -/
def booleanWordLeftCoordinate (q : List A → Bool) (w : List A) :
    C(BooleanWordLeftCompactum q, ℝ) :=
  ⟨fun k ↦ boolIndicator (k.1 w),
    (continuous_of_discreteTopology (f := boolIndicator)).comp
      ((continuous_apply w).comp continuous_subtype_val)⟩

@[simp] theorem booleanWordLeftCoordinate_apply
    (q : List A → Bool) (w : List A) (k : BooleanWordLeftCompactum q) :
    booleanWordLeftCoordinate q w k = boolIndicator (k.1 w) := rfl

/-- Restrict a continuous function on the compact left-profile space to
the dense family of original profiles. -/
def restrictToBooleanWordLeftProfiles (q : List A → Bool) :
    C(BooleanWordLeftCompactum q, ℝ) →L[ℝ] BoundedWordFunction A := by
  let L : C(BooleanWordLeftCompactum q, ℝ) →ₗ[ℝ] BoundedWordFunction A :=
    { toFun := fun F ↦ BoundedContinuousFunction.mkOfDiscrete
        (fun z ↦ F (booleanWordLeftProfilePoint q z)) (2 * ‖F‖)
        (fun z z' ↦ ContinuousMap.dist_le_two_norm F
          (booleanWordLeftProfilePoint q z) (booleanWordLeftProfilePoint q z'))
      map_add' := by intro F G; ext z; rfl
      map_smul' := by intro c F; ext z; rfl }
  exact L.mkContinuous 1 (fun F ↦ by
    rw [BoundedContinuousFunction.norm_le_of_nonempty]
    intro z
    simpa [L] using ContinuousMap.norm_coe_le_norm F
      (booleanWordLeftProfilePoint q z))

@[simp] theorem restrictToBooleanWordLeftProfiles_apply
    (q : List A → Bool) (F : C(BooleanWordLeftCompactum q, ℝ))
    (z : List A) :
    restrictToBooleanWordLeftProfiles q F z =
      F (booleanWordLeftProfilePoint q z) := rfl

/-- Density of the original profiles makes restriction norm-preserving. -/
theorem norm_restrictToBooleanWordLeftProfiles
    (q : List A → Bool) (F : C(BooleanWordLeftCompactum q, ℝ)) :
    ‖restrictToBooleanWordLeftProfiles q F‖ = ‖F‖ := by
  apply le_antisymm
  · rw [BoundedContinuousFunction.norm_eq_iSup_norm]
    exact ciSup_le fun z ↦ ContinuousMap.norm_coe_le_norm F
      (booleanWordLeftProfilePoint q z)
  · rw [ContinuousMap.norm_eq_iSup_norm]
    refine ciSup_le (fun k ↦ ?_)
    let C : Set (BooleanWordLeftCompactum q) :=
      {x | ‖F x‖ ≤ ‖restrictToBooleanWordLeftProfiles q F‖}
    have hC : IsClosed C := isClosed_le
      (continuous_norm.comp F.continuous) continuous_const
    have hrange : Set.range (booleanWordLeftProfilePoint q) ⊆ C := by
      rintro _ ⟨z, rfl⟩
      exact BoundedContinuousFunction.norm_coe_le_norm
        (restrictToBooleanWordLeftProfiles q F) z
    have hclosure := closure_minimal hrange hC
    rw [(denseRange_booleanWordLeftProfilePoint q).closure_range] at hclosure
    exact hclosure (Set.mem_univ k)

/-- Restriction to original profiles as a linear isometry. -/
def restrictToBooleanWordLeftProfilesLI (q : List A → Bool) :
    C(BooleanWordLeftCompactum q, ℝ) →ₗᵢ[ℝ] BoundedWordFunction A :=
  LinearIsometry.mk (restrictToBooleanWordLeftProfiles q).toLinearMap
    (norm_restrictToBooleanWordLeftProfiles q)

/-- Restricting a coordinate gives the corresponding actual right
translate of the Boolean word indicator. -/
@[simp] theorem restrictToBooleanWordLeftProfiles_coordinate
    (q : List A → Bool) (w : List A) :
    restrictToBooleanWordLeftProfiles q (booleanWordLeftCoordinate q w) =
      wordRightTranslate w (booleanWordIndicator q) := by
  ext z
  rfl

/-- Closed coordinate span in `C(K_L)`. This is the norming separable
representation space. -/
def BooleanWordLeftCoordinateSpan (q : List A → Bool) :
    Submodule ℝ C(BooleanWordLeftCompactum q, ℝ) :=
  (Submodule.span ℝ (Set.range (booleanWordLeftCoordinate q))).topologicalClosure

/-- Closed span of the actual right translates in bounded word functions. -/
def BooleanWordRightOrbitSpan (q : List A → Bool) :
    Submodule ℝ (BoundedWordFunction A) :=
  (Submodule.span ℝ
    (Set.range (fun w ↦ wordRightTranslate w (booleanWordIndicator q)))).topologicalClosure

/-- The closed right-orbit span is separable for a countable alphabet. -/
theorem isSeparable_booleanWordRightOrbitSpan [Countable A]
    (q : List A → Bool) :
    TopologicalSpace.IsSeparable
      (BooleanWordRightOrbitSpan q : Set (BoundedWordFunction A)) := by
  exact (Set.countable_range
    (fun w ↦ wordRightTranslate w (booleanWordIndicator q))).isSeparable.span.closure

noncomputable instance booleanWordRightOrbitSpan_separableSpace
    [Countable A] (q : List A → Bool) :
    TopologicalSpace.SeparableSpace (BooleanWordRightOrbitSpan q) :=
  (isSeparable_booleanWordRightOrbitSpan q).separableSpace

noncomputable instance booleanWordRightOrbitSpan_completeSpace
    (q : List A → Bool) : CompleteSpace (BooleanWordRightOrbitSpan q) := by
  unfold BooleanWordRightOrbitSpan
  exact (Submodule.isClosed_topologicalClosure _).completeSpace_coe

/-- The coordinate representation is separable when the alphabet is
countable. -/
theorem isSeparable_booleanWordLeftCoordinateSpan [Countable A]
    (q : List A → Bool) :
    TopologicalSpace.IsSeparable
      (BooleanWordLeftCoordinateSpan q : Set C(BooleanWordLeftCompactum q, ℝ)) := by
  exact (Set.countable_range (booleanWordLeftCoordinate q)).isSeparable.span.closure

noncomputable instance booleanWordLeftCoordinateSpan_separableSpace
    [Countable A] (q : List A → Bool) :
    TopologicalSpace.SeparableSpace (BooleanWordLeftCoordinateSpan q) :=
  (isSeparable_booleanWordLeftCoordinateSpan q).separableSpace

/-- The inclusion of the coordinate span into `C(K_L)` is a linear
isometry. -/
def booleanWordLeftCoordinateSpanInclusion (q : List A → Bool) :
    BooleanWordLeftCoordinateSpan q →ₗᵢ[ℝ]
      C(BooleanWordLeftCompactum q, ℝ) :=
  LinearIsometry.mk (BooleanWordLeftCoordinateSpan q).subtype (fun _ ↦ rfl)

/-- Restriction of the coordinate representation to the original left
profiles. -/
def restrictBooleanWordLeftCoordinateSpanLI (q : List A → Bool) :
    BooleanWordLeftCoordinateSpan q →ₗᵢ[ℝ] BoundedWordFunction A :=
  LinearIsometry.mk
    ((restrictToBooleanWordLeftProfiles q).toLinearMap.comp
      (BooleanWordLeftCoordinateSpan q).subtype)
    (fun F ↦ norm_restrictToBooleanWordLeftProfiles q
      (F : C(BooleanWordLeftCompactum q, ℝ)))

/-- Restriction of the closed coordinate span lands in the closed span of
the actual right translates. -/
theorem restrictBooleanWordLeftCoordinateSpan_mem_rightOrbitSpan
    (q : List A → Bool) (F : BooleanWordLeftCoordinateSpan q) :
    restrictToBooleanWordLeftProfiles q
        (F : C(BooleanWordLeftCompactum q, ℝ)) ∈
      BooleanWordRightOrbitSpan q := by
  let P : Submodule ℝ C(BooleanWordLeftCompactum q, ℝ) :=
    (BooleanWordRightOrbitSpan q).comap
      (restrictToBooleanWordLeftProfiles q).toLinearMap
  have hspan : Submodule.span ℝ (Set.range (booleanWordLeftCoordinate q)) ≤ P := by
    apply Submodule.span_le.2
    rintro _ ⟨w, rfl⟩
    change restrictToBooleanWordLeftProfiles q
        (booleanWordLeftCoordinate q w) ∈ BooleanWordRightOrbitSpan q
    rw [restrictToBooleanWordLeftProfiles_coordinate]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨w, rfl⟩)
  have hrightClosed : IsClosed
      (BooleanWordRightOrbitSpan q : Set (BoundedWordFunction A)) := by
    unfold BooleanWordRightOrbitSpan
    exact Submodule.isClosed_topologicalClosure _
  have hclosed : IsClosed (P : Set C(BooleanWordLeftCompactum q, ℝ)) := by
    change IsClosed ((restrictToBooleanWordLeftProfiles q) ⁻¹'
      (BooleanWordRightOrbitSpan q : Set (BoundedWordFunction A)))
    exact hrightClosed.preimage (restrictToBooleanWordLeftProfiles q).continuous
  exact Submodule.topologicalClosure_minimal _ hspan hclosed F.property

/-- The coordinate representation, with codomain restricted to the closed
right-orbit span. -/
def restrictBooleanWordLeftCoordinateSpanToOrbitLI (q : List A → Bool) :
    BooleanWordLeftCoordinateSpan q →ₗᵢ[ℝ] BooleanWordRightOrbitSpan q :=
  LinearIsometry.mk
    { toFun := fun F ↦
        ⟨restrictToBooleanWordLeftProfiles q
            (F : C(BooleanWordLeftCompactum q, ℝ)),
          restrictBooleanWordLeftCoordinateSpan_mem_rightOrbitSpan q F⟩
      map_add' := by intro F G; ext z; rfl
      map_smul' := by intro c F; ext z; rfl }
    (fun F ↦ norm_restrictToBooleanWordLeftProfiles q
      (F : C(BooleanWordLeftCompactum q, ℝ)))

/-- A coordinate generator bundled in the closed coordinate span. -/
def booleanWordLeftCoordinatePoint (q : List A → Bool) (w : List A) :
    BooleanWordLeftCoordinateSpan q :=
  ⟨booleanWordLeftCoordinate q w,
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨w, rfl⟩)⟩

/-- An actual right translate bundled in its closed orbit span. -/
def booleanWordRightOrbitPoint (q : List A → Bool) (w : List A) :
    BooleanWordRightOrbitSpan q :=
  ⟨wordRightTranslate w (booleanWordIndicator q),
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨w, rfl⟩)⟩

/-- Every actual right translate is represented by its coordinate function. -/
@[simp] theorem restrictBooleanWordLeftCoordinateSpanToOrbitLI_coordinate
    (q : List A → Bool) (w : List A) :
    restrictBooleanWordLeftCoordinateSpanToOrbitLI q
        ⟨booleanWordLeftCoordinate q w,
          Submodule.le_topologicalClosure _
            (Submodule.subset_span ⟨w, rfl⟩)⟩ =
      ⟨wordRightTranslate w (booleanWordIndicator q),
        Submodule.le_topologicalClosure _
          (Submodule.subset_span ⟨w, rfl⟩)⟩ := by
  apply Subtype.ext
  exact restrictToBooleanWordLeftProfiles_coordinate q w

@[simp] theorem restrictBooleanWordLeftCoordinateSpanToOrbitLI_coordinatePoint
    (q : List A → Bool) (w : List A) :
    restrictBooleanWordLeftCoordinateSpanToOrbitLI q
      (booleanWordLeftCoordinatePoint q w) =
      booleanWordRightOrbitPoint q w := by
  apply Subtype.ext
  exact restrictToBooleanWordLeftProfiles_coordinate q w

/-- The restricted coordinate representation is onto the closed
right-orbit span. -/
theorem restrictBooleanWordLeftCoordinateSpanToOrbitLI_surjective
    (q : List A → Bool) :
    Function.Surjective (restrictBooleanWordLeftCoordinateSpanToOrbitLI q) := by
  let J := restrictBooleanWordLeftCoordinateSpanLI q
  have hsourceClosed : IsClosed
      (BooleanWordLeftCoordinateSpan q :
        Set C(BooleanWordLeftCompactum q, ℝ)) := by
    unfold BooleanWordLeftCoordinateSpan
    exact Submodule.isClosed_topologicalClosure _
  letI : CompleteSpace (BooleanWordLeftCoordinateSpan q) :=
    hsourceClosed.completeSpace_coe
  have hrangeClosedSet : IsClosed (Set.range J) :=
    J.isometry.isUniformInducing.isComplete_range.isClosed
  have hrangeClosed : IsClosed
      (LinearMap.range J.toLinearMap : Set (BoundedWordFunction A)) := by
    exact hrangeClosedSet
  have hspan : Submodule.span ℝ
      (Set.range (fun w ↦ wordRightTranslate w (booleanWordIndicator q))) ≤
      LinearMap.range J.toLinearMap := by
    apply Submodule.span_le.2
    rintro _ ⟨w, rfl⟩
    refine ⟨⟨booleanWordLeftCoordinate q w,
      Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨w, rfl⟩)⟩, ?_⟩
    exact restrictToBooleanWordLeftProfiles_coordinate q w
  have honto : BooleanWordRightOrbitSpan q ≤ LinearMap.range J.toLinearMap := by
    exact Submodule.topologicalClosure_minimal _ hspan hrangeClosed
  intro y
  obtain ⟨F, hF⟩ := honto y.property
  refine ⟨F, ?_⟩
  apply Subtype.ext
  exact hF

/-- The norming coordinate representation and the original closed
right-orbit span are linearly isometrically equivalent. -/
noncomputable def booleanWordPairedCompactaEquiv (q : List A → Bool) :
    BooleanWordLeftCoordinateSpan q ≃ₗᵢ[ℝ] BooleanWordRightOrbitSpan q :=
  LinearIsometryEquiv.ofSurjective
    (restrictBooleanWordLeftCoordinateSpanToOrbitLI q)
    (restrictBooleanWordLeftCoordinateSpanToOrbitLI_surjective q)

/-- The closed right-orbit span embedded isometrically in continuous
functions on the compact left-profile space. This is the norming embedding
used by the positive Hahn--Banach construction. -/
noncomputable def booleanWordRightOrbitNormingLI (q : List A → Bool) :
    BooleanWordRightOrbitSpan q →ₗᵢ[ℝ]
      C(BooleanWordLeftCompactum q, ℝ) :=
  (booleanWordLeftCoordinateSpanInclusion q).comp
    (booleanWordPairedCompactaEquiv q).symm.toLinearIsometry

/-- The norming embedding sends each actual right translate to its
corresponding coordinate function on the left compactum. -/
@[simp] theorem booleanWordRightOrbitNormingLI_orbitPoint
    (q : List A → Bool) (w : List A) :
    booleanWordRightOrbitNormingLI q (booleanWordRightOrbitPoint q w) =
      booleanWordLeftCoordinate q w := by
  have hpair : booleanWordPairedCompactaEquiv q
      (booleanWordLeftCoordinatePoint q w) =
      booleanWordRightOrbitPoint q w := by
    change restrictBooleanWordLeftCoordinateSpanToOrbitLI q
      (booleanWordLeftCoordinatePoint q w) =
      booleanWordRightOrbitPoint q w
    exact restrictBooleanWordLeftCoordinateSpanToOrbitLI_coordinatePoint q w
  rw [← hpair]
  change (((booleanWordPairedCompactaEquiv q).symm
    ((booleanWordPairedCompactaEquiv q)
      (booleanWordLeftCoordinatePoint q w)) :
        BooleanWordLeftCoordinateSpan q) :
      C(BooleanWordLeftCompactum q, ℝ)) = booleanWordLeftCoordinate q w
  rw [LinearIsometryEquiv.symm_apply_apply]
  rfl

/-- Evaluation on the compact left-profile space norms every vector in the
closed right-orbit span. -/
theorem booleanWordRightOrbit_norm_eq_iSup_norming_eval
    (q : List A → Bool) (f : BooleanWordRightOrbitSpan q) :
    ‖f‖ = ⨆ k : BooleanWordLeftCompactum q,
      ‖booleanWordRightOrbitNormingLI q f k‖ := by
  rw [← (booleanWordRightOrbitNormingLI q).norm_map f]
  exact ContinuousMap.norm_eq_iSup_norm (booleanWordRightOrbitNormingLI q f)

/-- The raw pointwise right-row closure, before embedding in bounded word
functions. -/
abbrev BooleanWordRawRightCompactum (q : List A → Bool) :=
  booleanWordRowClosure q

instance booleanWordRawRightCompactum_compactSpace (q : List A → Bool) :
    CompactSpace (BooleanWordRawRightCompactum q) :=
  isCompact_iff_compactSpace.mp isClosed_closure.isCompact

instance booleanWordRawRightCompactum_nonempty (q : List A → Bool) :
    Nonempty (BooleanWordRawRightCompactum q) :=
  ⟨⟨booleanWordRow q [], subset_closure ⟨[], rfl⟩⟩⟩

/-- A raw Boolean right-row profile as a bounded real word function. -/
def booleanWordRawRightEmbedding (q : List A → Bool)
    (g : BooleanWordRawRightCompactum q) : BoundedWordFunction A :=
  booleanWordIndicator g.val

@[simp] theorem booleanWordRawRightEmbedding_apply
    (q : List A → Bool) (g : BooleanWordRawRightCompactum q) (z : List A) :
    booleanWordRawRightEmbedding q g z = boolIndicator (g.val z) := rfl

/-- Under stability, every raw pointwise right-row limit belongs to the
norm-closed linear span of the actual right translates. -/
theorem booleanWordRawRightEmbedding_mem_rightOrbitSpan [Countable A]
    (q : List A → Bool)
    (hDLP : HasBooleanDoubleLimitProperty (fun w z ↦ q (z ++ w)))
    (g : BooleanWordRawRightCompactum q) :
    booleanWordRawRightEmbedding q g ∈ BooleanWordRightOrbitSpan q := by
  have hext := booleanRowExtensionClosure_subset_weak_closure
    (booleanWordRow q) hDLP (booleanUltrafilterExtension g.val)
      ⟨g.val, g.property, rfl⟩
  have hres := mem_closure_image
    (WeakSpace.map (restrictToPure (List A))).continuous.continuousAt hext
  have htarget :
      WeakSpace.map (restrictToPure (List A)) ''
        (toWeakSpace ℝ C(Ultrafilter (List A), ℝ) ''
          Set.range (fun w ↦
            booleanUltrafilterExtension (booleanWordRow q w))) =
      toWeakSpace ℝ (BoundedWordFunction A) ''
        Set.range (fun w ↦
          wordRightTranslate w (booleanWordIndicator q)) := by
    ext u
    constructor
    · rintro ⟨_, ⟨_, ⟨w, rfl⟩, rfl⟩, rfl⟩
      refine ⟨wordRightTranslate w (booleanWordIndicator q), ⟨w, rfl⟩, ?_⟩
      change wordRightTranslate w (booleanWordIndicator q) =
        restrictToPure (List A)
          (booleanUltrafilterExtension (booleanWordRow q w))
      ext z
      simp [booleanWordRow, wordRightTranslate_apply]
    · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
      refine ⟨toWeakSpace ℝ C(Ultrafilter (List A), ℝ)
          (booleanUltrafilterExtension (booleanWordRow q w)),
        ⟨_, ⟨w, rfl⟩, rfl⟩, ?_⟩
      change restrictToPure (List A)
          (booleanUltrafilterExtension (booleanWordRow q w)) =
        wordRightTranslate w (booleanWordIndicator q)
      ext z
      simp [booleanWordRow, wordRightTranslate_apply]
  rw [htarget] at hres
  have heq : WeakSpace.map (restrictToPure (List A))
      (toWeakSpace ℝ C(Ultrafilter (List A), ℝ)
        (booleanUltrafilterExtension g.val)) =
      toWeakSpace ℝ (BoundedWordFunction A)
        (booleanWordRawRightEmbedding q g) := by
    change restrictToPure (List A) (booleanUltrafilterExtension g.val) =
      booleanWordIndicator g.val
    ext z
    simp
  rw [heq] at hres
  let V : Submodule ℝ (BoundedWordFunction A) :=
    Submodule.span ℝ
      (Set.range (fun w ↦ wordRightTranslate w (booleanWordIndicator q)))
  have hmono : toWeakSpace ℝ (BoundedWordFunction A) ''
      Set.range (fun w ↦ wordRightTranslate w (booleanWordIndicator q)) ⊆
      toWeakSpace ℝ (BoundedWordFunction A) '' (V : Set _) := by
    exact Set.image_mono Submodule.subset_span
  have hv := closure_mono hmono hres
  rw [← V.convex.toWeakSpace_closure ℝ] at hv
  obtain ⟨f, hf, hfg⟩ := hv
  have hfg' : f = booleanWordRawRightEmbedding q g :=
    (toWeakSpace ℝ (BoundedWordFunction A)).injective hfg
  change booleanWordRawRightEmbedding q g ∈ closure (V : Set _)
  simpa only [hfg'] using hf

/-- The raw right-row closure lifted to the actual orbit Banach space. -/
def booleanWordRawRightOrbitLift [Countable A]
    (q : List A → Bool)
    (hDLP : HasBooleanDoubleLimitProperty (fun w z ↦ q (z ++ w)))
    (g : BooleanWordRawRightCompactum q) : BooleanWordRightOrbitSpan q :=
  ⟨booleanWordRawRightEmbedding q g,
    booleanWordRawRightEmbedding_mem_rightOrbitSpan q hDLP g⟩

@[simp] theorem booleanWordRawRightOrbitLift_apply [Countable A]
    (q : List A → Bool)
    (hDLP : HasBooleanDoubleLimitProperty (fun w z ↦ q (z ++ w)))
    (g : BooleanWordRawRightCompactum q) (z : List A) :
    (booleanWordRawRightOrbitLift q hDLP g : BoundedWordFunction A) z =
      boolIndicator (g.val z) := rfl

/-- The raw right-row embedding is continuous from the pointwise compactum
to the weak topology of bounded word functions. -/
theorem continuous_toWeakSpace_booleanWordRawRightEmbedding [Countable A]
    (q : List A → Bool)
    (hDLP : HasBooleanDoubleLimitProperty (fun w z ↦ q (z ++ w))) :
    Continuous (fun g : BooleanWordRawRightCompactum q ↦
      toWeakSpace ℝ (BoundedWordFunction A)
        (booleanWordRawRightEmbedding q g)) := by
  have h := (WeakSpace.map (restrictToPure (List A))).continuous.comp
    (continuous_booleanRowWeakExtension (booleanWordRow q) hDLP)
  convert! h using 1
  funext g
  change booleanWordRawRightEmbedding q g =
    restrictToPure (List A) (booleanUltrafilterExtension g.val)
  ext z
  simp [booleanWordRawRightEmbedding]

/-- After lifting to the closed orbit span, the raw right-row map remains
weakly continuous. Hahn--Banach extends each functional on the span to the
ambient bounded-function space. -/
theorem continuous_toWeakSpace_booleanWordRawRightOrbitLift [Countable A]
    (q : List A → Bool)
    (hDLP : HasBooleanDoubleLimitProperty (fun w z ↦ q (z ++ w))) :
    Continuous (fun g : BooleanWordRawRightCompactum q ↦
      toWeakSpace ℝ (BooleanWordRightOrbitSpan q)
        (booleanWordRawRightOrbitLift q hDLP g)) := by
  apply WeakBilin.continuous_of_continuous_eval
  intro l
  obtain ⟨L, hL, _⟩ :=
    exists_extension_norm_eq (BooleanWordRightOrbitSpan q) l
  have hc :=
    (WeakBilin.eval_continuous
      (topDualPairing ℝ (BoundedWordFunction A)).flip L).comp
      (continuous_toWeakSpace_booleanWordRawRightEmbedding q hDLP)
  convert hc using 1
  funext g
  exact (hL (booleanWordRawRightOrbitLift q hDLP g)).symm

/-- Evaluation on `K_L` is norming for the coordinate representation. -/
theorem booleanWordLeftCoordinateSpan_norm_eq_iSup_eval
    (q : List A → Bool) (F : BooleanWordLeftCoordinateSpan q) :
    ‖F‖ = ⨆ k : BooleanWordLeftCompactum q, ‖(F :
      C(BooleanWordLeftCompactum q, ℝ)) k‖ := by
  change ‖(F : C(BooleanWordLeftCompactum q, ℝ))‖ = _
  exact ContinuousMap.norm_eq_iSup_norm
    (F : C(BooleanWordLeftCompactum q, ℝ))

end IndependentZeroBlocks
