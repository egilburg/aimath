import SierpinskiFormal.GroupBooleanTranslations
import Mathlib.Topology.Algebra.MulAction

/-! # The compact countable Boolean group flow and its weak embedding -/

noncomputable section

open Set Filter Topology
open scoped BoundedContinuousFunction

namespace IndependentZeroBlocks

theorem continuous_booleanRowWeakExtension
    {X Y : Type*} [Countable Y] (B : X → Y → Bool)
    (hDLP : HasBooleanDoubleLimitProperty B) :
    Continuous (fun g : ↥(closure (Set.range B)) ↦
      toWeakSpace ℝ C(Ultrafilter Y, ℝ) (booleanUltrafilterExtension g.val)) := by
  let K := ↥(closure (Set.range B))
  let row : X → K := fun x ↦ ⟨B x, subset_closure ⟨x, rfl⟩⟩
  letI : TopologicalSpace X := TopologicalSpace.induced row inferInstance
  have hdense : DenseRange row := by
    change Dense (Set.range row)
    rw [Subtype.dense_iff]
    simpa only [← Set.range_comp, Function.comp_def] using
      (Set.Subset.refl (closure (Set.range B)))
  have hdi : IsDenseInducing row := ⟨⟨rfl⟩, hdense⟩
  apply WeakBilin.continuous_of_continuous_eval
  intro l
  apply continuous_of_dense_sequential_limits row hdi
    (fun x ↦ l (booleanUltrafilterExtension (B x)))
    (fun g : K ↦ l (booleanUltrafilterExtension g.val))
  intro u g hu
  have hu' : Tendsto (fun n ↦ B (u n)) atTop (𝓝 g.val) :=
    (continuous_subtype_val.tendsto g).comp hu
  exact booleanRows_tendsto_weak_of_pointwise B hDLP u g.val hu' l

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

abbrev BooleanGroupRightFlow (q : G → Bool) := ↥(booleanGroupRightRowClosure q)

instance booleanGroupRightFlow_compactSpace (q : G → Bool) :
    CompactSpace (BooleanGroupRightFlow q) :=
  isCompact_iff_compactSpace.mp isClosed_closure.isCompact

instance booleanGroupRightFlow_nonempty (q : G → Bool) :
    Nonempty (BooleanGroupRightFlow q) :=
  ⟨⟨booleanGroupRightRow q 1, subset_closure ⟨1, rfl⟩⟩⟩

instance booleanGroupRightFlow_mulAction (q : G → Bool) :
    MulAction G (BooleanGroupRightFlow q) where
  smul g f := ⟨booleanGroupRightShift g f.val,
    mapsTo_booleanGroupRightShift_closure q g f.property⟩
  one_smul f := by
    apply Subtype.ext
    funext z
    change f.val (z * 1) = f.val z
    simp
  mul_smul g h f := by
    apply Subtype.ext
    funext z
    change f.val (z * (g * h)) = f.val ((z * g) * h)
    simp [mul_assoc]

@[simp] theorem booleanGroupRightFlow_smul_apply
    (q : G → Bool) (g z : G) (f : BooleanGroupRightFlow q) :
    (g • f).val z = f.val (z * g) := rfl

instance booleanGroupRightFlow_continuousConstSMul (q : G → Bool) :
    ContinuousConstSMul G (BooleanGroupRightFlow q) where
  continuous_const_smul g :=
    ((continuous_booleanGroupRightShift g).comp continuous_subtype_val).subtype_mk _

theorem booleanGroupRightFlow_countable [Countable G]
    (q : G → Bool)
    (hDLP : HasBooleanDoubleLimitProperty (booleanGroupRightRow q)) :
    Countable (BooleanGroupRightFlow q) :=
  (booleanGroupRightRowClosure_countable q hDLP).to_subtype

def booleanGroupFlowEmbedding (q : G → Bool) (f : BooleanGroupRightFlow q) :
    BoundedGroupFunction G := booleanGroupIndicator f.val

@[simp] theorem booleanGroupFlowEmbedding_apply
    (q : G → Bool) (f : BooleanGroupRightFlow q) (z : G) :
    booleanGroupFlowEmbedding q f z = boolIndicator (f.val z) := rfl

theorem continuous_toWeakSpace_booleanGroupFlowEmbedding [Countable G]
    (q : G → Bool)
    (hDLP : HasBooleanDoubleLimitProperty (booleanGroupRightRow q)) :
    Continuous (fun f : BooleanGroupRightFlow q ↦
      toWeakSpace ℝ (BoundedGroupFunction G) (booleanGroupFlowEmbedding q f)) := by
  have h := (WeakSpace.map (restrictToPure G)).continuous.comp
    (continuous_booleanRowWeakExtension (booleanGroupRightRow q) hDLP)
  convert! h using 1
  funext f
  change booleanGroupFlowEmbedding q f =
    restrictToPure G (booleanUltrafilterExtension f.val)
  ext z
  simp [booleanGroupFlowEmbedding]

theorem booleanGroupFlowEmbedding_smul
    (q : G → Bool) (g : G) (f : BooleanGroupRightFlow q) :
    booleanGroupFlowEmbedding q (g • f) =
      groupRightTranslate g (booleanGroupFlowEmbedding q f) := by
  ext z
  rfl

theorem isCompact_boundedBooleanGroupRightRowClosure [Countable G]
    (q : G → Bool)
    (hDLP : HasBooleanDoubleLimitProperty (booleanGroupRightRow q)) :
    IsCompact (toWeakSpace ℝ (BoundedGroupFunction G) ''
      boundedBooleanGroupRightRowClosure q) := by
  have h := isCompact_univ.image
    (continuous_toWeakSpace_booleanGroupFlowEmbedding q hDLP)
  convert h using 1
  ext f
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨⟨g, hg⟩, Set.mem_univ _, rfl⟩
  · rintro ⟨g, _, rfl⟩
    exact ⟨booleanGroupFlowEmbedding q g, ⟨g.val, g.property, rfl⟩, rfl⟩

theorem countable_boundedBooleanGroupRightRowClosure [Countable G]
    (q : G → Bool)
    (hDLP : HasBooleanDoubleLimitProperty (booleanGroupRightRow q)) :
    (boundedBooleanGroupRightRowClosure q).Countable :=
  (booleanGroupRightRowClosure_countable q hDLP).image _

theorem isCompact_closedConvexHull_boundedBooleanGroupRightRowClosure [Countable G]
    (q : G → Bool)
    (hDLP : HasBooleanDoubleLimitProperty (booleanGroupRightRow q)) :
    IsCompact (toWeakSpace ℝ (BoundedGroupFunction G) ''
      closedConvexHull ℝ (boundedBooleanGroupRightRowClosure q)) := by
  apply IndependentZeroBlocks.Set.Countable.isCompact_toWeakSpace_image_closedConvexHull
    (countable_boundedBooleanGroupRightRowClosure q hDLP)
    ⟨booleanGroupIndicator q, booleanGroupIndicator_mem_boundedBooleanGroupRightRowClosure q⟩
    1 (fun f hf ↦ norm_le_one_of_mem_boundedBooleanGroupRightRowClosure q hf)
    (isCompact_boundedBooleanGroupRightRowClosure q hDLP)

end IndependentZeroBlocks
