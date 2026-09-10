import SierpinskiFormal.BooleanWordCesaro
import SierpinskiFormal.CommutingConvexAverages

/-! # Left and right translation hulls of Boolean group predicates -/

noncomputable section

open Set Filter Topology
open scoped BoundedContinuousFunction

namespace IndependentZeroBlocks

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

abbrev BoundedGroupFunction (G : Type*) [TopologicalSpace G] := G →ᵇ ℝ

def booleanGroupIndicator (q : G → Bool) : BoundedGroupFunction G :=
  BoundedContinuousFunction.mkOfDiscrete (fun g ↦ boolIndicator (q g)) 1 (by
    intro x y
    cases hx : q x <;> cases hy : q y <;>
      norm_num [boolIndicator, Real.dist_eq, hx, hy])

@[simp] theorem booleanGroupIndicator_apply (q : G → Bool) (g : G) :
    booleanGroupIndicator q g = boolIndicator (q g) := rfl

def groupRightTranslate (g : G) (f : BoundedGroupFunction G) :
    BoundedGroupFunction G :=
  f.compContinuous ⟨fun z ↦ z * g, continuous_of_discreteTopology⟩

def groupLeftTranslate (g : G) (f : BoundedGroupFunction G) :
    BoundedGroupFunction G :=
  f.compContinuous ⟨fun z ↦ g * z, continuous_of_discreteTopology⟩

@[simp] theorem groupRightTranslate_apply (g z : G) (f : BoundedGroupFunction G) :
    groupRightTranslate g f z = f (z * g) := rfl

@[simp] theorem groupLeftTranslate_apply (g z : G) (f : BoundedGroupFunction G) :
    groupLeftTranslate g f z = f (g * z) := rfl

def groupRightTranslateCLM (g : G) :
    BoundedGroupFunction G →L[ℝ] BoundedGroupFunction G :=
  ({ toFun := groupRightTranslate g
     map_add' := by intros; ext z; rfl
     map_smul' := by intros; ext z; rfl } :
    BoundedGroupFunction G →ₗ[ℝ] BoundedGroupFunction G).mkContinuous 1 (by
      intro f
      simpa [groupRightTranslate] using
        BoundedContinuousFunction.norm_compContinuous_le f
          ⟨fun z ↦ z * g, continuous_of_discreteTopology⟩)

def groupLeftTranslateCLM (g : G) :
    BoundedGroupFunction G →L[ℝ] BoundedGroupFunction G :=
  ({ toFun := groupLeftTranslate g
     map_add' := by intros; ext z; rfl
     map_smul' := by intros; ext z; rfl } :
    BoundedGroupFunction G →ₗ[ℝ] BoundedGroupFunction G).mkContinuous 1 (by
      intro f
      simpa [groupLeftTranslate] using
        BoundedContinuousFunction.norm_compContinuous_le f
          ⟨fun z ↦ g * z, continuous_of_discreteTopology⟩)

@[simp] theorem groupRightTranslateCLM_apply (g : G) (f : BoundedGroupFunction G) :
    groupRightTranslateCLM g f = groupRightTranslate g f := rfl

@[simp] theorem groupLeftTranslateCLM_apply (g : G) (f : BoundedGroupFunction G) :
    groupLeftTranslateCLM g f = groupLeftTranslate g f := rfl

theorem groupRightTranslateCLM_norm_le (g : G) : ‖groupRightTranslateCLM g‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa [groupRightTranslateCLM, groupRightTranslate] using
    BoundedContinuousFunction.norm_compContinuous_le f
      ⟨fun z ↦ z * g, continuous_of_discreteTopology⟩

theorem groupLeftTranslateCLM_norm_le (g : G) : ‖groupLeftTranslateCLM g‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa [groupLeftTranslateCLM, groupLeftTranslate] using
    BoundedContinuousFunction.norm_compContinuous_le f
      ⟨fun z ↦ g * z, continuous_of_discreteTopology⟩

theorem groupLeftRightTranslate_commute (g h : G) (f : BoundedGroupFunction G) :
    groupLeftTranslateCLM g (groupRightTranslateCLM h f) =
      groupRightTranslateCLM h (groupLeftTranslateCLM g f) := by
  ext z
  simp [mul_assoc]

@[simp] theorem groupRightTranslate_one (f : BoundedGroupFunction G) :
    groupRightTranslate 1 f = f := by
  ext z
  simp

theorem groupRightTranslate_mul (g h : G) (f : BoundedGroupFunction G) :
    groupRightTranslate g (groupRightTranslate h f) =
      groupRightTranslate (g * h) f := by
  ext z
  simp [mul_assoc]

theorem groupRightTranslate_bijective (g : G) :
    Function.Bijective (groupRightTranslate g : BoundedGroupFunction G → _) := by
  have hi : Function.LeftInverse (groupRightTranslate g⁻¹) (groupRightTranslate g) := by
    intro f
    simp [groupRightTranslate_mul]
  have hs : Function.RightInverse (groupRightTranslate g⁻¹) (groupRightTranslate g) := by
    intro f
    simp [groupRightTranslate_mul]
  exact ⟨hi.injective, hs.surjective⟩

def booleanGroupRightRow (q : G → Bool) (g z : G) : Bool := q (z * g)

def booleanGroupRightRowClosure (q : G → Bool) : Set (G → Bool) :=
  closure (Set.range (booleanGroupRightRow q))

def boundedBooleanGroupRightRowClosure (q : G → Bool) : Set (BoundedGroupFunction G) :=
  booleanGroupIndicator '' booleanGroupRightRowClosure q

def booleanGroupRightShift (g : G) (f : G → Bool) (z : G) : Bool := f (z * g)

theorem continuous_booleanGroupRightShift (g : G) :
    Continuous (booleanGroupRightShift g) := by
  rw [continuous_pi_iff]
  intro z
  exact continuous_apply (z * g)

theorem mapsTo_booleanGroupRightShift_closure (q : G → Bool) (g : G) :
    Set.MapsTo (booleanGroupRightShift g)
      (booleanGroupRightRowClosure q) (booleanGroupRightRowClosure q) := by
  apply Set.MapsTo.closure ?_ (continuous_booleanGroupRightShift g)
  rintro _ ⟨h, rfl⟩
  refine ⟨g * h, ?_⟩
  funext z
  simp [booleanGroupRightShift, booleanGroupRightRow, mul_assoc]

theorem booleanGroupIndicator_mem_boundedBooleanGroupRightRowClosure (q : G → Bool) :
    booleanGroupIndicator q ∈ boundedBooleanGroupRightRowClosure q := by
  refine ⟨booleanGroupRightRow q 1, subset_closure ⟨1, rfl⟩, ?_⟩
  ext z
  simp [booleanGroupRightRow]

theorem mapsTo_groupRightTranslate_boundedBooleanGroupRightRowClosure
    (q : G → Bool) (g : G) :
    Set.MapsTo (groupRightTranslate g)
      (boundedBooleanGroupRightRowClosure q) (boundedBooleanGroupRightRowClosure q) := by
  rintro _ ⟨f, hf, rfl⟩
  refine ⟨booleanGroupRightShift g f,
    mapsTo_booleanGroupRightShift_closure q g hf, ?_⟩
  ext z
  rfl

theorem norm_le_one_of_mem_boundedBooleanGroupRightRowClosure
    (q : G → Bool) {f : BoundedGroupFunction G}
    (hf : f ∈ boundedBooleanGroupRightRowClosure q) : ‖f‖ ≤ 1 := by
  obtain ⟨g, hg, rfl⟩ := hf
  rw [BoundedContinuousFunction.norm_le_of_nonempty]
  intro z
  cases hz : g z <;> norm_num [boolIndicator, hz]

theorem booleanGroupRightRowClosure_countable [Countable G]
    (q : G → Bool)
    (hDLP : HasBooleanDoubleLimitProperty (booleanGroupRightRow q)) :
    (booleanGroupRightRowClosure q).Countable := by
  have hc := booleanRowExtensionClosure_countable (booleanGroupRightRow q) hDLP
  exact Set.countable_of_injective_of_countable_image
    (fun f hf g hg hfg ↦ booleanUltrafilterExtension_injective hfg) hc

theorem groupRight_invariant_is_constant (f : BoundedGroupFunction G)
    (hf : ∀ g, groupRightTranslate g f = f) (z : G) : f z = f 1 := by
  have h := congrArg (fun u : BoundedGroupFunction G ↦ u 1) (hf z)
  simpa using h

end IndependentZeroBlocks
