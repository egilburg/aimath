import SierpinskiFormal.GroupFiniteOrbitAverage

/-! # Inversion transfers finite right orbits to rational left averages -/

noncomputable section

open Set Filter Topology
open scoped BoundedContinuousFunction

namespace IndependentZeroBlocks

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

def groupInversionCLM : BoundedGroupFunction G →L[ℝ] BoundedGroupFunction G :=
  ({ toFun := fun f ↦
       f.compContinuous ⟨fun z ↦ z⁻¹, continuous_of_discreteTopology⟩
     map_add' := by intros; ext z; rfl
     map_smul' := by intros; ext z; rfl } :
    BoundedGroupFunction G →ₗ[ℝ] BoundedGroupFunction G).mkContinuous 1 (by
      intro f
      simpa using BoundedContinuousFunction.norm_compContinuous_le f
        ⟨fun z ↦ z⁻¹, continuous_of_discreteTopology⟩)

@[simp] theorem groupInversionCLM_apply (f : BoundedGroupFunction G) (z : G) :
    groupInversionCLM f z = f z⁻¹ := rfl

@[simp] theorem groupInversionCLM_involution (f : BoundedGroupFunction G) :
    groupInversionCLM (groupInversionCLM f) = f := by
  ext z
  simp

theorem groupInversionCLM_rightTranslate (g : G) (f : BoundedGroupFunction G) :
    groupInversionCLM (groupRightTranslate g f) =
      groupLeftTranslate g⁻¹ (groupInversionCLM f) := by
  ext z
  simp

def inverseGroupPredicate (q : G → Bool) (g : G) : Bool := q g⁻¹

theorem inverseGroupPredicate_hasBooleanDoubleLimitProperty
    (q : G → Bool)
    (hDLP : HasBooleanDoubleLimitProperty (booleanGroupRightRow q)) :
    HasBooleanDoubleLimitProperty (booleanGroupRightRow (inverseGroupPredicate q)) := by
  intro x y row col a b hrow hcol ha hb
  apply Eq.symm
  apply hDLP (fun n ↦ (y n)⁻¹) (fun n ↦ (x n)⁻¹) col row b a
  · intro i
    simpa [booleanGroupRightRow, inverseGroupPredicate] using hcol i
  · intro i
    simpa [booleanGroupRightRow, inverseGroupPredicate] using hrow i
  · exact hb
  · exact ha

@[simp] theorem groupInversionCLM_inverseIndicator (q : G → Bool) :
    groupInversionCLM (booleanGroupIndicator (inverseGroupPredicate q)) =
      booleanGroupIndicator q := by
  ext z
  simp [inverseGroupPredicate]

theorem inverse_finiteAverage_mem_closedConvexHull_leftOrbit [Countable G]
    (q : G → Bool)
    (hDLP : HasBooleanDoubleLimitProperty (booleanGroupRightRow q))
    (F : Finset (BooleanGroupRightFlow (inverseGroupPredicate q)))
    (hFne : F.Nonempty)
    (hF : ∀ g : G, Set.MapsTo
      (fun f : BooleanGroupRightFlow (inverseGroupPredicate q) ↦ g • f)
      (F : Set _) (F : Set _)) :
    groupFlowFiniteAverage (inverseGroupPredicate q) F ∈
      closedConvexHull ℝ (Set.range (fun g ↦ groupLeftTranslate g (booleanGroupIndicator q))) := by
  have hmem := groupFlowFiniteAverage_mem_closedConvexHull_orbit
    (inverseGroupPredicate q) (inverseGroupPredicate_hasBooleanDoubleLimitProperty q hDLP) F hFne
  have hmap : Set.MapsTo (groupInversionCLM (G := G))
      (Set.range (fun g ↦ groupRightTranslate g (booleanGroupIndicator (inverseGroupPredicate q))))
      (Set.range (fun g ↦ groupLeftTranslate g (booleanGroupIndicator q))) := by
    rintro _ ⟨g, rfl⟩
    refine ⟨g⁻¹, ?_⟩
    simp [groupInversionCLM_rightTranslate]
  have hh := mapsTo_closedConvexHulls_of_mapsTo groupInversionCLM hmap hmem
  have heq : groupInversionCLM (groupFlowFiniteAverage (inverseGroupPredicate q) F) =
      groupFlowFiniteAverage (inverseGroupPredicate q) F := by
    ext z
    simp only [groupInversionCLM_apply]
    rw [groupFlowFiniteAverage_constant _ F hF z⁻¹,
      groupFlowFiniteAverage_constant _ F hF z]
  simpa only [heq] using hh

/-- A finite orbit in the inverse-predicate flow fixes the value of every
right-invariant point in the closed convex right orbit. -/
theorem invariant_rightHull_eq_inverse_finiteAverage [Countable G]
    (q : G → Bool)
    (hDLP : HasBooleanDoubleLimitProperty (booleanGroupRightRow q))
    (F : Finset (BooleanGroupRightFlow (inverseGroupPredicate q)))
    (hFne : F.Nonempty)
    (hF : ∀ g : G, Set.MapsTo
      (fun f : BooleanGroupRightFlow (inverseGroupPredicate q) ↦ g • f)
      (F : Set _) (F : Set _))
    (a : BoundedGroupFunction G)
    (ha : a ∈ closedConvexHull ℝ
      (Set.range (fun g ↦ groupRightTranslate g (booleanGroupIndicator q))))
    (hainv : ∀ g, groupRightTranslate g a = a) :
    a = groupFlowFiniteAverage (inverseGroupPredicate q) F := by
  apply eq_of_mem_commuting_closedConvexHulls
    (groupLeftTranslateCLM (G := G)) (groupRightTranslateCLM (G := G))
    (booleanGroupIndicator q) a (groupFlowFiniteAverage (inverseGroupPredicate q) F)
  · intro g h f
    exact groupLeftRightTranslate_commute g h f
  · exact groupRightTranslateCLM_norm_le
  · intro g
    ext z
    simp only [groupLeftTranslateCLM_apply, groupLeftTranslate_apply]
    rw [groupRight_invariant_is_constant a hainv (g * z),
      groupRight_invariant_is_constant a hainv z]
  · intro g
    exact groupFlowFiniteAverage_invariant (inverseGroupPredicate q) F hF g
  · exact ha
  · exact inverse_finiteAverage_mem_closedConvexHull_leftOrbit q hDLP F hFne hF

end IndependentZeroBlocks
