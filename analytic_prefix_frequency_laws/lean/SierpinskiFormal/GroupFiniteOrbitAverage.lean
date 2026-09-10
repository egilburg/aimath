import SierpinskiFormal.GroupBooleanFlow

/-! # Rational constants supplied by finite Boolean group orbits -/

noncomputable section

open Set Filter Topology
open scoped BigOperators BoundedContinuousFunction

namespace IndependentZeroBlocks

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

def groupFlowFiniteAverage (q : G → Bool) (F : Finset (BooleanGroupRightFlow q)) :
    BoundedGroupFunction G :=
  (F.card : ℝ)⁻¹ • ∑ f ∈ F, booleanGroupFlowEmbedding q f

theorem groupFlowFiniteAverage_invariant
    (q : G → Bool) (F : Finset (BooleanGroupRightFlow q))
    (hF : ∀ g : G, Set.MapsTo (fun f : BooleanGroupRightFlow q ↦ g • f)
      (F : Set _) (F : Set _)) (g : G) :
    groupRightTranslate g (groupFlowFiniteAverage q F) = groupFlowFiniteAverage q F := by
  classical
  have hsum : (∑ f ∈ F, booleanGroupFlowEmbedding q (g • f)) =
      ∑ f ∈ F, booleanGroupFlowEmbedding q f := by
    apply Finset.sum_bij (fun f hf ↦ g • f)
    · intro f hf
      exact hF g hf
    · intro f hf f' hf' he
      have hh := congrArg (fun x : BooleanGroupRightFlow q ↦ g⁻¹ • x) he
      simpa only [inv_smul_smul] using hh
    · intro f hf
      exact ⟨g⁻¹ • f, hF g⁻¹ hf, smul_inv_smul g f⟩
    · intro f hf
      rfl
  change groupRightTranslateCLM g ((F.card : ℝ)⁻¹ •
      ∑ f ∈ F, booleanGroupFlowEmbedding q f) = _
  rw [map_smul, map_sum]
  simp only [groupRightTranslateCLM_apply, ← booleanGroupFlowEmbedding_smul, hsum]
  rfl

theorem groupFlowFiniteAverage_constant
    (q : G → Bool) (F : Finset (BooleanGroupRightFlow q))
    (hF : ∀ g : G, Set.MapsTo (fun f : BooleanGroupRightFlow q ↦ g • f)
      (F : Set _) (F : Set _)) (z : G) :
    groupFlowFiniteAverage q F z = groupFlowFiniteAverage q F 1 :=
  groupRight_invariant_is_constant _ (groupFlowFiniteAverage_invariant q F hF) z

theorem groupFlowFiniteAverage_rational
    (q : G → Bool) (F : Finset (BooleanGroupRightFlow q)) (z : G) :
    ∃ r : ℚ, groupFlowFiniteAverage q F z = (r : ℝ) := by
  classical
  refine ⟨((F.filter (fun f ↦ f.val z = true)).card : ℚ) / (F.card : ℚ), ?_⟩
  simp only [groupFlowFiniteAverage, BoundedContinuousFunction.smul_apply,
    BoundedContinuousFunction.sum_apply, booleanGroupFlowEmbedding_apply,
    boolIndicator, smul_eq_mul]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Rat.cast_div, Rat.cast_natCast]
  ring

theorem groupFlowFiniteAverage_mem_closedConvexHull
    (q : G → Bool) (F : Finset (BooleanGroupRightFlow q)) (hF : F.Nonempty) :
    groupFlowFiniteAverage q F ∈
      closedConvexHull ℝ (boundedBooleanGroupRightRowClosure q) := by
  classical
  unfold groupFlowFiniteAverage
  rw [Finset.smul_sum]
  apply (convex_closedConvexHull (𝕜 := ℝ)
    (s := boundedBooleanGroupRightRowClosure q)).sum_mem
  · intro f hf
    positivity
  · simp [Finset.card_ne_zero.mpr hF]
  · intro f hf
    exact subset_closedConvexHull ⟨f.val, f.property, rfl⟩

/-- Every point of the weak Boolean closure is in the norm-closed convex
hull of the original right translates. -/
theorem boundedBooleanGroupRightRowClosure_subset_closedConvexHull_orbit [Countable G]
    (q : G → Bool)
    (hDLP : HasBooleanDoubleLimitProperty (booleanGroupRightRow q)) :
    boundedBooleanGroupRightRowClosure q ⊆
      closedConvexHull ℝ (Set.range (fun g ↦ groupRightTranslate g (booleanGroupIndicator q))) := by
  rintro _ ⟨f, hf, rfl⟩
  have hext := booleanRowExtensionClosure_subset_weak_closure
    (booleanGroupRightRow q) hDLP (booleanUltrafilterExtension f) ⟨f, hf, rfl⟩
  have hres := mem_closure_image
    (WeakSpace.map (restrictToPure G)).continuous.continuousAt hext
  have htarget :
      WeakSpace.map (restrictToPure G) ''
        (toWeakSpace ℝ C(Ultrafilter G, ℝ) ''
          Set.range (fun g ↦ booleanUltrafilterExtension (booleanGroupRightRow q g))) =
      toWeakSpace ℝ (BoundedGroupFunction G) ''
        Set.range (fun g ↦ groupRightTranslate g (booleanGroupIndicator q)) := by
    ext u
    constructor
    · rintro ⟨_, ⟨_, ⟨g, rfl⟩, rfl⟩, rfl⟩
      refine ⟨groupRightTranslate g (booleanGroupIndicator q), ⟨g, rfl⟩, ?_⟩
      change groupRightTranslate g (booleanGroupIndicator q) =
        restrictToPure G (booleanUltrafilterExtension (booleanGroupRightRow q g))
      ext z
      simp [booleanGroupRightRow]
    · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
      refine ⟨toWeakSpace ℝ C(Ultrafilter G, ℝ)
        (booleanUltrafilterExtension (booleanGroupRightRow q g)),
        ⟨_, ⟨g, rfl⟩, rfl⟩, ?_⟩
      change restrictToPure G (booleanUltrafilterExtension (booleanGroupRightRow q g)) =
        groupRightTranslate g (booleanGroupIndicator q)
      ext z
      simp [booleanGroupRightRow]
  rw [htarget] at hres
  have heq : WeakSpace.map (restrictToPure G)
      (toWeakSpace ℝ C(Ultrafilter G, ℝ) (booleanUltrafilterExtension f)) =
      toWeakSpace ℝ (BoundedGroupFunction G) (booleanGroupIndicator f) := by
    change restrictToPure G (booleanUltrafilterExtension f) = booleanGroupIndicator f
    ext z
    simp
  rw [heq] at hres
  have hconv := closure_mono (subset_convexHull ℝ
    (toWeakSpace ℝ (BoundedGroupFunction G) ''
      Set.range (fun g ↦ groupRightTranslate g (booleanGroupIndicator q)))) hres
  rw [← toWeakSpace_image_closedConvexHull] at hconv
  obtain ⟨u, hu, he⟩ := hconv
  have hueq : u = booleanGroupIndicator f :=
    (toWeakSpace ℝ (BoundedGroupFunction G)).injective he
  simpa only [hueq] using hu

theorem groupFlowFiniteAverage_mem_closedConvexHull_orbit [Countable G]
    (q : G → Bool)
    (hDLP : HasBooleanDoubleLimitProperty (booleanGroupRightRow q))
    (F : Finset (BooleanGroupRightFlow q)) (hF : F.Nonempty) :
    groupFlowFiniteAverage q F ∈
      closedConvexHull ℝ (Set.range (fun g ↦ groupRightTranslate g (booleanGroupIndicator q))) := by
  have hsub := closedConvexHull_min
    (boundedBooleanGroupRightRowClosure_subset_closedConvexHull_orbit q hDLP)
    (convex_closedConvexHull (𝕜 := ℝ)
      (s := Set.range (fun g ↦ groupRightTranslate g (booleanGroupIndicator q))))
    (isClosed_closedConvexHull (𝕜 := ℝ)
      (s := Set.range (fun g ↦ groupRightTranslate g (booleanGroupIndicator q))))
  exact hsub (groupFlowFiniteAverage_mem_closedConvexHull q F hF)

end IndependentZeroBlocks
