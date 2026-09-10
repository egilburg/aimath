import SierpinskiFormal.GroupBooleanInversion
import SierpinskiFormal.GroupFlowProbability
import Mathlib.Analysis.Convex.Integral

/-! # Invariant measures on Boolean group flows have a common rational barycenter -/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped BoundedContinuousFunction

namespace IndependentZeroBlocks

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G] [Countable G]

section Barycenter

variable (q : G → Bool)
variable [MeasurableSpace (BooleanGroupRightFlow q)] [BorelSpace (BooleanGroupRightFlow q)]

theorem integrable_booleanGroupFlowEmbedding
    (hDLP : HasBooleanDoubleLimitProperty (booleanGroupRightRow q))
    (μ : Measure (BooleanGroupRightFlow q)) [IsFiniteMeasure μ] :
    Integrable (booleanGroupFlowEmbedding q) μ := by
  letI : Countable (BooleanGroupRightFlow q) := booleanGroupRightFlow_countable q hDLP
  borelize (BoundedGroupFunction G)
  apply (integrable_const (1 : ℝ)).mono'
  · exact (stronglyMeasurable_of_countable_domain
      (BooleanGroupRightFlow q) (booleanGroupFlowEmbedding q)).aestronglyMeasurable
  · filter_upwards with f
    exact norm_le_one_of_mem_boundedBooleanGroupRightRowClosure q
      ⟨f.val, f.property, rfl⟩

theorem integral_booleanGroupFlowEmbedding_mem_rightHull
    (hDLP : HasBooleanDoubleLimitProperty (booleanGroupRightRow q))
    (μ : Measure (BooleanGroupRightFlow q)) [IsProbabilityMeasure μ] :
    (∫ f, booleanGroupFlowEmbedding q f ∂μ) ∈
      closedConvexHull ℝ
        (Set.range (fun g ↦ groupRightTranslate g (booleanGroupIndicator q))) := by
  apply (convex_closedConvexHull (𝕜 := ℝ)
    (s := Set.range (fun g ↦ groupRightTranslate g (booleanGroupIndicator q)))).integral_mem
    isClosed_closedConvexHull
  · filter_upwards with f
    exact boundedBooleanGroupRightRowClosure_subset_closedConvexHull_orbit q hDLP
      ⟨f.val, f.property, rfl⟩
  · exact integrable_booleanGroupFlowEmbedding q hDLP μ

theorem integral_booleanGroupFlowEmbedding_invariant
    (hDLP : HasBooleanDoubleLimitProperty (booleanGroupRightRow q))
    (μ : Measure (BooleanGroupRightFlow q)) [IsProbabilityMeasure μ]
    (hμ : ∀ g : G, Measure.map (fun f : BooleanGroupRightFlow q ↦ g • f) μ = μ)
    (g : G) :
    groupRightTranslate g (∫ f, booleanGroupFlowEmbedding q f ∂μ) =
      ∫ f, booleanGroupFlowEmbedding q f ∂μ := by
  have hj := integrable_booleanGroupFlowEmbedding q hDLP μ
  have hm : Measurable (fun f : BooleanGroupRightFlow q ↦ g • f) :=
    (continuous_const_smul g).measurable
  have hjae : AEStronglyMeasurable (booleanGroupFlowEmbedding q)
      (Measure.map (fun f : BooleanGroupRightFlow q ↦ g • f) μ) := by
    rw [hμ g]
    exact hj.aestronglyMeasurable
  have hi := integral_map hm.aemeasurable hjae
  rw [hμ g] at hi
  change groupRightTranslateCLM g (∫ f, booleanGroupFlowEmbedding q f ∂μ) = _
  rw [← (groupRightTranslateCLM g).integral_comp_comm hj]
  calc
    (∫ f, groupRightTranslateCLM g (booleanGroupFlowEmbedding q f) ∂μ) =
        ∫ f, booleanGroupFlowEmbedding q (g • f) ∂μ := by
      apply integral_congr_ae
      filter_upwards with f
      exact (booleanGroupFlowEmbedding_smul q g f).symm
    _ = ∫ f, booleanGroupFlowEmbedding q f ∂μ := hi.symm

theorem integral_booleanGroupFlowEmbedding_eq_inverse_finiteAverage
    (hDLP : HasBooleanDoubleLimitProperty (booleanGroupRightRow q))
    (F : Finset (BooleanGroupRightFlow (inverseGroupPredicate q)))
    (hFne : F.Nonempty)
    (hF : ∀ g : G, Set.MapsTo
      (fun f : BooleanGroupRightFlow (inverseGroupPredicate q) ↦ g • f)
      (F : Set _) (F : Set _))
    (μ : Measure (BooleanGroupRightFlow q)) [IsProbabilityMeasure μ]
    (hμ : ∀ g : G, Measure.map (fun f : BooleanGroupRightFlow q ↦ g • f) μ = μ) :
    (∫ f, booleanGroupFlowEmbedding q f ∂μ) =
      groupFlowFiniteAverage (inverseGroupPredicate q) F := by
  exact invariant_rightHull_eq_inverse_finiteAverage q hDLP F hFne hF _
    (integral_booleanGroupFlowEmbedding_mem_rightHull q hDLP μ)
    (integral_booleanGroupFlowEmbedding_invariant q hDLP μ hμ)

end Barycenter

end IndependentZeroBlocks
