import SierpinskiFormal.CountableGroupFlowStationary
import SierpinskiFormal.GroupInvariantBarycenter

/-!
# Common rational barycenters from countably supported stationarity

This removes the finite-generation restriction from the finite-orbit step.
The remaining input is a pointwise stationary probability for a positive
summable law whose (possibly infinite) range generates the group.
-/

noncomputable section

open Set Filter Topology MeasureTheory

namespace IndependentZeroBlocks

variable {G D : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable [Countable G]

/-- A positive countably supported stationary law on the inverse Boolean
flow supplies the same common rational barycenter as the finite-generator
construction, with no finiteness assumption on the generating family. -/
theorem exists_common_rational_invariant_barycenter_of_countable_stationary
    (q : G → Bool)
    (hDLP : HasBooleanDoubleLimitProperty (booleanGroupRightRow q))
    (step : D → G) (weight : D → ℝ)
    (hweight : ∀ d, 0 < weight d) (hweight_sum : HasSum weight 1)
    (hgenerate : Subgroup.closure (Set.range step) = ⊤)
    [MeasurableSpace (BooleanGroupRightFlow (inverseGroupPredicate q))]
    [BorelSpace (BooleanGroupRightFlow (inverseGroupPredicate q))]
    (ν : Measure (BooleanGroupRightFlow (inverseGroupPredicate q)))
    [IsProbabilityMeasure ν]
    (hν : IsCountableStationaryMeasure step weight ν)
    [MeasurableSpace (BooleanGroupRightFlow q)]
    [BorelSpace (BooleanGroupRightFlow q)] :
    ∃ r : ℚ, ∀ (μ : Measure (BooleanGroupRightFlow q)) [IsProbabilityMeasure μ],
      (∀ g : G, Measure.map (fun f : BooleanGroupRightFlow q ↦ g • f) μ = μ) →
      ∀ z : G, (∫ f, booleanGroupFlowEmbedding q f ∂μ) z = (r : ℝ) := by
  classical
  let qi := inverseGroupPredicate q
  have hqi := inverseGroupPredicate_hasBooleanDoubleLimitProperty q hDLP
  letI : Countable (BooleanGroupRightFlow qi) := booleanGroupRightFlow_countable qi hqi
  obtain ⟨F, hFne, hF, _⟩ :=
    countable_exists_invariant_finite_orbit_finset_of_stationary_probability
      step weight ν hweight hweight_sum hgenerate hν
  obtain ⟨r, hr⟩ := groupFlowFiniteAverage_rational qi F (1 : G)
  refine ⟨r, fun μ _ hμ z ↦ ?_⟩
  rw [integral_booleanGroupFlowEmbedding_eq_inverse_finiteAverage
    q hDLP F hFne hF μ hμ]
  exact (groupFlowFiniteAverage_constant qi F hF z).trans hr

end IndependentZeroBlocks
