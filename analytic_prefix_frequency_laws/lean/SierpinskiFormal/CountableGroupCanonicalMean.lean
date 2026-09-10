import SierpinskiFormal.CountableGroupMoments

/-!
# A law-independent rational mean for a fixed countable group action

A single strictly positive generating reference law constructs one invariant
finite-orbit barycenter.  The resulting rational number depends only on the
Boolean flow: it is the common value of every invariant probability measure.
Consequently every other strictly positive limiting law on the same step map,
and every total-variation perturbation of it, has the same shifted tuple-Abel
limit.
-/

noncomputable section

open Filter Set Topology MeasureTheory
open scoped BigOperators Topology

namespace IndependentZeroBlocks

variable {G D : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable [Countable G]

/-- A strictly positive generating reference law constructs a rational value
shared by every invariant probability measure on the Boolean flow.  In
particular, the value does not depend on which random-walk law is later used
to approximate invariance. -/
theorem exists_canonical_rational_invariant_barycenter
    (q : G → Bool)
    (hDLP : HasBooleanDoubleLimitProperty (booleanGroupRightRow q))
    (step : D → G) (referenceWeight : D → ℝ)
    (href_pos : ∀ d, 0 < referenceWeight d)
    (href_sum : HasSum referenceWeight 1)
    (hgenerate : Subgroup.closure (Set.range step) = ⊤)
    [MeasurableSpace (BooleanGroupRightFlow (inverseGroupPredicate q))]
    [BorelSpace (BooleanGroupRightFlow (inverseGroupPredicate q))]
    [MeasurableSpace (BooleanGroupRightFlow q)]
    [BorelSpace (BooleanGroupRightFlow q)] :
    ∃ r : ℚ, ∀ (μ : Measure (BooleanGroupRightFlow q))
      [IsProbabilityMeasure μ],
      (∀ g : G, Measure.map (fun x : BooleanGroupRightFlow q ↦ g • x) μ = μ) →
      ∀ z : G, (∫ x, booleanGroupFlowEmbedding q x ∂μ) z = (r : ℝ) := by
  classical
  let qi := inverseGroupPredicate q
  have hqi : HasBooleanDoubleLimitProperty (booleanGroupRightRow qi) :=
    inverseGroupPredicate_hasBooleanDoubleLimitProperty q hDLP
  letI : Countable (BooleanGroupRightFlow qi) :=
    booleanGroupRightFlow_countable qi hqi
  let Pref := countableGroupActionAverage
    (X := BooleanGroupRightFlow qi) step referenceWeight
  have hPref : IsMarkovOperator (BooleanGroupRightFlow qi) Pref :=
    countableGroupActionAverage_isMarkov (X := BooleanGroupRightFlow qi)
      step referenceWeight (fun d ↦ (href_pos d).le) href_sum
  obtain ⟨Lref, hLref⟩ :=
    exists_stationary_state (BooleanGroupRightFlow qi) Pref hPref
  have hLrefCountable : IsCountableStationaryState step referenceWeight Lref :=
    isCountableStationaryState_of_fixed_countableGroupActionAverage
      (X := BooleanGroupRightFlow qi) step referenceWeight
      (fun d ↦ (href_pos d).le) href_sum Lref hLref
  have hνref : IsCountableStationaryMeasure step referenceWeight
      (stateRieszMeasure (BooleanGroupRightFlow qi) Lref) :=
    stateRieszMeasure_isCountableStationaryMeasure step referenceWeight
      (fun d ↦ (href_pos d).le) href_sum Lref hLrefCountable
  exact exists_common_rational_invariant_barycenter_of_countable_stationary
    q hDLP step referenceWeight href_pos href_sum hgenerate
      (stateRieszMeasure (BooleanGroupRightFlow qi) Lref) hνref

/-- A reference positive generating law fixes one rational Abel mean which
works simultaneously for every other positive limiting law on the same step
map. -/
theorem exists_canonical_rational_tendsto_all_countableGroupTupleAbel_succ
    (q : G → Bool)
    (hDLP : HasBooleanDoubleLimitProperty (booleanGroupRightRow q))
    (step : D → G)
    (referenceWeight : D → ℝ)
    (href_pos : ∀ d, 0 < referenceWeight d)
    (href_sum : HasSum referenceWeight 1)
    (hgenerate : Subgroup.closure (Set.range step) = ⊤) :
    ∃ r : ℚ,
      ∀ (weight : ℕ → D → ℝ) (weightLim : D → ℝ),
      (∀ n d, 0 ≤ weight n d) →
      (∀ n, HasSum (weight n) 1) →
      (∀ d, 0 < weightLim d) →
      HasSum weightLim 1 →
      (∀ n, Summable fun d ↦ |weight n d - weightLim d|) →
      Tendsto (fun n ↦ ∑' d, |weight n d - weightLim d|) atTop (𝓝 0) →
      ∀ (c : ℕ → ℝ), (∀ n, 0 ≤ c n) → (∀ n, c n < 1) →
      Tendsto c atTop (𝓝 1) → ∀ z : G,
      Tendsto (fun n ↦ (1 - c n) * ∑' k : ℕ, c n ^ k *
        countableGroupTupleMoment q step (weight n) z 1 (k + 1))
        atTop (𝓝 (r : ℝ)) := by
  classical
  let qi := inverseGroupPredicate q
  have hqi : HasBooleanDoubleLimitProperty (booleanGroupRightRow qi) :=
    inverseGroupPredicate_hasBooleanDoubleLimitProperty q hDLP
  letI : Countable (BooleanGroupRightFlow qi) :=
    booleanGroupRightFlow_countable qi hqi
  borelize (BooleanGroupRightFlow qi)
  let Pref := countableGroupActionAverage
    (X := BooleanGroupRightFlow qi) step referenceWeight
  have hPref : IsMarkovOperator (BooleanGroupRightFlow qi) Pref :=
    countableGroupActionAverage_isMarkov (X := BooleanGroupRightFlow qi)
      step referenceWeight (fun d ↦ (href_pos d).le) href_sum
  obtain ⟨Lref, hLref⟩ :=
    exists_stationary_state (BooleanGroupRightFlow qi) Pref hPref
  have hLrefCountable : IsCountableStationaryState step referenceWeight Lref :=
    isCountableStationaryState_of_fixed_countableGroupActionAverage
      (X := BooleanGroupRightFlow qi) step referenceWeight
      (fun d ↦ (href_pos d).le) href_sum Lref hLref
  have hνref : IsCountableStationaryMeasure step referenceWeight
      (stateRieszMeasure (BooleanGroupRightFlow qi) Lref) :=
    stateRieszMeasure_isCountableStationaryMeasure step referenceWeight
      (fun d ↦ (href_pos d).le) href_sum Lref hLrefCountable
  letI : Countable (BooleanGroupRightFlow q) :=
    booleanGroupRightFlow_countable q hDLP
  borelize (BooleanGroupRightFlow q)
  obtain ⟨r, hr⟩ :=
    exists_common_rational_invariant_barycenter_of_countable_stationary
      q hDLP step referenceWeight href_pos href_sum hgenerate
      (stateRieszMeasure (BooleanGroupRightFlow qi) Lref) hνref
  refine ⟨r, ?_⟩
  intro weight weightLim hweight hweight_sum hweightLim hweightLim_sum
    hdiff hl1 c hc hclt hc_one z
  let P := countableGroupActionAverage
    (X := BooleanGroupRightFlow q) step weightLim
  let Pseq : ℕ → C(BooleanGroupRightFlow q, ℝ) →L[ℝ]
      C(BooleanGroupRightFlow q, ℝ) := fun n ↦
    countableGroupActionAverage (X := BooleanGroupRightFlow q) step (weight n)
  have hP : IsMarkovOperator (BooleanGroupRightFlow q) P :=
    countableGroupActionAverage_isMarkov (X := BooleanGroupRightFlow q)
      step weightLim (fun d ↦ (hweightLim d).le) hweightLim_sum
  have hPseq : ∀ n, IsMarkovOperator (BooleanGroupRightFlow q) (Pseq n) :=
    fun n ↦ countableGroupActionAverage_isMarkov
      (X := BooleanGroupRightFlow q) step (weight n)
      (hweight n) (hweight_sum n)
  have hop : Tendsto (fun n ↦ ‖Pseq n - P‖) atTop (𝓝 0) :=
    tendsto_countableGroupActionAverage_of_tendsto_l1
      (X := BooleanGroupRightFlow q) step weight weightLim
      hweight hweight_sum (fun d ↦ (hweightLim d).le) hweightLim_sum hdiff hl1
  let L0 : PositiveNormalizedState (BooleanGroupRightFlow q) :=
    evaluationState (BooleanGroupRightFlow q) (booleanGroupFlowPoint q 1)
  have hvalue : ∀ L : PositiveNormalizedState (BooleanGroupRightFlow q),
      pullbackState (BooleanGroupRightFlow q) P hP L = L →
        L.1 (booleanGroupFlowCoordinate q z) = (r : ℝ) := by
    intro L hfixed
    have hLCountable : IsCountableStationaryState step weightLim L :=
      isCountableStationaryState_of_fixed_countableGroupActionAverage
        (X := BooleanGroupRightFlow q) step weightLim
        (fun d ↦ (hweightLim d).le) hweightLim_sum L hfixed
    have hμ : IsCountableStationaryMeasure step weightLim
        (stateRieszMeasure (BooleanGroupRightFlow q) L) :=
      stateRieszMeasure_isCountableStationaryMeasure step weightLim
        (fun d ↦ (hweightLim d).le) hweightLim_sum L hLCountable
    have hinvariant : ∀ g : G,
        Measure.map (fun x : BooleanGroupRightFlow q ↦ g • x)
          (stateRieszMeasure (BooleanGroupRightFlow q) L) =
            stateRieszMeasure (BooleanGroupRightFlow q) L :=
      countable_groupActionMeasure_invariant_of_pointwise_stationary
        step weightLim hweightLim hweightLim_sum hgenerate
        (stateRieszMeasure (BooleanGroupRightFlow q) L) hμ
    have hrz := hr (stateRieszMeasure (BooleanGroupRightFlow q) L) hinvariant z
    have hj := integrable_booleanGroupFlowEmbedding q hDLP
      (stateRieszMeasure (BooleanGroupRightFlow q) L)
    calc
      L.1 (booleanGroupFlowCoordinate q z) =
          ∫ x, booleanGroupFlowCoordinate q z x
            ∂stateRieszMeasure (BooleanGroupRightFlow q) L :=
        (integral_stateRieszMeasure (BooleanGroupRightFlow q) L
          (booleanGroupFlowCoordinate q z)).symm
      _ = (∫ x, booleanGroupFlowEmbedding q x
            ∂stateRieszMeasure (BooleanGroupRightFlow q) L) z := by
        simpa [booleanGroupFlowCoordinate_apply, booleanGroupFlowEmbedding_apply] using
          (BoundedContinuousFunction.evalCLM ℝ z).integral_comp_comm hj
      _ = (r : ℝ) := hrz
  have hbase : Tendsto (fun n ↦
      (discountedState (BooleanGroupRightFlow q) (Pseq n) (hPseq n) L0
        (c n) (hc n) (hclt n)).1 (booleanGroupFlowCoordinate q z))
      atTop (𝓝 (r : ℝ)) :=
    tendsto_discountedState_apply_of_stationary_value
      (BooleanGroupRightFlow q) P hP Pseq hPseq hop L0 c hc hclt hc_one
      (booleanGroupFlowCoordinate q z) (r : ℝ) hvalue
  exact tendsto_shifted_tupleMoment_of_tendsto_discountedState
    q step weight hweight hweight_sum z 1 c hc hclt hc_one (r : ℝ) hbase

end IndependentZeroBlocks
