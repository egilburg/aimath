import SierpinskiFormal.AbelMarkovState
import SierpinskiFormal.CountableGroupRationalMean
import SierpinskiFormal.CountableGroupFlowRiesz
import SierpinskiFormal.GroupFlowStationaryMeasure
import SierpinskiFormal.GroupFlowWordAverages
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Abel means for countably supported group laws

We construct the Markov operator of a summable group law as an operator-norm
sum.  Total-variation convergence of the coefficients then gives
operator-norm convergence, so the variable-operator Abel theorem applies.
-/

noncomputable section

open Filter Set Topology MeasureTheory
open scoped BigOperators Topology

namespace IndependentZeroBlocks

variable {G X D : Type*} [Group G] [MulAction G X]
variable [TopologicalSpace X] [CompactSpace X] [T2Space X] [Nonempty X]
variable [ContinuousConstSMul G X]

/-- Precomposition by a group action does not increase the uniform norm. -/
theorem norm_continuousPrecompCLM_groupAction_le
    (g : G) (f : C(X, ℝ)) :
    ‖continuousPrecompCLM X (groupActionContinuousMap (X := X) g) f‖ ≤ ‖f‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
  intro x
  exact ContinuousMap.norm_coe_le_norm f (g • x)

/-- The operator-norm contribution of one signed coefficient is bounded by
its absolute value. -/
theorem norm_smul_continuousPrecompCLM_groupAction_le
    (a : ℝ) (g : G) :
    ‖a • continuousPrecompCLM X (groupActionContinuousMap (X := X) g)‖ ≤ |a| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg a)
  intro f
  rw [ContinuousLinearMap.smul_apply]
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left
    (norm_continuousPrecompCLM_groupAction_le (X := X) g f) (abs_nonneg a)

/-- Operator terms associated with an absolutely summable signed law. -/
def countableGroupActionAverageTerm (step : D → G) (weight : D → ℝ) (d : D) :
    C(X, ℝ) →L[ℝ] C(X, ℝ) :=
  weight d • continuousPrecompCLM X
    (groupActionContinuousMap (X := X) (step d))

theorem summable_countableGroupActionAverageTerm
    (step : D → G) (weight : D → ℝ)
    (hweight : Summable fun d ↦ |weight d|) :
    Summable (countableGroupActionAverageTerm (X := X) step weight) := by
  apply Summable.of_norm_bounded
    (f := countableGroupActionAverageTerm (X := X) step weight)
    hweight
  intro d
  exact norm_smul_continuousPrecompCLM_groupAction_le
    (X := X) (weight d) (step d)

/-- The operator-norm sum of the action operators of a countably supported
signed law. -/
def countableGroupActionAverage (step : D → G) (weight : D → ℝ) :
    C(X, ℝ) →L[ℝ] C(X, ℝ) :=
  ∑' d, countableGroupActionAverageTerm (X := X) step weight d

theorem hasSum_countableGroupActionAverage
    (step : D → G) (weight : D → ℝ)
    (hweight : Summable fun d ↦ |weight d|) :
    HasSum (countableGroupActionAverageTerm (X := X) step weight)
      (countableGroupActionAverage (X := X) step weight) :=
  (summable_countableGroupActionAverageTerm (X := X) step weight hweight).hasSum

theorem hasSum_countableGroupActionAverage_apply
    (step : D → G) (weight : D → ℝ)
    (hweight : Summable fun d ↦ |weight d|)
    (f : C(X, ℝ)) (x : X) :
    HasSum (fun d ↦ weight d * f (step d • x))
      (countableGroupActionAverage (X := X) step weight f x) := by
  have hs := hasSum_countableGroupActionAverage (X := X) step weight hweight
  have hsf := hs.map (ContinuousLinearMap.apply ℝ C(X, ℝ) f)
    (ContinuousLinearMap.apply ℝ C(X, ℝ) f).continuous
  have hsx := hsf.map (ContinuousMap.evalCLM ℝ x)
    (ContinuousMap.evalCLM ℝ x).continuous
  simpa [Function.comp_def, countableGroupActionAverageTerm, continuousPrecompCLM_apply,
    groupActionContinuousMap] using hsx

@[simp] theorem countableGroupActionAverage_apply
    (step : D → G) (weight : D → ℝ)
    (hweight : Summable fun d ↦ |weight d|)
    (f : C(X, ℝ)) (x : X) :
    countableGroupActionAverage (X := X) step weight f x =
      ∑' d, weight d * f (step d • x) :=
  (hasSum_countableGroupActionAverage_apply (X := X) step weight hweight f x).tsum_eq.symm

/-- A nonnegative countably supported probability law defines a Markov
operator. -/
theorem countableGroupActionAverage_isMarkov
    (step : D → G) (weight : D → ℝ)
    (hweight : ∀ d, 0 ≤ weight d) (hweight_sum : HasSum weight 1) :
    IsMarkovOperator X (countableGroupActionAverage (X := X) step weight) := by
  have habs : Summable fun d ↦ |weight d| := by
    simpa only [abs_of_nonneg (hweight _)] using hweight_sum.summable
  constructor
  · intro f hf x
    change 0 ≤ countableGroupActionAverage (X := X) step weight f x
    rw [countableGroupActionAverage_apply (X := X) step weight habs f x]
    exact tsum_nonneg fun d ↦ mul_nonneg (hweight d) (hf (step d • x))
  · ext x
    rw [countableGroupActionAverage_apply (X := X) step weight habs 1 x]
    simpa using hweight_sum.tsum_eq

/-- A fixed state of the countable action average satisfies the scalar
stationarity identity used by the countable Riesz bridge. -/
theorem isCountableStationaryState_of_fixed_countableGroupActionAverage
    (step : D → G) (weight : D → ℝ)
    (hweight : ∀ d, 0 ≤ weight d) (hweight_sum : HasSum weight 1)
    (L : PositiveNormalizedState X)
    (hfixed : pullbackState X (countableGroupActionAverage (X := X) step weight)
      (countableGroupActionAverage_isMarkov (X := X) step weight hweight hweight_sum) L = L) :
    IsCountableStationaryState step weight L := by
  have habs : Summable fun d ↦ |weight d| := by
    simpa only [abs_of_nonneg (hweight _)] using hweight_sum.summable
  intro f
  have hfixeval := congrArg (fun M : PositiveNormalizedState X ↦ M.1 f) hfixed
  change L.1 (countableGroupActionAverage (X := X) step weight f) = L.1 f at hfixeval
  have hs := hasSum_countableGroupActionAverage (X := X) step weight habs
  have hsf := hs.map (ContinuousLinearMap.apply ℝ C(X, ℝ) f)
    (ContinuousLinearMap.apply ℝ C(X, ℝ) f).continuous
  have hsL := hsf.map (WeakDual.toStrongDual L.1)
    (WeakDual.toStrongDual L.1).continuous
  have hsL' : HasSum (fun d ↦ weight d *
      L.1 (f.comp (groupActionContinuousMap (X := X) (step d))))
      (L.1 (countableGroupActionAverage (X := X) step weight f)) := by
    convert! hsL using 1
    · funext d
      change weight d * L.1 (f.comp (groupActionContinuousMap (X := X) (step d))) =
        L.1 (weight d • continuousPrecompCLM X
          (groupActionContinuousMap (X := X) (step d)) f)
      rw [map_smul]
      rfl
  calc
    L.1 f = L.1 (countableGroupActionAverage (X := X) step weight f) := hfixeval.symm
    _ = ∑' d, weight d *
        L.1 (f.comp (groupActionContinuousMap (X := X) (step d))) := hsL'.tsum_eq.symm

/-- The operator norm of a signed action average is bounded by the `ℓ¹`
norm of its coefficients. -/
theorem norm_countableGroupActionAverage_le
    (step : D → G) (weight : D → ℝ)
    (hweight : Summable fun d ↦ |weight d|) :
    ‖countableGroupActionAverage (X := X) step weight‖ ≤
      ∑' d, |weight d| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (tsum_nonneg fun d ↦ abs_nonneg _)
  intro f
  apply (ContinuousMap.norm_le _
    (mul_nonneg (tsum_nonneg fun d ↦ abs_nonneg _) (norm_nonneg f))).mpr
  intro x
  rw [Real.norm_eq_abs,
    countableGroupActionAverage_apply (X := X) step weight hweight f x]
  have hpoint : ∀ d,
      ‖weight d * f (step d • x)‖ ≤ |weight d| * ‖f‖ := by
    intro d
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left
      (ContinuousMap.norm_coe_le_norm f (step d • x)) (abs_nonneg (weight d))
  have hmajor : Summable fun d ↦ |weight d| * ‖f‖ := hweight.mul_right ‖f‖
  have hnorm : Summable fun d ↦ ‖weight d * f (step d • x)‖ :=
    Summable.of_nonneg_of_le (f := fun d ↦ |weight d| * ‖f‖)
      (g := fun d ↦ ‖weight d * f (step d • x)‖)
      (fun d ↦ norm_nonneg _) hpoint hmajor
  calc
    |∑' d, weight d * f (step d • x)| =
        ‖∑' d, weight d * f (step d • x)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' d, ‖weight d * f (step d • x)‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' d, |weight d| * ‖f‖ := hnorm.tsum_le_tsum hpoint hmajor
    _ = (∑' d, |weight d|) * ‖f‖ := hweight.tsum_mul_right ‖f‖

/-- Difference of two countable action averages as the sum of the signed
coefficient differences. -/
theorem countableGroupActionAverage_sub
    (step : D → G) (weight₁ weight₂ : D → ℝ)
    (hweight₁ : Summable fun d ↦ |weight₁ d|)
    (hweight₂ : Summable fun d ↦ |weight₂ d|) :
    countableGroupActionAverage (X := X) step weight₁ -
        countableGroupActionAverage (X := X) step weight₂ =
      ∑' d, countableGroupActionAverageTerm (X := X) step
        (fun e ↦ weight₁ e - weight₂ e) d := by
  rw [countableGroupActionAverage, countableGroupActionAverage,
    ← (summable_countableGroupActionAverageTerm (X := X) step weight₁ hweight₁).tsum_sub
      (summable_countableGroupActionAverageTerm (X := X) step weight₂ hweight₂)]
  apply tsum_congr
  intro d
  exact (sub_smul (weight₁ d) (weight₂ d)
    (continuousPrecompCLM X
      (groupActionContinuousMap (X := X) (step d)))).symm

/-- Total variation of the coefficients dominates operator-norm distance. -/
theorem norm_countableGroupActionAverage_sub_le
    (step : D → G) (weight₁ weight₂ : D → ℝ)
    (hweight₁ : Summable fun d ↦ |weight₁ d|)
    (hweight₂ : Summable fun d ↦ |weight₂ d|)
    (hdiff : Summable fun d ↦ |weight₁ d - weight₂ d|) :
    ‖countableGroupActionAverage (X := X) step weight₁ -
      countableGroupActionAverage (X := X) step weight₂‖ ≤
        ∑' d, |weight₁ d - weight₂ d| := by
  rw [countableGroupActionAverage_sub (X := X) step weight₁ weight₂
    hweight₁ hweight₂]
  exact norm_countableGroupActionAverage_le (X := X) step
    (fun d ↦ weight₁ d - weight₂ d) hdiff

/-- Total-variation convergence of probability laws implies operator-norm
convergence of their action averages. -/
theorem tendsto_countableGroupActionAverage_of_tendsto_l1
    (step : D → G) (weight : ℕ → D → ℝ) (weightLim : D → ℝ)
    (hweight : ∀ n d, 0 ≤ weight n d)
    (hweight_sum : ∀ n, HasSum (weight n) 1)
    (hweightLim : ∀ d, 0 ≤ weightLim d)
    (hweightLim_sum : HasSum weightLim 1)
    (hdiff : ∀ n, Summable fun d ↦ |weight n d - weightLim d|)
    (hl1 : Tendsto (fun n ↦ ∑' d, |weight n d - weightLim d|) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ‖countableGroupActionAverage (X := X) step (weight n) -
      countableGroupActionAverage (X := X) step weightLim‖) atTop (𝓝 0) := by
  have habs : ∀ n, Summable fun d ↦ |weight n d| := fun n ↦ by
    simpa only [abs_of_nonneg (hweight n _)] using (hweight_sum n).summable
  have habsLim : Summable fun d ↦ |weightLim d| := by
    simpa only [abs_of_nonneg (hweightLim _)] using hweightLim_sum.summable
  have hbound : ∀ n,
      ‖countableGroupActionAverage (X := X) step (weight n) -
        countableGroupActionAverage (X := X) step weightLim‖ ≤
      ∑' d, |weight n d - weightLim d| := fun n ↦
    norm_countableGroupActionAverage_sub_le
      (X := X) step (weight n) weightLim (habs n) habsLim (hdiff n)
  apply squeeze_zero'
    (f := fun n ↦ ‖countableGroupActionAverage (X := X) step (weight n) -
      countableGroupActionAverage (X := X) step weightLim‖)
    (g := fun n ↦ ∑' d, |weight n d - weightLim d|)
    (Eventually.of_forall fun n ↦ norm_nonneg
      (countableGroupActionAverage (X := X) step (weight n) -
        countableGroupActionAverage (X := X) step weightLim))
    (Eventually.of_forall hbound)
    hl1

section BooleanFlow

variable {G D : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable [Countable G]

/-- For a stable Boolean function on a countable group, variable countable
probability laws converging in total variation to a strictly positive
generating law have a rational Abel limit at every flow coordinate.

The initial Abel state is evaluation at the original right row.  The proof
constructs a stationary state and stationary Riesz measure on the inverse
flow, obtains the rational finite-orbit barycenter, and then applies the
variable-Markov Abel theorem on the original flow. -/
theorem exists_rational_tendsto_countableGroupAbel
    (q : G → Bool)
    (hDLP : HasBooleanDoubleLimitProperty (booleanGroupRightRow q))
    (step : D → G)
    (weight : ℕ → D → ℝ) (weightLim : D → ℝ)
    (hweight : ∀ n d, 0 ≤ weight n d)
    (hweight_sum : ∀ n, HasSum (weight n) 1)
    (hweightLim : ∀ d, 0 < weightLim d)
    (hweightLim_sum : HasSum weightLim 1)
    (hgenerate : Subgroup.closure (Set.range step) = ⊤)
    (hdiff : ∀ n, Summable fun d ↦ |weight n d - weightLim d|)
    (hl1 : Tendsto (fun n ↦ ∑' d, |weight n d - weightLim d|) atTop (𝓝 0))
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hclt : ∀ n, c n < 1)
    (hc_one : Tendsto c atTop (𝓝 1)) (z : G) :
    ∃ r : ℚ, Tendsto (fun n ↦
      (discountedState (BooleanGroupRightFlow q)
        (countableGroupActionAverage (X := BooleanGroupRightFlow q) step (weight n))
        (countableGroupActionAverage_isMarkov (X := BooleanGroupRightFlow q)
          step (weight n) (hweight n) (hweight_sum n))
        (evaluationState (BooleanGroupRightFlow q) (booleanGroupFlowPoint q 1))
        (c n) (hc n) (hclt n)).1 (booleanGroupFlowCoordinate q z))
      atTop (𝓝 (r : ℝ)) := by
  classical
  let qi := inverseGroupPredicate q
  have hqi : HasBooleanDoubleLimitProperty (booleanGroupRightRow qi) :=
    inverseGroupPredicate_hasBooleanDoubleLimitProperty q hDLP
  letI : Countable (BooleanGroupRightFlow qi) :=
    booleanGroupRightFlow_countable qi hqi
  borelize (BooleanGroupRightFlow qi)
  let Pinv := countableGroupActionAverage
    (X := BooleanGroupRightFlow qi) step weightLim
  have hPinv : IsMarkovOperator (BooleanGroupRightFlow qi) Pinv :=
    countableGroupActionAverage_isMarkov (X := BooleanGroupRightFlow qi)
      step weightLim (fun d ↦ (hweightLim d).le) hweightLim_sum
  obtain ⟨Linv, hLinv⟩ :=
    exists_stationary_state (BooleanGroupRightFlow qi) Pinv hPinv
  have hLinvCountable : IsCountableStationaryState step weightLim Linv :=
    isCountableStationaryState_of_fixed_countableGroupActionAverage
      (X := BooleanGroupRightFlow qi) step weightLim
      (fun d ↦ (hweightLim d).le) hweightLim_sum Linv hLinv
  have hν : IsCountableStationaryMeasure step weightLim
      (stateRieszMeasure (BooleanGroupRightFlow qi) Linv) :=
    stateRieszMeasure_isCountableStationaryMeasure step weightLim
      (fun d ↦ (hweightLim d).le) hweightLim_sum Linv hLinvCountable
  letI : Countable (BooleanGroupRightFlow q) :=
    booleanGroupRightFlow_countable q hDLP
  borelize (BooleanGroupRightFlow q)
  obtain ⟨r, hr⟩ :=
    exists_common_rational_invariant_barycenter_of_countable_stationary
      q hDLP step weightLim hweightLim hweightLim_sum hgenerate
      (stateRieszMeasure (BooleanGroupRightFlow qi) Linv) hν
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
      (X := BooleanGroupRightFlow q) step (weight n) (hweight n) (hweight_sum n)
  have hop : Tendsto (fun n ↦ ‖Pseq n - P‖) atTop (𝓝 0) :=
    tendsto_countableGroupActionAverage_of_tendsto_l1
      (X := BooleanGroupRightFlow q) step weight weightLim hweight hweight_sum
      (fun d ↦ (hweightLim d).le) hweightLim_sum hdiff hl1
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
  refine ⟨r, ?_⟩
  exact tendsto_discountedState_apply_of_stationary_value
    (BooleanGroupRightFlow q) P hP Pseq hPseq hop L0 c hc hclt hc_one
    (booleanGroupFlowCoordinate q z) (r : ℝ) hvalue

end BooleanFlow

end IndependentZeroBlocks
