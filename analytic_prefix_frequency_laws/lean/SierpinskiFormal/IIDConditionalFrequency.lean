import SierpinskiFormal.IIDConditionalWord
import SierpinskiFormal.CesaroPrefixShift
import SierpinskiFormal.StationaryBooleanFrequency

/-! # Conditional expectations of actual prefix-frequency limits -/

noncomputable section
open Filter MeasureTheory Set Topology
open scoped BigOperators
namespace IndependentZeroBlocks

variable {A : Type*} [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype A] [DecidableEq A] [Nonempty A]
  [TopologicalSpace A] [DiscreteTopology A]

def shiftedPrefixFrequency (q : List A → Bool) (n N : ℕ) (ω : ℕ → A) : ℝ :=
  realCesaroMean (fun j ↦ boolIndicator
    (q (stationaryPrefix digitHead digitShift (n + 1 + j) ω))) N

theorem integrable_shiftedPrefixFrequency (P : FiniteProbabilityWeights A)
    (q : List A → Bool) (n N : ℕ) :
    Integrable (shiftedPrefixFrequency q n N) P.iidMeasure := by
  unfold shiftedPrefixFrequency realCesaroMean
  apply Integrable.div_const
  apply integrable_finsetSum
  intro j _
  exact P.integrable_stationaryPrefix (n + 1 + j) (fun w ↦ boolIndicator (q w))

theorem shiftedPrefixFrequency_norm_le_one (q : List A → Bool)
    (n N : ℕ) (ω : ℕ → A) : ‖shiftedPrefixFrequency q n N ω‖ ≤ 1 := by
  apply norm_realCesaroMean_le_one
  intro j
  cases q (stationaryPrefix digitHead digitShift (n + 1 + j) ω) <;> norm_num [boolIndicator]

theorem condExp_shiftedPrefixFrequency (P : FiniteProbabilityWeights A)
    (q : List A → Bool) (n N : ℕ) :
    P.iidMeasure[shiftedPrefixFrequency q n N | prefixFiltration n] =ᵐ[P.iidMeasure]
      fun ω ↦ realCesaroMean (fun j ↦ weightedWordExtensionAverage P.weight
        (booleanWordIndicator q) j (stationaryPrefix digitHead digitShift (n + 1) ω)) N := by
  let f : ℕ → (ℕ → A) → ℝ := fun j ω ↦ boolIndicator
    (q (stationaryPrefix digitHead digitShift (n + 1 + j) ω))
  have hfi (j : ℕ) : Integrable (f j) P.iidMeasure :=
    P.integrable_stationaryPrefix (n + 1 + j) (fun w ↦ boolIndicator (q w))
  have hfun : shiftedPrefixFrequency q n N =
      (N : ℝ)⁻¹ • (∑ j ∈ Finset.range N, f j) := by
    funext ω
    simp [shiftedPrefixFrequency, realCesaroMean, f, div_eq_mul_inv, mul_comm]
  rw [hfun]
  have hscalar := condExp_smul (μ := P.iidMeasure) (N : ℝ)⁻¹
    (∑ j ∈ Finset.range N, f j) (prefixFiltration n)
  have hsum := condExp_finsetSum (fun j (_ : j ∈ Finset.range N) ↦ hfi j)
    (prefixFiltration n)
  have hall : ∀ᵐ ω ∂P.iidMeasure, ∀ j,
      (P.iidMeasure[f j | prefixFiltration n]) ω =
        weightedWordExtensionAverage P.weight (booleanWordIndicator q) j
          (stationaryPrefix digitHead digitShift (n + 1) ω) :=
    ae_all_iff.mpr fun j ↦ condExp_iid_prefix_observation P n j q
  filter_upwards [hscalar, hsum, hall] with ω hs hsumω hω
  simp only [Pi.smul_apply, smul_eq_mul] at hs
  rw [hs, hsumω]
  simp only [Finset.sum_apply, hω, realCesaroMean, div_eq_mul_inv, mul_comm]

theorem measurable_prefix_real_observation (n : ℕ) (H : List A → ℝ) :
    Measurable[prefixFiltration n] (fun ω : ℕ → A ↦
      H (stationaryPrefix digitHead digitShift (n + 1) ω)) := by
  letI : MeasurableSpace (ℕ → A) := prefixFiltration n
  simp only [FiniteProbabilityWeights.stationaryPrefix_digit_eq_ofFn]
  apply (measurable_of_countable (fun w : Fin (n + 1) → A ↦ H (List.ofFn w))).comp
  apply measurable_pi_lambda
  intro i
  exact measurable_prefix_coordinate (Nat.le_of_lt_succ i.isLt)

/-- Annealed continuation means identify the conditional expectation of the
already existing actual pathwise limit at every finite observed prefix. -/
theorem condExp_iid_frequency_limit (P : FiniteProbabilityWeights A)
    (q : List A → Bool) (L : (ℕ → A) → ℝ) (H : List A → ℝ)
    (hL : ∀ᵐ ω ∂P.iidMeasure, Tendsto
      (fun N ↦ stationaryBooleanFrequency digitHead digitShift q N ω) atTop (𝓝 (L ω)))
    (hH : ∀ w, Tendsto (realCesaroMean (fun j ↦
      weightedWordExtensionAverage P.weight (booleanWordIndicator q) j w))
      atTop (𝓝 (H w))) (n : ℕ) :
    P.iidMeasure[L | prefixFiltration n] =ᵐ[P.iidMeasure]
      fun ω ↦ H (stationaryPrefix digitHead digitShift (n + 1) ω) := by
  apply conditional_limit_identification (prefixFiltration.le n)
    (shiftedPrefixFrequency q n) L
    (fun ω ↦ H (stationaryPrefix digitHead digitShift (n + 1) ω)) 1
  · exact fun N ↦ integrable_shiftedPrefixFrequency P q n N
  · exact fun N ↦ Filter.Eventually.of_forall (shiftedPrefixFrequency_norm_le_one q n N)
  · filter_upwards [hL] with ω hω
    exact tendsto_realCesaroMean_prefixShift
      (fun j ↦ boolIndicator (q (stationaryPrefix digitHead digitShift j ω)))
      (L ω) hω (n + 1)
  · exact (measurable_prefix_real_observation n H).stronglyMeasurable
  · exact P.integrable_stationaryPrefix (n + 1) H
  · have hall : ∀ᵐ ω ∂P.iidMeasure, ∀ N,
        (P.iidMeasure[shiftedPrefixFrequency q n N | prefixFiltration n]) ω =
          realCesaroMean (fun j ↦ weightedWordExtensionAverage P.weight
            (booleanWordIndicator q) j (stationaryPrefix digitHead digitShift (n + 1) ω)) N :=
      ae_all_iff.mpr fun N ↦ condExp_shiftedPrefixFrequency P q n N
    filter_upwards [hall] with ω hω
    exact (hH _).congr (fun N ↦ (hω N).symm)

end IndependentZeroBlocks
