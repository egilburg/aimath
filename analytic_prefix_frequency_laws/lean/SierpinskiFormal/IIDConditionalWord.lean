import SierpinskiFormal.IIDConditionalPrefix
import SierpinskiFormal.FiniteConditionalParameter

/-! # Exact finite-prefix conditional expectations for IID words -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace IndependentZeroBlocks

variable {A : Type*} [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype A] [DecidableEq A]

theorem condExp_iid_joint_word (L : FiniteProbabilityWeights A)
    (n N : ℕ) (F : (Fin (n + 1) → A) → (Fin N → A) → ℝ) :
    L.iidMeasure[fun ω ↦ F (fun i ↦ ω i.val) (fun i ↦ ω (n + 1 + i.val)) |
      prefixFiltration n] =ᵐ[L.iidMeasure]
      fun ω ↦ ∑ v : Fin N → A,
        wordWeight L.weight (List.ofFn v) * F (fun i ↦ ω i.val) v := by
  have hX : Measurable[prefixFiltration n]
      (fun ω : ℕ → A ↦ fun i : Fin (n + 1) ↦ ω i.val) := by
    letI : MeasurableSpace (ℕ → A) := prefixFiltration n
    apply measurable_pi_lambda
    intro i
    exact measurable_prefix_coordinate (Nat.le_of_lt_succ i.isLt)
  apply condExp_finite_parameter (prefixFiltration.le n)
    (fun ω : ℕ → A ↦ fun i : Fin (n + 1) ↦ ω i.val) hX
    (fun w ω ↦ F w (fun i ↦ ω (n + 1 + i.val)))
    (fun w ↦ ∑ v : Fin N → A, wordWeight L.weight (List.ofFn v) * F w v)
  · intro w
    exact (iid_tail_observation_law L n N (F w)).1
  · intro w
    have h := condExp_tail_observation L n N (F w)
    rwa [(iid_tail_observation_law L n N (F w)).2] at h

variable [Nonempty A] [TopologicalSpace A] [DiscreteTopology A]

/-- Conditioning an actual longer prefix gives the accepted weighted-word
continuation operator evaluated at the observed prefix. -/
theorem condExp_iid_prefix_observation (L : FiniteProbabilityWeights A)
    (n N : ℕ) (q : List A → Bool) :
    L.iidMeasure[fun ω ↦ boolIndicator
      (q (stationaryPrefix digitHead digitShift (n + 1 + N) ω)) |
      prefixFiltration n] =ᵐ[L.iidMeasure]
      fun ω ↦ weightedWordExtensionAverage L.weight (booleanWordIndicator q) N
        (stationaryPrefix digitHead digitShift (n + 1) ω) := by
  have h := condExp_iid_joint_word L n N
    (fun w v ↦ boolIndicator (q (List.ofFn w ++ List.ofFn v)))
  have hword (ω : ℕ → A) :
      stationaryPrefix digitHead digitShift (n + 1 + N) ω =
        List.ofFn (fun i : Fin (n + 1) ↦ ω i.val) ++
          List.ofFn (fun i : Fin N ↦ ω (n + 1 + i.val)) := by
    rw [FiniteProbabilityWeights.stationaryPrefix_digit_eq_ofFn, List.ofFn_add]
    rfl
  simpa only [hword, FiniteProbabilityWeights.stationaryPrefix_digit_eq_ofFn,
    weightedWordExtensionAverage_eq_tuple_sum, booleanWordIndicator_apply] using h

end IndependentZeroBlocks
