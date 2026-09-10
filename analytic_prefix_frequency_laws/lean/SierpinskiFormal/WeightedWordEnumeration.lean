import SierpinskiFormal.WeightedWordCesaro
import SierpinskiFormal.MatrixWordLogDensityBridge
import SierpinskiFormal.RenewalWordDecomposition

/-! # Exact finite-word meaning of weighted averages -/

noncomputable section
open scoped BigOperators
namespace IndependentZeroBlocks

variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
variable [Fintype A] [Nonempty A]

theorem weightedWordExtensionAverage_eq_tuple_sum
    (p : A → ℝ) (q : BoundedWordFunction A) (n : ℕ) (z : List A) :
    weightedWordExtensionAverage p q n z =
      ∑ x : Fin n → A, wordWeight p (List.ofFn x) * q (z ++ List.ofFn x) := by
  induction n generalizing z with
  | zero => simp [weightedWordExtensionAverage, wordWeight]
  | succ n ih =>
      simp only [weightedWordExtensionAverage]
      simp_rw [ih]
      rw [Fintype.sum_equiv (finSuccTupleEquiv n)
        (fun x : Fin (n + 1) → A ↦ wordWeight p (List.ofFn x) * q (z ++ List.ofFn x))
        (fun ax : A × (Fin n → A) ↦
          p ax.1 * wordWeight p (List.ofFn ax.2) * q (z ++ ax.1 :: List.ofFn ax.2))]
      · rw [Fintype.sum_prod_type]
        simp_rw [Finset.mul_sum, List.append_assoc, List.singleton_append, mul_assoc]
      · intro x
        simp [List.ofFn_succ, finSuccTupleEquiv, wordWeight]

/-- The total mass of exact-length words is one under a probability law. -/
theorem sum_tuple_wordWeight_eq_one (p : A → ℝ) (hp1 : ∑ a, p a = 1) (n : ℕ) :
    (∑ x : Fin n → A, wordWeight p (List.ofFn x)) = 1 := by
  simpa [wordWeight, List.prod_ofFn, hp1] using (Fintype.sum_pow p n).symm

end IndependentZeroBlocks
