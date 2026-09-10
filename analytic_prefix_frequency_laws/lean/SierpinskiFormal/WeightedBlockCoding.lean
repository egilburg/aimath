import SierpinskiFormal.WeightedWordEnumeration
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Exact IID block coding

Finite words of length `N * ell` are regrouped into `N` consecutive blocks
of length `ell`.  Product weights and exact-length weighted sums are preserved.
-/

noncomputable section
open scoped BigOperators

namespace IndependentZeroBlocks

variable {A : Type*}

/-- Flatten a word over the block alphabet `Fin ell → A`. -/
def flattenBlocks (ell : ℕ) (w : List (Fin ell → A)) : List A :=
  (w.map List.ofFn).flatten

@[simp] theorem flattenBlocks_nil (ell : ℕ) :
    flattenBlocks (A := A) ell [] = [] := by
  simp [flattenBlocks]

@[simp] theorem flattenBlocks_cons (ell : ℕ) (a : Fin ell → A)
    (w : List (Fin ell → A)) :
    flattenBlocks ell (a :: w) = List.ofFn a ++ flattenBlocks ell w := by
  simp [flattenBlocks]

@[simp] theorem flattenBlocks_append (ell : ℕ)
    (u v : List (Fin ell → A)) :
    flattenBlocks ell (u ++ v) = flattenBlocks ell u ++ flattenBlocks ell v := by
  simp [flattenBlocks]

@[simp] theorem length_flattenBlocks (ell : ℕ) (w : List (Fin ell → A)) :
    (flattenBlocks ell w).length = w.length * ell := by
  induction w with
  | nil => simp
  | cons a w ih =>
      simp only [flattenBlocks_cons, List.length_append, List.length_ofFn, ih,
        List.length_cons]
      rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]

section

variable [Fintype A]

/-- The product law induced on blocks by the letter law `p`. -/
def blockWeight (p : A → ℝ) (ell : ℕ) (a : Fin ell → A) : ℝ :=
  wordWeight p (List.ofFn a)

theorem sum_blockWeight_eq_one (p : A → ℝ) (hp1 : ∑ a, p a = 1) (ell : ℕ) :
    ∑ a : Fin ell → A, blockWeight p ell a = 1 := by
  simpa [blockWeight, wordWeight, List.prod_ofFn, hp1] using
    (Fintype.sum_pow p ell).symm

omit [Fintype A] in theorem blockWeight_nonneg (p : A → ℝ) (hp : ∀ a, 0 ≤ p a)
    (ell : ℕ) (a : Fin ell → A) :
    0 ≤ blockWeight p ell a := by
  simp only [blockWeight, wordWeight]
  induction List.ofFn a with
  | nil => simp
  | cons b w ih =>
      simp only [List.map_cons, List.prod_cons]
      exact mul_nonneg (hp b) ih

omit [Fintype A] in @[simp] theorem wordWeight_flattenBlocks (p : A → ℝ) (ell : ℕ)
    (w : List (Fin ell → A)) :
    wordWeight p (flattenBlocks ell w) = wordWeight (blockWeight p ell) w := by
  classical
  induction w with
  | nil => simp [flattenBlocks, wordWeight]
  | cons a w ih =>
      rw [flattenBlocks_cons, wordWeight_append, ih]
      rfl

/-- Regroup a tuple of `N * ell` letters into `N` consecutive `ell`-blocks. -/
def blockTupleEquiv (N ell : ℕ) :
    (Fin (N * ell) → A) ≃ (Fin N → Fin ell → A) :=
  (Equiv.piCongrLeft (fun _ : Fin (N * ell) ↦ A)
    (finProdFinEquiv : Fin N × Fin ell ≃ Fin (N * ell))).symm.trans
      (Equiv.curry (Fin N) (Fin ell) A)

omit [Fintype A] in theorem ofFn_blockTupleEquiv (N ell : ℕ) (x : Fin (N * ell) → A) :
    List.ofFn x = flattenBlocks ell (List.ofFn (blockTupleEquiv N ell x)) := by
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  rw [List.map_ofFn]
  rw [List.ofFn_inj]
  funext i
  apply congrArg List.ofFn
  funext j
  simp [blockTupleEquiv, finProdFinEquiv, Nat.add_comm, Nat.mul_comm]

/-- The exact product-weighted expectation of a function on words of length `n`. -/
def weightedTupleSum (p : A → ℝ) (f : List A → ℝ) (n : ℕ) : ℝ :=
  ∑ x : Fin n → A, wordWeight p (List.ofFn x) * f (List.ofFn x)

/-- Regrouping consecutive letters into blocks preserves the exact weighted sum. -/
theorem weightedTupleSum_mul_eq_blockSum
    (p : A → ℝ) (f : List A → ℝ) (N ell : ℕ) :
    weightedTupleSum p f (N * ell) =
      weightedTupleSum (blockWeight p ell) (fun w ↦ f (flattenBlocks ell w)) N := by
  classical
  unfold weightedTupleSum
  apply Fintype.sum_equiv (blockTupleEquiv N ell)
  intro x
  rw [ofFn_blockTupleEquiv N ell x, wordWeight_flattenBlocks]

/-- Split an exact weighted sum into an initial segment and a residual suffix. -/
theorem weightedTupleSum_add_eq_prefix_suffix
    (p : A → ℝ) (f : List A → ℝ) (n s : ℕ) :
    weightedTupleSum p f (n + s) =
      ∑ x : Fin n → A, ∑ ξ : Fin s → A,
        wordWeight p (List.ofFn x) * wordWeight p (List.ofFn ξ) *
          f (List.ofFn x ++ List.ofFn ξ) := by
  classical
  unfold weightedTupleSum
  rw [← Fintype.sum_prod_type (fun pair : (Fin n → A) × (Fin s → A) ↦
    wordWeight p (List.ofFn pair.1) * wordWeight p (List.ofFn pair.2) *
      f (List.ofFn pair.1 ++ List.ofFn pair.2))]
  apply Fintype.sum_equiv (Fin.appendEquiv n s).symm
  intro x
  simp only [Fin.appendEquiv_symm_apply]
  rw [List.ofFn_add (f := x), wordWeight_append]
  rfl

/-- Exact block coding at the residue length `N * ell + s`.  The last `s`
letters remain as the suffix used by the renewal boundary formula. -/
theorem weightedTupleSum_mul_add_eq_block_suffix
    (p : A → ℝ) (f : List A → ℝ) (N ell s : ℕ) :
    weightedTupleSum p f (N * ell + s) =
      ∑ w : Fin N → (Fin ell → A), ∑ ξ : Fin s → A,
        wordWeight (blockWeight p ell) (List.ofFn w) * wordWeight p (List.ofFn ξ) *
          f (flattenBlocks ell (List.ofFn w) ++ List.ofFn ξ) := by
  rw [weightedTupleSum_add_eq_prefix_suffix]
  classical
  apply Fintype.sum_equiv (blockTupleEquiv N ell)
  intro x
  rw [ofFn_blockTupleEquiv N ell x, wordWeight_flattenBlocks]

end

section WordAverages

variable [TopologicalSpace A] [DiscreteTopology A] [Fintype A] [Nonempty A]

theorem weightedWordExtensionAverage_eq_weightedTupleSum
    (p : A → ℝ) (q : BoundedWordFunction A) (n : ℕ) :
    weightedWordExtensionAverage p q n [] = weightedTupleSum p q n := by
  rw [weightedWordExtensionAverage_eq_tuple_sum]
  rfl

/-- Exact IID block coding for a Boolean predicate at length `N * ell + s`.
The outer finite mixture is over the residual suffix `ξ : Fin s → A`. -/
theorem weightedBooleanWordExtension_mul_add_eq_block_suffix
    (p : A → ℝ) (q : List A → Bool) (N ell s : ℕ) :
    weightedWordExtensionAverage p (booleanWordIndicator q) (N * ell + s) [] =
      ∑ ξ : Fin s → A, wordWeight p (List.ofFn ξ) *
        weightedWordExtensionAverage (blockWeight p ell)
          (booleanWordIndicator (fun w : List (Fin ell → A) ↦
            q (flattenBlocks ell w ++ List.ofFn ξ))) N [] := by
  rw [weightedWordExtensionAverage_eq_weightedTupleSum,
    weightedTupleSum_mul_add_eq_block_suffix]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ξ hξ
  rw [weightedWordExtensionAverage_eq_weightedTupleSum]
  unfold weightedTupleSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  simp only [booleanWordIndicator_apply]
  ring

end WordAverages

end IndependentZeroBlocks
