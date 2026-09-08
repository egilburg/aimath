import Publication

set_option autoImplicit false

/-!
# Compatibility with the previously released claims

Each statement below is copied from the original paper package, with its
original matrix-word and bound definitions reproduced transparently here.
Lean checks that the refactored endpoint inhabits exactly that statement.
Only the namespace changes; no original proof modules are imported.
-/

namespace PublishedSpecification

variable {F A ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]

def matrixWord (M : A → Matrix ι ι F) (w : List A) : Matrix ι ι F :=
  (w.map M).prod

def finiteMortalityBound (n : ℕ) : ℕ :=
  2 ^ (n - 1) + (2 ^ (n - 1) - 1) * (n * (n + 1) / 2)

theorem exists_short_zero_word_of_finite_real_monoid
    {A : Type*} {n : ℕ} (hn : 0 < n)
    (M : A → Matrix (Fin n) (Fin n) ℝ)
    (hfinite : (Set.range (matrixWord M)).Finite)
    (hzero : ∃ z : List A, matrixWord M z = 0) :
    ∃ z : List A, matrixWord M z = 0 ∧ z.length ≤ finiteMortalityBound n := by
  exact FiniteMonoidMortality.exists_short_zero_word_of_finite_real_monoid hn M hfinite hzero

theorem exists_short_zero_word_of_finite_rational_monoid
    {A : Type*} {n : ℕ} (hn : 0 < n)
    (M : A → Matrix (Fin n) (Fin n) ℚ)
    (hfinite : (Set.range (matrixWord M)).Finite)
    (hzero : ∃ z : List A, matrixWord M z = 0) :
    ∃ z : List A, matrixWord M z = 0 ∧ z.length ≤ finiteMortalityBound n := by
  exact FiniteMonoidMortality.exists_short_zero_word_of_finite_rational_monoid hn M hfinite hzero

theorem exists_short_rank_decreasing_sandwich_of_finite
    {A : Type*} {n : ℕ} (M : A → Matrix (Fin n) (Fin n) ℝ)
    (hfinite : (Set.range (matrixWord M)).Finite)
    (hzero : ∃ z : List A, matrixWord M z = 0)
    (h : List A) (hh : matrixWord M h ≠ 0) :
    ∃ w : List A, w.length ≤ n * (n + 1) / 2 ∧
      (matrixWord M (h ++ w ++ h)).rank < (matrixWord M h).rank := by
  exact FiniteMonoidMortality.exists_short_rank_decreasing_sandwich_of_finite M hfinite hzero h hh

end PublishedSpecification

#print axioms PublishedSpecification.exists_short_zero_word_of_finite_real_monoid
#print axioms PublishedSpecification.exists_short_zero_word_of_finite_rational_monoid
#print axioms PublishedSpecification.exists_short_rank_decreasing_sandwich_of_finite
