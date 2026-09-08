import FiniteMonoidMortality.InvariantForms
import FiniteMonoidMortality.QuadraticObservation
import FiniteMonoidMortality.Descent

set_option autoImplicit false

/-!
# An exponential mortality bound for finite real matrix monoids

The entire word-product monoid is assumed finite and to contain zero. The generator indexing type need not be finite. The real theorem and rational specialization have the same explicit bound.
-/

noncomputable section

open scoped BigOperators

namespace FiniteMonoidMortality

/-- The uniform mortality bound in dimension `n > 0`. -/
def finiteMortalityBound (n : ℕ) : ℕ :=
  2 ^ (n - 1) + (2 ^ (n - 1) - 1) * (n * (n + 1) / 2)

/-- At every positive-rank word, a middle of quadratic length decreases the
rank of its sandwich. The two outside copies are retained in the conclusion. -/
theorem exists_short_rank_decreasing_sandwich_of_finite
    {A : Type*} {n : ℕ} (M : A → Matrix (Fin n) (Fin n) ℝ)
    (hfinite : (Set.range (matrixWord M)).Finite)
    (hzero : ∃ z : List A, matrixWord M z = 0)
    (h : List A) (hh : matrixWord M h ≠ 0) :
    ∃ w : List A, w.length ≤ n * (n + 1) / 2 ∧
      (matrixWord M (h ++ w ++ h)).rank < (matrixWord M h).rank := by
  obtain ⟨U, V, hfac⟩ := exists_rankFactorization (matrixWord M h)
  obtain ⟨Q, hQsymm, hQtrace, hQinv⟩ :=
    exists_invariant_quadraticForm_compressedReturn_of_finite
      (rank_pos_of_ne_zero _ hh) M h U V hfac hfinite
  let B := U * Q * U.transpose
  have hB : B.IsSymm := by
    change B.transpose = B
    simp only [B, Matrix.transpose_mul, Matrix.transpose_transpose, hQsymm]
    simp only [Matrix.mul_assoc]
  let ell := traceSandwichMatrixDual V
  have heval (w : List A) :
      ell (matrixWord M w * B * (matrixWord M w).transpose) =
        Matrix.trace (compressedReturn M U V w * Q *
          (compressedReturn M U V w).transpose) := by
    simp only [ell, traceSandwichMatrixDual_apply, B, compressedReturn,
      Matrix.transpose_mul, Matrix.mul_assoc]
  have hsignal : ∃ z : List A,
      Matrix.trace Q - ell (matrixWord M z * B * (matrixWord M z).transpose) ≠ 0 := by
    obtain ⟨z, hz⟩ := hzero
    refine ⟨z, ?_⟩
    simpa [hz] using hQtrace.ne'
  obtain ⟨w, hwlen, hw⟩ := exists_short_quadratic_observation_matrixDual_ne_zero
    M B hB ell (Matrix.trace Q) hsignal
  refine ⟨w, hwlen, ?_⟩
  apply rank_wordSandwich_lt_of_invariantTraceDefect_ne_zero M h w U V hfac Q (hQinv w)
  simpa only [invariantTraceDefect, heval] using hw

/-- Main real mortality theorem: a finite entire word monoid containing zero
has a zero word of length at most `finiteMortalityBound n`.
No finiteness of the generator indexing type is required. -/
theorem exists_short_zero_word_of_finite_real_monoid
    {A : Type*} {n : ℕ} (hn : 0 < n)
    (M : A → Matrix (Fin n) (Fin n) ℝ)
    (hfinite : (Set.range (matrixWord M)).Finite)
    (hzero : ∃ z : List A, matrixWord M z = 0) :
    ∃ z : List A, matrixWord M z = 0 ∧ z.length ≤ finiteMortalityBound n := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hdrop := exists_short_rank_decreasing_sandwich_of_finite M hfinite hzero
  obtain ⟨z, hz, hl⟩ := exists_zero_word_bound_of_short_sandwich
    M (n * (n + 1) / 2) hzero hdrop
  exact ⟨z, hz, by simpa [finiteMortalityBound] using hl⟩

/-- Rational specialization, with exactly the same dimension and word bound.
Extension to the reals preserves finite word range and reflects the zero word. -/
theorem exists_short_zero_word_of_finite_rational_monoid
    {A : Type*} {n : ℕ} (hn : 0 < n)
    (M : A → Matrix (Fin n) (Fin n) ℚ)
    (hfinite : (Set.range (matrixWord M)).Finite)
    (hzero : ∃ z : List A, matrixWord M z = 0) :
    ∃ z : List A, matrixWord M z = 0 ∧ z.length ≤ finiteMortalityBound n := by
  let f : ℚ →+* ℝ := Rat.castHom ℝ
  let MR : A → Matrix (Fin n) (Fin n) ℝ := fun a => (M a).map f
  have hRfinite : (Set.range (matrixWord MR)).Finite :=
    finite_matrixWord_range_map f M hfinite
  have hRzero : ∃ z : List A, matrixWord MR z = 0 := by
    obtain ⟨z, hz⟩ := hzero
    exact ⟨z, (matrixWord_map_eq_zero_iff f M z).mpr hz⟩
  obtain ⟨z, hz, hl⟩ := exists_short_zero_word_of_finite_real_monoid
    hn MR hRfinite hRzero
  exact ⟨z, (matrixWord_map_eq_zero_iff f M z).mp hz, hl⟩

end FiniteMonoidMortality
