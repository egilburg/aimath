import SierpinskiFormal.MinimalRankCompression
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace IndependentZeroBlocks

/-- The cost of at most `r` sandwich reductions, including both copies of
the accumulated word at every step. -/
def rankDescentBudget (D r L : ℕ) : ℕ :=
  2 ^ r * L + (2 ^ r - 1) * D

@[simp] theorem rankDescentBudget_zero (D L : ℕ) :
    rankDescentBudget D 0 L = L := by
  simp [rankDescentBudget]

theorem rankDescentBudget_succ (D r L : ℕ) :
    rankDescentBudget D r (2 * L + D) = rankDescentBudget D (r + 1) L := by
  have hp : 1 ≤ 2 ^ r := Nat.one_le_pow r 2 (by omega)
  have hp' : 2 ^ r - 1 + 1 = 2 ^ r := Nat.sub_add_cancel hp
  have htwo : 2 ^ r * 2 - 1 = 2 * (2 ^ r - 1) + 1 := by omega
  simp only [rankDescentBudget, pow_succ, htwo]
  nlinarith

theorem rankDescentBudget_mono_length (D r : ℕ) {L K : ℕ} (h : L ≤ K) :
    rankDescentBudget D r L ≤ rankDescentBudget D r K := by
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ h) _

section Descent

variable {F A ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]

/-- A uniform short-middle lemma gives a global zero word. This interface
does not suppress the accumulated prefix cost. The final mortality theorem
will discharge its local rank-drop hypothesis. -/
theorem exists_zero_word_of_short_sandwich
    (M : A → Matrix ι ι F) (D : ℕ)
    (hdrop : ∀ h : List A, matrixWord M h ≠ 0 →
      ∃ w : List A, w.length ≤ D ∧
        (matrixWord M (h ++ w ++ h)).rank < (matrixWord M h).rank)
    (r : ℕ) (h : List A) (hrank : (matrixWord M h).rank ≤ r) :
    ∃ z : List A, matrixWord M z = 0 ∧
      z.length ≤ rankDescentBudget D r h.length := by
  induction r generalizing h with
  | zero =>
      refine ⟨h, ?_, by simp⟩
      by_contra hn
      exact (Nat.not_lt_of_ge hrank) (rank_pos_of_ne_zero _ hn)
  | succ r ih =>
      by_cases hz : matrixWord M h = 0
      · refine ⟨h, hz, ?_⟩
        have hp : 1 ≤ 2 ^ (r + 1) := Nat.one_le_pow (r + 1) 2 (by omega)
        unfold rankDescentBudget
        calc
          h.length = 1 * h.length := by omega
          _ ≤ 2 ^ (r + 1) * h.length := Nat.mul_le_mul_right _ hp
          _ ≤ _ := Nat.le_add_right _ _
      · obtain ⟨w, hw, hd⟩ := hdrop h hz
        obtain ⟨z, hz, hl⟩ := ih (h ++ w ++ h) (by omega)
        refine ⟨z, hz, hl.trans ?_⟩
        calc
          rankDescentBudget D r (h ++ w ++ h).length ≤
              rankDescentBudget D r (2 * h.length + D) := by
            apply rankDescentBudget_mono_length
            simp only [List.length_append]
            omega
          _ = _ := rankDescentBudget_succ D r h.length

/-- In positive dimension a mortal generating family contains a singular letter. -/
theorem exists_singular_letter_of_zero_word [Nonempty ι]
    (M : A → Matrix ι ι F) (hz : ∃ z : List A, matrixWord M z = 0) :
    ∃ a : A, (M a).rank < Fintype.card ι := by
  by_contra h
  push Not at h
  have hu : ∀ a, IsUnit (M a) := fun a =>
    isUnit_of_rank_eq_card _ (Nat.le_antisymm (Matrix.rank_le_card_width _) (h a))
  have hw : ∀ w : List A, IsUnit (matrixWord M w) := by
    intro w
    induction w with
    | nil => simp
    | cons a w ih =>
        simpa [matrixWord] using (hu a).mul ih
  obtain ⟨z, hz⟩ := hz
  have hzunit := hw z
  rw [hz] at hzunit
  exact not_isUnit_zero hzunit

/-- Exact global bound from a local short-sandwich theorem and mortality.
The singular initial letter saves one rank-descent step. -/
theorem exists_zero_word_bound_of_short_sandwich [Nonempty ι]
    (M : A → Matrix ι ι F) (D : ℕ)
    (hz : ∃ z : List A, matrixWord M z = 0)
    (hdrop : ∀ h : List A, matrixWord M h ≠ 0 →
      ∃ w : List A, w.length ≤ D ∧
        (matrixWord M (h ++ w ++ h)).rank < (matrixWord M h).rank) :
    ∃ z : List A, matrixWord M z = 0 ∧
      z.length ≤ 2 ^ (Fintype.card ι - 1) +
        (2 ^ (Fintype.card ι - 1) - 1) * D := by
  obtain ⟨a, ha⟩ := exists_singular_letter_of_zero_word M hz
  have harank : (matrixWord M [a]).rank ≤ Fintype.card ι - 1 := by
    simpa [matrixWord] using (show (M a).rank ≤ Fintype.card ι - 1 by omega)
  obtain ⟨z, hz, hl⟩ := exists_zero_word_of_short_sandwich M D hdrop
    (Fintype.card ι - 1) [a] harank
  exact ⟨z, hz, by simpa [rankDescentBudget] using hl⟩

end Descent

end IndependentZeroBlocks
