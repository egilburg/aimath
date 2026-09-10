import FiniteMonoidMortality.MatrixWordScalarExtension
import FiniteMonoidMortality.MinimalRankCompression
import FiniteMonoidMortality.MortalityBudget
import FiniteMonoidMortality.RankSensitiveMortality

set_option autoImplicit false

noncomputable section

namespace FiniteMonoidMortality

def improvedMortalityBound (n : ℕ) : ℕ := n * 2 ^ n - n * (n + 1) / 2

theorem exists_zero_word_of_rank_sensitive_sandwich
    {A : Type*} {n : ℕ} (M : A → Matrix (Fin n) (Fin n) ℝ)
    (hdrop : ∀ h : List A, matrixWord M h ≠ 0 →
      ∃ w : List A,
        w.length ≤ 1 + n * (n + 1) / 2 -
          (matrixWord M h).rank * ((matrixWord M h).rank + 1) / 2 ∧
        (matrixWord M (h ++ w ++ h)).rank < (matrixWord M h).rank) :
    ∃ z : List A, matrixWord M z = 0 ∧ z.length ≤ improvedMortalityBound n := by
  have aux : ∀ r : ℕ, ∀ h : List A, (matrixWord M h).rank = r →
      h.length ≤ mortalityBudget n (n - r) →
      ∃ z : List A, matrixWord M z = 0 ∧ z.length ≤ mortalityBudget n n := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro h hr hl
      by_cases hz : matrixWord M h = 0
      · exact ⟨h, hz, hl.trans (mortalityBudget_mono n (by omega))⟩
      · have hrn : r ≤ n := by
          have := Matrix.rank_le_card_width (matrixWord M h)
          simpa [hr] using this
        obtain ⟨w, hw, hd⟩ := hdrop h hz
        let q := (matrixWord M (h ++ w ++ h)).rank
        have hqr : q < r := by simpa [q, hr] using hd
        apply ih q hqr (h ++ w ++ h) rfl
        have hstep : (h ++ w ++ h).length ≤ mortalityBudget n (n - r + 1) := by
          rw [mortalityBudget]
          have hnr : n - (n - r) = r := by omega
          rw [hnr, rankTriangle_eq, rankTriangle_eq]
          simp only [List.length_append] at *
          rw [hr] at hw
          omega
        exact hstep.trans (mortalityBudget_mono n (by omega))
  obtain ⟨z, hz, hl⟩ := aux n [] (by simp [Matrix.rank_one]) (by simp [mortalityBudget])
  exact ⟨z, hz, by simpa [mortalityBudget_full, improvedMortalityBound] using hl⟩

theorem exists_improved_short_zero_word_of_finite_real_monoid
    {A : Type*} {n : ℕ} (M : A → Matrix (Fin n) (Fin n) ℝ)
    (hfinite : (Set.range (matrixWord M)).Finite)
    (hzero : ∃ z : List A, matrixWord M z = 0) :
    ∃ z : List A, matrixWord M z = 0 ∧ z.length ≤ improvedMortalityBound n := by
  exact exists_zero_word_of_rank_sensitive_sandwich M
    (exists_rank_sensitive_sandwich_of_finite M hfinite hzero)

theorem exists_improved_short_zero_word_of_finite_rational_monoid
    {A : Type*} {n : ℕ} (M : A → Matrix (Fin n) (Fin n) ℚ)
    (hfinite : (Set.range (matrixWord M)).Finite)
    (hzero : ∃ z : List A, matrixWord M z = 0) :
    ∃ z : List A, matrixWord M z = 0 ∧ z.length ≤ improvedMortalityBound n := by
  let f : ℚ →+* ℝ := Rat.castHom ℝ
  let MR : A → Matrix (Fin n) (Fin n) ℝ := fun a => (M a).map f
  have hf := finite_matrixWord_range_map f M hfinite
  have hz : ∃ z : List A, matrixWord MR z = 0 := by
    obtain ⟨z, hz⟩ := hzero
    exact ⟨z, (matrixWord_map_eq_zero_iff f M z).mpr hz⟩
  obtain ⟨z, hz, hl⟩ := exists_improved_short_zero_word_of_finite_real_monoid MR hf hz
  exact ⟨z, (matrixWord_map_eq_zero_iff f M z).mp hz, hl⟩

end FiniteMonoidMortality
