import FiniteMonoidMortality.FiniteMortalityCompression
import FiniteMonoidMortality.MatrixRankScalarExtension
import FiniteMonoidMortality.MatrixWordScalarExtension
import FiniteMonoidMortality.MinimalRankCompression
import FiniteMonoidMortality.MortalityBudget
import FiniteMonoidMortality.RankSensitiveMortality
import FiniteMonoidMortality.ReachableSpanMortality
import FiniteMonoidMortality.ShortQuadraticObservation
import FiniteMonoidMortality.SubspaceEscape

set_option autoImplicit false

noncomputable section

namespace FiniteMonoidMortality

theorem exists_rank_sensitive_sandwich_below_word
    {A : Type*} {n : ℕ} (M : A → Matrix (Fin n) (Fin n) ℝ)
    (hfinite : (Set.range (matrixWord M)).Finite)
    (h : List A) (hlower : ∃ z : List A, (matrixWord M z).rank < (matrixWord M h).rank) :
    ∃ w : List A,
      w.length ≤ 1 + n * (n + 1) / 2 -
        (matrixWord M h).rank * ((matrixWord M h).rank + 1) / 2 ∧
      (matrixWord M (h ++ w ++ h)).rank < (matrixWord M h).rank := by
  obtain ⟨U, V, hfac⟩ := exists_rankFactorization (matrixWord M h)
  by_cases hd : (matrixWord M (h ++ [] ++ h)).rank < (matrixWord M h).rank
  · exact ⟨[], Nat.zero_le _, hd⟩
  have hu : IsUnit (V * U) := by
    have hl : (matrixWord M h).rank ≤
        (matrixWord M h * (1 : Matrix (Fin n) (Fin n) ℝ) * matrixWord M h).rank := by
      simpa only [matrixWord_append, matrixWord_nil] using Nat.le_of_not_gt hd
    simpa using sandwich_isUnit_of_rank_lower_bound U V
      (matrixWord M h) 1 hfac hl
  obtain ⟨u, hu⟩ := hu
  let W := U * u.inv
  have hVW : V * W = 1 := by
    dsimp [W]
    rw [← Matrix.mul_assoc, ← hu]
    exact u.val_inv
  obtain ⟨Q, hQs, hQt, hQi⟩ :=
    exists_invariant_posDef_compressedReturn_of_finite
      (by obtain ⟨z, hz⟩ := hlower; omega) M h U V hfac hfinite
  let q : SymmetricMatrix (matrixWord M h).rank := ⟨Q, hQs⟩
  let B := U * Q * U.transpose
  have hB : B.IsSymm := by
    change B.transpose = B
    simp only [B, Matrix.transpose_mul, Matrix.transpose_transpose, hQs,
      Matrix.mul_assoc]
  let F := matrixInvariantDefect V q
  let T := quadraticObservationLetter M
  let seed : QuadraticObservationState n := (1, ⟨B, hB⟩)
  have heval (w : List A) :
      (F (linearWord T w seed)).1 =
        compressedReturn M U V w * Q * (compressedReturn M U V w).transpose - Q := by
    simp only [T, seed, linearWord_quadraticObservationLetter]
    change V * (matrixWord M w * B * (matrixWord M w).transpose) * V.transpose -
      (1 : ℝ) • Q = _
    simp only [B, compressedReturn, Matrix.transpose_mul, Matrix.mul_assoc, one_smul]
  have hex : ∃ w : List A, linearWord T w seed ∉ LinearMap.ker F := by
    obtain ⟨z, hz⟩ := hlower
    refine ⟨z, ?_⟩
    intro hm
    have he := congrArg Subtype.val (LinearMap.mem_ker.mp hm)
    rw [heval] at he
    have heq : compressedReturn M U V z * Q * (compressedReturn M U V z).transpose = Q :=
      sub_eq_zero.mp he
    have hle : Q.rank ≤ (matrixWord M z).rank := by
      rw [← heq]
      exact (Matrix.rank_mul_le_left _ _).trans
        ((Matrix.rank_mul_le_left _ _).trans
          ((Matrix.rank_mul_le_left (V * matrixWord M z) U).trans
            (Matrix.rank_mul_le_right V (matrixWord M z))))
    have hQr := Matrix.rank_of_isUnit Q hQt.isUnit
    simp only [Fintype.card_fin] at hQr
    omega
  obtain ⟨w, hw, hd⟩ := exists_short_linearWord_not_mem T seed (LinearMap.ker F) hex
  refine ⟨w, ?_, ?_⟩
  · simpa only [F, finrank_ker_matrixInvariantDefect V W hVW q] using hw
  · apply Nat.lt_of_not_ge
    intro hl
    have hunit : IsUnit (compressedReturn M U V w) := by
      apply sandwich_isUnit_of_rank_lower_bound U V (matrixWord M h)
        (matrixWord M w) hfac
      simpa only [matrixWord_append] using hl
    apply hd
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    rw [heval, hQi w hunit, sub_self]
    rfl

def minimumRankBound (n s : ℕ) : ℕ :=
  n * 2 ^ (n - s) + s * (s - 1) / 2 - n * (n + 1) / 2

theorem mortalityBudget_at_minimum (n s : ℕ) (hs : s ≤ n) :
    mortalityBudget n (n - s) = minimumRankBound n s := by
  have hi := mortalityBudget_identity n (n - s) (Nat.sub_le _ _)
  have hns : n - (n - s) = s := by omega
  rw [hns] at hi
  have ht : rankTriangle s = s + s * (s - 1) / 2 := by
    cases s with
    | zero => simp [rankTriangle]
    | succ k =>
      simp only [rankTriangle, Nat.add_sub_cancel]
      rw [show (k + 1) * k = k * (k + 1) by exact Nat.mul_comm _ _, ← rankTriangle_eq]
      omega
  rw [ht, rankTriangle_eq] at hi
  unfold minimumRankBound
  omega

@[simp] theorem minimumRankBound_full (n : ℕ) : minimumRankBound n n = 0 := by
  rw [← mortalityBudget_at_minimum n n le_rfl]
  simp [mortalityBudget]

@[simp] theorem minimumRankBound_zero (n : ℕ) :
    minimumRankBound n 0 = n * 2 ^ n - n * (n + 1) / 2 := by
  simp [minimumRankBound]

theorem exists_minimum_rank_word_of_minimizer
    {A : Type*} {n : ℕ} (M : A → Matrix (Fin n) (Fin n) ℝ)
    (hfinite : (Set.range (matrixWord M)).Finite)
    (z : List A) (hmin : ∀ w, (matrixWord M z).rank ≤ (matrixWord M w).rank) :
    ∃ w : List A, (matrixWord M w).rank = (matrixWord M z).rank ∧
      w.length ≤ minimumRankBound n (matrixWord M z).rank := by
  let s := (matrixWord M z).rank
  have aux : ∀ r, ∀ h : List A, (matrixWord M h).rank = r →
      h.length ≤ mortalityBudget n (n - r) →
      ∃ w : List A, (matrixWord M w).rank = s ∧
        w.length ≤ mortalityBudget n (n - s) := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro h hr hl
      by_cases he : r = s
      · exact ⟨h, hr.trans he, by simpa [he] using hl⟩
      · have hsr : s < r := by have := hmin h; dsimp [s] at *; omega
        have hrn : r ≤ n := by
          have := Matrix.rank_le_card_width (matrixWord M h)
          simpa [hr] using this
        obtain ⟨w, hw, hd⟩ := exists_rank_sensitive_sandwich_below_word M hfinite h
          ⟨z, by simpa [hr] using hsr⟩
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
  obtain ⟨w, hw, hl⟩ := aux n [] (by simp [Matrix.rank_one]) (by simp [mortalityBudget])
  refine ⟨w, hw, ?_⟩
  have hsn : s ≤ n := by simpa [s] using Matrix.rank_le_card_width (matrixWord M z)
  simpa [mortalityBudget_at_minimum n s hsn, s] using hl

theorem exists_minimum_rank_word_real_of_finite
    {A : Type*} {n : ℕ} (M : A → Matrix (Fin n) (Fin n) ℝ)
    (hfinite : (Set.range (matrixWord M)).Finite) :
    ∃ w : List A,
      (∀ v : List A, (matrixWord M w).rank ≤ (matrixWord M v).rank) ∧
      w.length ≤ minimumRankBound n (matrixWord M w).rank := by
  classical
  have hex : ∃ r : ℕ, ∃ w : List A, (matrixWord M w).rank = r := ⟨_, [], rfl⟩
  obtain ⟨z, hz⟩ := Nat.find_spec hex
  have hmin : ∀ v : List A, (matrixWord M z).rank ≤ (matrixWord M v).rank := by
    intro v
    rw [hz]
    exact Nat.find_min' hex ⟨v, rfl⟩
  obtain ⟨w, hw, hl⟩ := exists_minimum_rank_word_of_minimizer M hfinite z hmin
  exact ⟨w, fun v => hw ▸ hmin v, by simpa [hw] using hl⟩

theorem exists_minimum_rank_word_rational_of_finite
    {A : Type*} {n : ℕ} (M : A → Matrix (Fin n) (Fin n) ℚ)
    (hfinite : (Set.range (matrixWord M)).Finite) :
    ∃ w : List A,
      (∀ v : List A, (matrixWord M w).rank ≤ (matrixWord M v).rank) ∧
      w.length ≤ minimumRankBound n (matrixWord M w).rank := by
  let f : ℚ →+* ℝ := Rat.castHom ℝ
  let MR : A → Matrix (Fin n) (Fin n) ℝ := fun a => (M a).map f
  have hr : ∀ w : List A, (matrixWord MR w).rank = (matrixWord M w).rank := by
    intro w
    rw [matrixWord_map f M w]
    exact matrix_rank_map_field f _
  obtain ⟨w, hw, hl⟩ := exists_minimum_rank_word_real_of_finite MR
    (finite_matrixWord_range_map f M hfinite)
  exact ⟨w, fun v => by simpa only [hr] using hw v, by simpa only [hr] using hl⟩

end FiniteMonoidMortality
