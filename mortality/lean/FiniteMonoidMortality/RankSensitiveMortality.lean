import FiniteMonoidMortality.FiniteMortalityCompression
import FiniteMonoidMortality.MinimalRankCompression
import FiniteMonoidMortality.ReachableSpanMortality
import FiniteMonoidMortality.ShortQuadraticObservation
import FiniteMonoidMortality.SubspaceEscape

set_option autoImplicit false

noncomputable section

namespace FiniteMonoidMortality

def symmetricSandwichMap {n r : ℕ} (V : Matrix (Fin r) (Fin n) ℝ) :
    SymmetricMatrix n →ₗ[ℝ] SymmetricMatrix r where
  toFun X := ⟨V * X.1 * V.transpose, by
    change (V * X.1 * V.transpose).transpose = _
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, X.2.eq,
      Matrix.mul_assoc]⟩
  map_add' X Y := by
    apply Subtype.ext
    change V * (X.1 + Y.1) * V.transpose = _
    simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by
    apply Subtype.ext
    change V * (c • X.1) * V.transpose = _
    simp [Matrix.mul_smul, Matrix.smul_mul]

def matrixInvariantDefect {n r : ℕ} (V : Matrix (Fin r) (Fin n) ℝ)
    (Q : SymmetricMatrix r) : QuadraticObservationState n →ₗ[ℝ] SymmetricMatrix r :=
  (symmetricSandwichMap V).comp (LinearMap.snd ℝ ℝ (SymmetricMatrix n)) -
    (LinearMap.toSpanSingleton ℝ (SymmetricMatrix r) Q).comp
      (LinearMap.fst ℝ ℝ (SymmetricMatrix n))

theorem matrixInvariantDefect_surjective {n r : ℕ}
    (V : Matrix (Fin r) (Fin n) ℝ) (W : Matrix (Fin n) (Fin r) ℝ)
    (hVW : V * W = 1) (Q : SymmetricMatrix r) :
    Function.Surjective (matrixInvariantDefect V Q) := by
  intro R
  refine ⟨(0, symmetricSandwichMap W R), ?_⟩
  apply Subtype.ext
  change V * (W * R.1 * W.transpose) * V.transpose - 0 • Q.1 = R.1
  have ht : W.transpose * V.transpose = 1 := by
    rw [← Matrix.transpose_mul, hVW, Matrix.transpose_one]
  simp only [zero_smul, sub_zero]
  calc
    V * (W * R.1 * W.transpose) * V.transpose =
        (V * W) * R.1 * (W.transpose * V.transpose) := by
      simp only [Matrix.mul_assoc]
    _ = R.1 := by rw [hVW, ht, one_mul, mul_one]

theorem finrank_ker_matrixInvariantDefect {n r : ℕ}
    (V : Matrix (Fin r) (Fin n) ℝ) (W : Matrix (Fin n) (Fin r) ℝ)
    (hVW : V * W = 1) (Q : SymmetricMatrix r) :
    Module.finrank ℝ (LinearMap.ker (matrixInvariantDefect V Q)) =
      1 + n * (n + 1) / 2 - r * (r + 1) / 2 := by
  have hs := matrixInvariantDefect_surjective V W hVW Q
  have hr := LinearMap.finrank_range_add_finrank_ker (matrixInvariantDefect V Q)
  rw [LinearMap.range_eq_top.mpr hs] at hr
  simp only [finrank_top, Module.finrank_prod, Module.finrank_self,
    finrank_symmetricMatrix] at hr
  omega

theorem exists_rank_sensitive_sandwich_of_finite
    {A : Type*} {n : ℕ} (M : A → Matrix (Fin n) (Fin n) ℝ)
    (hfinite : (Set.range (matrixWord M)).Finite)
    (hzero : ∃ z : List A, matrixWord M z = 0)
    (h : List A) (hh : matrixWord M h ≠ 0) :
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
    exists_invariant_quadraticForm_compressedReturn_of_finite
      (rank_pos_of_ne_zero _ hh) M h U V hfac hfinite
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
    obtain ⟨z, hz⟩ := hzero
    refine ⟨z, ?_⟩
    intro hm
    have he := congrArg Subtype.val (LinearMap.mem_ker.mp hm)
    rw [heval] at he
    have hQzero : Q = 0 := by
      simpa [compressedReturn, hz] using he
    have := hQt
    simp [hQzero] at this
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

end FiniteMonoidMortality
