import FiniteMonoidMortality.FiniteMortalityCompression
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option autoImplicit false

namespace FiniteMonoidMortality

theorem matrix_two_square_of_det_zero (K : Matrix (Fin 2) (Fin 2) ℝ)
    (hd : K.det = 0) : K * K = K.trace • K := by
  simp only [Matrix.det_fin_two] at hd
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.trace, Fin.sum_univ_two] <;> nlinarith

theorem matrix_two_pow_of_det_zero (K : Matrix (Fin 2) (Fin 2) ℝ)
    (hd : K.det = 0) (j : ℕ) : K ^ (j+1) = K.trace ^ j • K := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, ih, Matrix.smul_mul, matrix_two_square_of_det_zero K hd,
      smul_smul, pow_succ]

theorem matrix_two_trace_quantized (K : Matrix (Fin 2) (Fin 2) ℝ)
    (hK : K ≠ 0) (hd : K.det = 0)
    (hf : (Set.range (fun j : ℕ => K ^ j)).Finite) :
    K.trace = 0 ∨ K.trace = 1 ∨ K.trace = -1 := by
  by_cases ht : K.trace = 0
  · exact Or.inl ht
  obtain ⟨i, j, hij, he⟩ := Set.Finite.exists_lt_map_eq_of_forall_mem
    (f := fun j : ℕ => K ^ (j+1)) (fun j => show K ^ (j+1) ∈ Set.range (fun j : ℕ => K ^ j) from ⟨j+1, rfl⟩) hf
  rw [matrix_two_pow_of_det_zero K hd, matrix_two_pow_of_det_zero K hd] at he
  have hp : K.trace ^ i = K.trace ^ j := (smul_left_injective ℝ hK) he
  have horder : IsOfFinOrder K.trace := by
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨j-i, by omega, ?_⟩
    apply (mul_left_cancel₀ (pow_ne_zero i ht))
    rw [← pow_add, Nat.add_sub_of_le hij.le, ← hp, mul_one]
  right
  rcases le_total 0 K.trace with h | h
  · exact Or.inl (horder.eq_one h)
  · exact Or.inr (horder.eq_neg_one h)

end FiniteMonoidMortality
