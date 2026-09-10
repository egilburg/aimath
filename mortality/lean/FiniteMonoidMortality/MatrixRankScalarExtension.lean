import FiniteMonoidMortality.MatrixWordScalarExtension

open Matrix

set_option autoImplicit false

noncomputable section

namespace FiniteMonoidMortality

theorem matrix_rank_map_field {F K ι : Type*} [Field F] [Field K]
    [Fintype ι] [DecidableEq ι] (f : F →+* K) (H : Matrix ι ι F) :
    (H.map f).rank = H.rank := by
  classical
  obtain ⟨V, U, e, hV, hU, hH⟩ := Matrix.exists_rank_normal_form H
  have hV' := hV.map (f.mapMatrix : Matrix ι ι F →+* Matrix ι ι K)
  have hU' := hU.map (f.mapMatrix : Matrix ι ι F →+* Matrix ι ι K)
  change IsUnit (V.map f) at hV'
  change IsUnit (U.map f) at hU'
  have hm := congrArg (fun X : Matrix ι ι F => X.map f) hH
  simp only [Matrix.map_mul] at hm
  have hnormal : ((Matrix.fromBlocks (1 : Matrix (Fin H.rank) (Fin H.rank) F)
      0 0 (0 : Matrix (Fin (Fintype.card ι - H.rank)) (Fin (Fintype.card ι - H.rank)) F)).submatrix e e).map f =
      (Matrix.fromBlocks (1 : Matrix (Fin H.rank) (Fin H.rank) K) 0 0 0).submatrix e e := by
    ext i j
    simp only [Matrix.map_apply, Matrix.submatrix_apply]
    cases e i <;> cases e j <;> simp [Matrix.one_apply]
  rw [hnormal] at hm
  have hr : (H.map f).rank = ((V.map f * H.map f) * U.map f).rank := by
    rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnit_iff_isUnit_det _ |>.mp hU'),
      Matrix.rank_mul_eq_right_of_isUnit_det _ _ (Matrix.isUnit_iff_isUnit_det _ |>.mp hV')]
  rw [hr, hm, Matrix.rank_submatrix _ e e]
  rw [← Matrix.diagonal_one, ← Matrix.diagonal_zero, Matrix.fromBlocks_diagonal,
    Matrix.rank_diagonal]
  rw [Fintype.card_congr Equiv.subtypeSum]
  simp

end FiniteMonoidMortality
