import SierpinskiFormal.MatrixRadixRegularity
import Mathlib.Data.Matrix.Block

set_option autoImplicit false
namespace IndependentZeroBlocks
open scoped BigOperators

variable {K : Type*} [CommRing K]

theorem IsRadixRegular.const (b : ℕ) (hb : 2 ≤ b) (c : K) :
    IsRadixRegular b (fun _ => c) := by
  let u : ℕ → Unit → K := fun _ _ => c
  have hrec : ∀ n (r : Fin b), u (b * n + r.val) =
      Matrix.mulVecLin (1 : Matrix Unit Unit K) (u n) := by
    intro n r
    simp [Matrix.mulVecLin_apply, u]
  exact matrix_observation_isRadixRegular b hb (fun _ => 1) u hrec (LinearMap.proj ())

theorem IsRadixRegular.add (b : ℕ) (hb : 2 ≤ b) {f g : ℕ → K}
    (hf : IsRadixRegular b f) (hg : IsRadixRegular b g) :
    IsRadixRegular b (fun n => f n + g n) := by
  obtain ⟨d, M, u, l, hrec, hout⟩ := radixRegular_exists_matrix_representation b hb f hf
  obtain ⟨e, N, v, k, hrec', hout'⟩ := radixRegular_exists_matrix_representation b hb g hg
  let W : ℕ → (Fin d ⊕ Fin e) → K := fun n => Sum.elim (u n) (v n)
  let A : Fin b → Matrix (Fin d ⊕ Fin e) (Fin d ⊕ Fin e) K :=
    fun r => Matrix.fromBlocks (M r) 0 0 (N r)
  let L : Module.Dual K ((Fin d ⊕ Fin e) → K) := {
    toFun := fun x => l (fun i => x (Sum.inl i)) + k (fun i => x (Sum.inr i))
    map_add' := by
      intro x y
      change l ((fun i => x (Sum.inl i)) + (fun i => y (Sum.inl i))) +
        k ((fun i => x (Sum.inr i)) + (fun i => y (Sum.inr i))) = _
      rw [map_add, map_add]
      ring
    map_smul' := by
      intro c x
      change l (c • (fun i => x (Sum.inl i))) + k (c • (fun i => x (Sum.inr i))) =
        c • (l (fun i => x (Sum.inl i)) + k (fun i => x (Sum.inr i)))
      simp only [map_smul, smul_add] }
  have hW : ∀ n (r : Fin b), W (b * n + r.val) = Matrix.mulVecLin (A r) (W n) := by
    intro n r
    simp only [W, A, Matrix.mulVecLin_apply, Matrix.fromBlocks_mulVec,
      Matrix.zero_mulVec, add_zero, zero_add]
    rw [hrec, hrec']
    rfl
  have h := matrix_observation_isRadixRegular b hb A W hW L
  simpa only [L, W, LinearMap.coe_mk, AddHom.coe_mk, Sum.elim_inl, Sum.elim_inr,
    hout, hout'] using h

theorem IsRadixRegular.neg (b : ℕ) (hb : 2 ≤ b) {f : ℕ → K}
    (hf : IsRadixRegular b f) : IsRadixRegular b (fun n => -f n) := by
  obtain ⟨d, M, u, l, hrec, hout⟩ := radixRegular_exists_matrix_representation b hb f hf
  have h := matrix_observation_isRadixRegular b hb M u hrec (-l)
  simpa only [LinearMap.neg_apply, hout] using h

theorem IsRadixRegular.mul (b : ℕ) (hb : 2 ≤ b) {f g : ℕ → K}
    (hf : IsRadixRegular b f) (hg : IsRadixRegular b g) :
    IsRadixRegular b (fun n => f n * g n) := by
  classical
  obtain ⟨d, M, u, l, hrec, hout⟩ := radixRegular_exists_matrix_representation b hb f hf
  obtain ⟨e, N, v, k, hrec', hout'⟩ := radixRegular_exists_matrix_representation b hb g hg
  let W : ℕ → (Fin d × Fin e) → K := fun n ij => u n ij.1 * v n ij.2
  let A : Fin b → Matrix (Fin d × Fin e) (Fin d × Fin e) K :=
    fun r ij pq => M r ij.1 pq.1 * N r ij.2 pq.2
  let L : Module.Dual K ((Fin d × Fin e) → K) := coordinateRowDual
    (fun ij => l (coordinateUnit ij.1) * k (coordinateUnit ij.2))
  have hW : ∀ n (r : Fin b), W (b * n + r.val) = Matrix.mulVecLin (A r) (W n) := by
    intro n r
    funext ij
    rw [Matrix.mulVecLin_apply]
    change u (b * n + r.val) ij.1 * v (b * n + r.val) ij.2 = _
    rw [hrec, hrec', Matrix.mulVecLin_apply, Matrix.mulVecLin_apply]
    simp only [W, Matrix.mulVec, dotProduct, A, Fintype.sum_prod_type,
      Fintype.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hL : ∀ n, L (W n) = f n * g n := by
    intro n
    rw [← hout n, ← hout' n, dual_apply_eq_sum_single l, dual_apply_eq_sum_single k]
    simp only [L, coordinateRowDual_apply, W, Fintype.sum_prod_type,
      Fintype.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have h := matrix_observation_isRadixRegular b hb A W hW L
  simpa only [hL] using h

theorem IsRadixRegular.pow (b : ℕ) (hb : 2 ≤ b) {f : ℕ → K}
    (hf : IsRadixRegular b f) (n : ℕ) : IsRadixRegular b (fun k => f k ^ n) := by
  induction n with
  | zero => simpa using IsRadixRegular.const b hb (1 : K)
  | succ n ih => simpa only [pow_succ] using ih.mul b hb hf

end IndependentZeroBlocks
