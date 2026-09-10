import FiniteMonoidMortality.FiniteMortalityCompression
import FiniteMonoidMortality.PlaneEllipse
import FiniteMonoidMortality.RankOneSandwich
import Mathlib.LinearAlgebra.Matrix.Invertible

set_option autoImplicit false

noncomputable section

open Matrix

namespace FiniteMonoidMortality

theorem exists_invariant_vector_form (S : Set (Matrix (Fin 2) (Fin 2) ℝ))
    (hf : S.Finite) (hm : ∀ ⦃X Y⦄, X ∈ S → Y ∈ S → X*Y ∈ S) :
    ∃ Q : Matrix (Fin 2) (Fin 2) ℝ, Q.PosDef ∧
      ∀ g ∈ S, IsUnit g → g.transpose*Q*g=Q := by
  let R := Matrix.transpose '' S
  have hr : R.Finite := hf.image Matrix.transpose
  have hmR : ∀ ⦃X Y : Matrix (Fin 2) (Fin 2) ℝ⦄, X ∈ R → Y ∈ R → X*Y ∈ R := by
    rintro X Y ⟨x,hx,rfl⟩ ⟨y,hy,rfl⟩
    exact ⟨y*x,hm hy hx,Matrix.transpose_mul y x⟩
  obtain ⟨Q,_,hp,hi⟩ := exists_invariant_posDef_of_finite_mul_mem R hr hmR
  refine ⟨Q,hp,fun g hg hu => ?_⟩
  simpa using hi g.transpose ⟨g,hg,rfl⟩ (by simpa using hu)

theorem planeQuad_matrix (Q : Matrix (Fin 2) (Fin 2) ℝ) (x : Fin 2 → ℝ) :
    planeQuad (Q 0 0) (Q 0 1+Q 1 0) (Q 1 1) x = x ⬝ᵥ (Q *ᵥ x) := by
  simp [planeQuad,dotProduct,Matrix.mulVec,Fin.sum_univ_two]
  ring

theorem planeQuad_pos_of_posDef (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Q.PosDef)
    (x : Fin 2 → ℝ) (hx : x ≠ 0) :
    0 < planeQuad (Q 0 0) (Q 0 1+Q 1 0) (Q 1 1) x := by
  rw [planeQuad_matrix]
  simpa using hQ.dotProduct_mulVec_pos hx

theorem planeQuad_invariant (Q g : Matrix (Fin 2) (Fin 2) ℝ)
    (hg : g.transpose*Q*g=Q) (x : Fin 2 → ℝ) :
    planeQuad (Q 0 0) (Q 0 1+Q 1 0) (Q 1 1) (g *ᵥ x) =
      planeQuad (Q 0 0) (Q 0 1+Q 1 0) (Q 1 1) x := by
  rw [planeQuad_matrix,planeQuad_matrix]
  calc
    (g *ᵥ x) ⬝ᵥ (Q *ᵥ (g *ᵥ x)) = (Q *ᵥ (g *ᵥ x)) ⬝ᵥ (g *ᵥ x) := dotProduct_comm _ _
    _ = x ⬝ᵥ (g.transpose *ᵥ (Q *ᵥ (g *ᵥ x))) := (Matrix.dotProduct_transpose_mulVec g x _).symm
    _ = x ⬝ᵥ ((g.transpose*Q*g) *ᵥ x) := by simp only [Matrix.mulVec_mulVec,Matrix.mul_assoc]
    _ = x ⬝ᵥ (Q *ᵥ x) := by rw [hg]

end FiniteMonoidMortality
