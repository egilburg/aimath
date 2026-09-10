import FiniteMonoidMortality.BlockMortality
import FiniteMonoidMortality.MinimalRankCompression
import FiniteMonoidMortality.MortalityExtremizer
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace FiniteMonoidMortality

abbrev smallBlockIndex (k1 k2 : ℕ) := Fin k1 ⊕ Fin k2

abbrev smallBlockDim {k1 k2 : ℕ} : smallBlockIndex k1 k2 → ℕ
  | .inl _ => 1
  | .inr _ => 2

def smallBlockDigit {k1 k2 : ℕ} (i : smallBlockIndex k1 k2) :
    Bool → Matrix (Fin (smallBlockDim i)) (Fin (smallBlockDim i)) ℤ :=
  match i with
  | .inl _ => fun _ => 0
  | .inr _ => mortalityExample

def smallBlockZero {k1 k2 : ℕ} : smallBlockIndex k1 k2 → List Bool
  | .inl _ => [false]
  | .inr _ => [true,false,false,true]

def smallBlockCost {k1 k2 : ℕ} : smallBlockIndex k1 k2 → ℕ
  | .inl _ => 1
  | .inr _ => 4

theorem smallBlock_local_finite {k1 k2 : ℕ} (i : smallBlockIndex k1 k2) :
    (Set.range (matrixWord (smallBlockDigit i))).Finite := by
  cases i with
  | inl j =>
    apply (Set.toFinite ({0,1} : Set (Matrix (Fin 1) (Fin 1) ℤ))).subset
    rintro X ⟨w,rfl⟩
    cases w with
    | nil => exact Set.mem_insert_of_mem 0 (Set.mem_singleton 1)
    | cons a w =>
      change 0 * matrixWord (smallBlockDigit (Sum.inl j)) w ∈ _
      rw [zero_mul]
      exact Set.mem_insert 0 _
  | inr j => exact mortalityExample_finite

theorem smallBlock_local_zero {k1 k2 : ℕ} (i : smallBlockIndex k1 k2) :
    matrixWord (smallBlockDigit i) (smallBlockZero i)=0 := by
  cases i with
  | inl j => simp [matrixWord,smallBlockDigit,smallBlockZero]
  | inr j => exact mortalityExample_zero

theorem smallBlock_local_lower {k1 k2 : ℕ} (i : smallBlockIndex k1 k2)
    (w : List Bool) (hw : matrixWord (smallBlockDigit i) w=0) : smallBlockCost i ≤ w.length := by
  cases i with
  | inl j =>
    cases w with
    | nil =>
      have he := congrFun (congrFun hw 0) 0
      exact False.elim (by norm_num [matrixWord] at he)
    | cons a w => simp [smallBlockCost]
  | inr j => exact mortalityExample_minimal w hw

theorem sharp_small_block_threshold (k1 k2 : ℕ) :
    Fintype.card (Σ i : smallBlockIndex k1 k2, Fin (smallBlockDim i))=k1+2*k2 ∧
    (Set.range (matrixWord (blockMortalityDigit smallBlockDim
      (@smallBlockDigit k1 k2)))).Finite ∧
    (∃ w, matrixWord (blockMortalityDigit smallBlockDim (@smallBlockDigit k1 k2)) w=0 ∧
      w.length=k1+4*k2) ∧
    (∀ w, matrixWord (blockMortalityDigit smallBlockDim (@smallBlockDigit k1 k2)) w=0 →
      k1+4*k2 ≤ w.length) := by
  refine ⟨?_,blockMortality_finite _ _ smallBlock_local_finite,?_,?_⟩
  · rw [Fintype.card_sigma]
    rw [Fintype.sum_sum_type]
    change (∑ _ : Fin k1, Fintype.card (Fin 1)) +
      (∑ _ : Fin k2, Fintype.card (Fin 2))=k1+2*k2
    simp [Nat.mul_comm]
  · obtain ⟨w,hw,hl⟩ := blockMortality_attains_sum smallBlockDim (@smallBlockDigit k1 k2)
      smallBlockZero smallBlock_local_zero
    exact ⟨w,hw,by simpa [Fintype.sum_sum_type,smallBlockZero,Nat.mul_comm] using hl⟩
  · intro w hw
    have hl := blockMortality_length_lower_bound smallBlockDim (@smallBlockDigit k1 k2)
      smallBlockCost smallBlock_local_lower w hw
    simpa [Fintype.sum_sum_type,smallBlockCost,Nat.mul_comm] using hl

theorem mortalityRotation_no_real_eigenvector (x : Fin 2 → ℝ) (t : ℝ)
    (h : (mortalityRotation.map (Int.castRingHom ℝ)).mulVec x=t • x) : x=0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [mortalityRotation,Matrix.mulVec,Fin.sum_univ_two] at h0 h1
  have hp : 0 < t*t+t+1 := by nlinarith [sq_nonneg (t+1/2)]
  have hz : (t*t+t+1)*x 1=0 := by nlinarith [h0,h1]
  have hx1 : x 1=0 := (mul_eq_zero.mp hz).resolve_left (ne_of_gt hp)
  have hx0 : x 0=0 := by simpa [hx1] using h1
  ext i
  fin_cases i <;> assumption

theorem mortalityRotation_irreducible (U : Submodule ℝ (Fin 2 → ℝ))
    (hU : ∀ x ∈ U, (mortalityRotation.map (Int.castRingHom ℝ)).mulVec x ∈ U) :
    U=⊥ ∨ U=⊤ := by
  have hd := U.finrank_le
  have hd2 : Module.finrank ℝ (Fin 2 → ℝ)=2 := by simp
  rw [hd2] at hd
  by_cases h0 : Module.finrank ℝ U=0
  · exact Or.inl (Submodule.finrank_eq_zero.mp h0)
  by_cases h2 : Module.finrank ℝ U=2
  · exact Or.inr (Submodule.eq_top_of_finrank_eq (h2.trans hd2.symm))
  have h1 : Module.finrank ℝ U=1 := by omega
  haveI : Nontrivial U := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank ℝ U)
  obtain ⟨x,hx⟩ := exists_ne (0 : U)
  obtain ⟨t,ht⟩ := exists_smul_eq_of_finrank_eq_one h1 hx
    (⟨(mortalityRotation.map (Int.castRingHom ℝ)).mulVec x,hU x x.property⟩ : U)
  have he : (mortalityRotation.map (Int.castRingHom ℝ)).mulVec x=t • (x : Fin 2 → ℝ) :=
    (congrArg Subtype.val ht).symm
  exact False.elim (hx (Subtype.ext (mortalityRotation_no_real_eigenvector x t he)))

end FiniteMonoidMortality
