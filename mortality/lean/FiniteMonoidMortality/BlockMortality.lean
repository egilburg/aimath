import FiniteMonoidMortality.FlagMortality
import FiniteMonoidMortality.MinimalRankCompression
import FiniteMonoidMortality.MortalityExtremizer
import Mathlib.Data.Matrix.Block

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace FiniteMonoidMortality

section Blocks

variable {I A R : Type*} [Fintype I] [DecidableEq I] [Semiring R]
    (d : I → ℕ) (M : ∀ i, A → Matrix (Fin (d i)) (Fin (d i)) R)

def blockMortalityDigit (a : I × A) : Matrix (Σ i, Fin (d i)) (Σ i, Fin (d i)) R :=
  Matrix.blockDiagonal' (fun i => if a.1=i then M i a.2 else 1)

def projectBlockWord (i : I) (w : List (I × A)) : List A :=
  w.filterMap (fun a => if a.1=i then some a.2 else none)

theorem blockMortality_word (w : List (I × A)) :
    matrixWord (blockMortalityDigit d M) w =
      Matrix.blockDiagonal' (fun i => matrixWord (M i) (projectBlockWord i w)) := by
  induction w with
  | nil =>
    change 1=Matrix.blockDiagonal' (1 : ∀ i, Matrix (Fin (d i)) (Fin (d i)) R)
    exact Matrix.blockDiagonal'_one.symm
  | cons a w ih =>
    change blockMortalityDigit d M a * matrixWord (blockMortalityDigit d M) w = _
    rw [ih]
    unfold blockMortalityDigit
    rw [← Matrix.blockDiagonal'_mul]
    congr 1
    funext i
    by_cases hi : a.1=i <;> simp [projectBlockWord,hi,matrixWord]

theorem blockMortality_zero_iff (w : List (I × A)) :
    matrixWord (blockMortalityDigit d M) w=0 ↔
      ∀ i, matrixWord (M i) (projectBlockWord i w)=0 := by
  rw [blockMortality_word]
  constructor
  · intro h i
    have he := Matrix.blockDiagonal'_injective (h.trans Matrix.blockDiagonal'_zero.symm)
    exact congrFun he i
  · intro h
    have he : (fun i => matrixWord (M i) (projectBlockWord i w))=0 := funext h
    rw [he,Matrix.blockDiagonal'_zero]

theorem blockMortality_finite
    (hf : ∀ i, (Set.range (matrixWord (M i))).Finite) :
    (Set.range (matrixWord (blockMortalityDigit d M))).Finite := by
  classical
  letI : ∀ i, Fintype (Set.range (matrixWord (M i))) := fun i => (hf i).fintype
  let f : (∀ i, Set.range (matrixWord (M i))) → Matrix (Σ i,Fin (d i)) (Σ i,Fin (d i)) R :=
    fun v => Matrix.blockDiagonal' (fun i => (v i).val)
  apply (Set.finite_range f).subset
  rintro _ ⟨w,rfl⟩
  refine ⟨fun i => ⟨matrixWord (M i) (projectBlockWord i w),⟨_,rfl⟩⟩,?_⟩
  exact (blockMortality_word d M w).symm

omit d M in

theorem projectBlockWord_lengths (w : List (I × A)) :
    (∑ i, (projectBlockWord i w).length)=w.length := by
  induction w with
  | nil => simp [projectBlockWord]
  | cons a w ih =>
    have he (i : I) : (projectBlockWord i (a::w)).length =
        (if a.1=i then 1 else 0)+(projectBlockWord i w).length := by
      by_cases hi : a.1=i <;> simp [projectBlockWord,hi,Nat.add_comm]
    simp_rw [he]
    rw [Finset.sum_add_distrib,ih]
    simp [Nat.add_comm]

theorem blockMortality_length_lower_bound (cost : I → ℕ)
    (hcost : ∀ i w, matrixWord (M i) w=0 → cost i ≤ w.length)
    (w : List (I × A)) (hw : matrixWord (blockMortalityDigit d M) w=0) :
    (∑ i,cost i) ≤ w.length := by
  have hi := (blockMortality_zero_iff d M w).mp hw
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hcost i _ (hi i))
  exact hh.trans_eq (projectBlockWord_lengths w)

omit d M in

theorem projectBlockWord_embed (i j : I) (w : List A) :
    projectBlockWord i (w.map (fun a => (j,a)))=if j=i then w else [] := by
  induction w with
  | nil => simp [projectBlockWord]
  | cons a w ih =>
    by_cases h : j=i <;> simp_all [projectBlockWord]

theorem blockMortality_attains_sum (ws : I → List A)
    (hws : ∀ i, matrixWord (M i) (ws i)=0) :
    ∃ w : List (I × A), matrixWord (blockMortalityDigit d M) w=0 ∧
      w.length=∑ i,(ws i).length := by
  classical
  let tagged := fun i => (ws i).map (fun a => (i,a))
  let w := (Finset.univ.toList.map tagged).flatten
  refine ⟨w,?_,?_⟩
  · apply (blockMortality_zero_iff d M w).mpr
    intro i
    have hp : ∀ L : List (List (I × A)),
        projectBlockWord i L.flatten=(L.map (projectBlockWord i)).flatten := by
      intro L
      induction L with
      | nil => simp [projectBlockWord]
      | cons l L ih => simpa [projectBlockWord] using congrArg (fun X => projectBlockWord i l++X) ih
    rw [show w=(Finset.univ.toList.map tagged).flatten from rfl,hp,matrixWord_flatten]
    have hz : (0 : Matrix (Fin (d i)) (Fin (d i)) R) ∈
        (((Finset.univ.toList.map tagged).map (projectBlockWord i)).map (matrixWord (M i))) := by
      simp only [List.mem_map]
      refine ⟨projectBlockWord i (tagged i),⟨tagged i,⟨i,by simp,rfl⟩,rfl⟩,?_⟩
      simp only [tagged,projectBlockWord_embed,if_pos rfl]
      exact hws i
    obtain ⟨l1,l2,he,_⟩ := List.eq_append_cons_of_mem hz
    rw [he]
    simp
  · simp [w,tagged,List.length_flatten,List.map_map,Function.comp_def]

end Blocks

end FiniteMonoidMortality
