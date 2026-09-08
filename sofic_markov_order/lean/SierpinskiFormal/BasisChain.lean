import SierpinskiFormal.UniformNilpotence
import Mathlib.Data.List.OfFn

set_option autoImplicit false

namespace IndependentZeroBlocks

variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W] {D : ℕ}

/-- Consecutive matrix units in a chosen ordered basis. -/
noncomputable def basisChain (b : Module.Basis (Fin D) K W) (s : Fin (D - 1)) :
    Module.End K W :=
  (b.coord ⟨s.val + 1, by omega⟩).smulRight (b ⟨s.val, by omega⟩)

theorem basisChain_apply_basis (b : Module.Basis (Fin D) K W)
    (s : Fin (D - 1)) (j : Fin D) :
    basisChain b s (b j) =
      if j.val = s.val + 1 then b ⟨s.val, by omega⟩ else 0 := by
  classical
  simp [basisChain, Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_apply, Fin.ext_iff]

/-- Every generator lowers the only possibly surviving basis index by one. -/
theorem basisChain_word_basis_zero (b : Module.Basis (Fin D) K W)
    (w : List (Fin (D - 1))) (j : Fin D) (hj : j.val < w.length) :
    linearWord (basisChain b) w (b j) = 0 := by
  induction w using List.reverseRecOn generalizing j with
  | nil => simp at hj
  | append_singleton w s ih =>
      rw [linearWord_append, Module.End.mul_apply]
      have hs : linearWord (basisChain b) [s] = basisChain b s := by simp [linearWord]
      rw [hs, basisChain_apply_basis]
      split_ifs with heq
      · apply ih ⟨s.val, by omega⟩
        change s.val < w.length
        simp only [List.length_append, List.length_singleton] at hj
        omega
      · exact map_zero _

theorem basisChain_word_zero (b : Module.Basis (Fin D) K W)
    (w : List (Fin (D - 1))) (hw : w.length = D) :
    linearWord (basisChain b) w = 0 := by
  apply b.ext
  intro j
  exact basisChain_word_basis_zero b w j (by rw [hw]; exact j.isLt)

/-- The initial segment of the consecutive chain, written in product order. -/
def basisChainWord (m : ℕ) (hm : m ≤ D - 1) : List (Fin (D - 1)) :=
  List.ofFn fun i : Fin m => ⟨i.val, by omega⟩

@[simp] theorem basisChainWord_length (m : ℕ) (hm : m ≤ D - 1) :
    (basisChainWord m hm).length = m := List.length_ofFn

theorem basisChainWord_succ (m : ℕ) (hm : m + 1 ≤ D - 1) :
    basisChainWord (m + 1) hm =
      basisChainWord m (by omega) ++ [⟨m, by omega⟩] := by
  unfold basisChainWord
  rw [List.ofFn_succ_last]
  rfl

/-- The chain of length D-1 survives on the last basis vector. -/
theorem basisChainWord_apply (b : Module.Basis (Fin D) K W) (hD : 0 < D)
    (m : ℕ) (hm : m ≤ D - 1) :
    linearWord (basisChain b) (basisChainWord m hm) (b ⟨m, by omega⟩) = b ⟨0, hD⟩ := by
  induction m with
  | zero => simp [basisChainWord]
  | succ m ih =>
      rw [basisChainWord_succ, linearWord_append, Module.End.mul_apply]
      have hs : linearWord (basisChain b) [⟨m, by omega⟩] = basisChain b ⟨m, by omega⟩ :=
        by simp [linearWord]
      rw [hs, basisChain_apply_basis, if_pos rfl]
      exact ih (by omega)

theorem basisChain_critical_nonzero (b : Module.Basis (Fin D) K W) (hD : 0 < D) :
    linearWord (basisChain b) (basisChainWord (D - 1) le_rfl) ≠ 0 := by
  intro h
  have he := basisChainWord_apply b hD (D - 1) le_rfl
  rw [h, LinearMap.zero_apply] at he
  exact b.ne_zero ⟨0, hD⟩ he.symm

end IndependentZeroBlocks
