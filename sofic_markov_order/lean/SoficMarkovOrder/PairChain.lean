import SoficMarkovOrder.ExteriorPairs
import SoficMarkovOrder.BasisChain

/-!
# Pair-chain core of the sharp examples

For lexicographically ordered pairs the numerical rank-two letters are the
pair-chain construction of A. N. Trahtman (1998), Section 6, expressed here
in column-action convention. The deterministic binomial-delay precedent is
due to M.-P. Beal and J. Senellart (1998). The manuscript gives the precise
comparison and bibliography; no originality is claimed for this core.
-/

set_option autoImplicit false

namespace SoficMarkovOrder

variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]
  [LinearOrder I] [FiniteDimensional K V] {D : ℕ}

noncomputable def pairChain (b : Module.Basis I K V)
    (e : Fin D ≃ Set.powersetCard I 2) (s : Fin (D - 1)) : Module.End K V :=
  pairTransition b (e ⟨s.val, by omega⟩) (e ⟨s.val + 1, by omega⟩)

theorem exterior_pairChain (b : Module.Basis I K V)
    (e : Fin D ≃ Set.powersetCard I 2) (s : Fin (D - 1)) :
    exteriorPower.map 2 (pairChain b e s) =
      basisChain ((b.exteriorPower 2).reindex e.symm) s := by
  rw [pairChain, exterior_pairTransition]
  unfold basisChain
  congr 1
  · ext x
    simp [Module.Basis.coord_apply, Module.Basis.repr_reindex_apply]

theorem pairChain_rankOne_at_cutoff (b : Module.Basis I K V)
    (e : Fin D ≃ Set.powersetCard I 2) (w : List (Fin (D - 1)))
    (hw : w.length = D) : Module.finrank K (linearWord (pairChain b e) w).range ≤ 1 := by
  apply (exteriorSquare_zero_iff_rank_le_one _).mp
  rw [← linearWord_exteriorPower]
  have he : (fun s => exteriorPower.map 2 (pairChain b e s)) =
      basisChain ((b.exteriorPower 2).reindex e.symm) :=
    funext (exterior_pairChain b e)
  rw [he]
  exact basisChain_word_zero _ w hw

theorem pairChain_critical_rank (b : Module.Basis I K V)
    (e : Fin D ≃ Set.powersetCard I 2) (hD : 0 < D) :
    ¬Module.finrank K
      (linearWord (pairChain b e) (basisChainWord (D - 1) le_rfl)).range ≤ 1 := by
  intro h
  have hz := (exteriorSquare_zero_iff_rank_le_one _).mpr h
  rw [← linearWord_exteriorPower] at hz
  have he : (fun s => exteriorPower.map 2 (pairChain b e s)) =
      basisChain ((b.exteriorPower 2).reindex e.symm) :=
    funext (exterior_pairChain b e)
  rw [he] at hz
  exact basisChain_critical_nonzero _ hD hz

omit [LinearOrder I] [FiniteDimensional K V] in
theorem linearWord_uniform_smul {A : Type*} (T : A → Module.End K V)
    (c : K) (w : List A) :
    linearWord (fun a => c • T a) w = c ^ w.length • linearWord T w := by
  induction w with
  | nil => simp
  | cons a w ih =>
      rw [linearWord_cons, linearWord_cons, ih]
      simp only [List.length_cons, smul_mul_assoc, mul_smul_comm, smul_smul]
      rw [pow_succ', mul_comm (c ^ w.length) c]

omit [LinearOrder I] [FiniteDimensional K V] in
theorem linearWord_uniform_smul_range {A : Type*} (T : A → Module.End K V)
    (c : K) (hc : c ≠ 0) (w : List A) :
    (linearWord (fun a => c • T a) w).range = (linearWord T w).range := by
  rw [linearWord_uniform_smul]
  exact LinearMap.range_smul _ _ (pow_ne_zero _ hc)

end SoficMarkovOrder
