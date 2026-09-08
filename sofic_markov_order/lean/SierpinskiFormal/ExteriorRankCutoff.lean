import SierpinskiFormal.UniformNilpotence
import Mathlib.LinearAlgebra.ExteriorPower.Basis

set_option autoImplicit false

/-!
# Exterior rank detection and universal rank cutoff

This algebraic layer proves a binomial cutoff for eventual universal rank
collapse. It does not by itself assert a probabilistic Markov-order theorem.
-/

namespace IndependentZeroBlocks

open exteriorPower

variable {K V A : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- Exterior powers preserve the dimension of the image by the binomial rule. -/
theorem finrank_range_exteriorPower_map (r : ℕ) (f : Module.End K V) :
    Module.finrank K (LinearMap.range (exteriorPower.map r f)) =
      (Module.finrank K (LinearMap.range f)).choose r := by
  have hfac : f.range.subtype.comp f.rangeRestrict = f := by ext x; rfl
  have hsurj := exteriorPower.map_surjective (n := r) f.surjective_rangeRestrict
  have hinj := exteriorPower.map_injective_field (n := r) (Submodule.subtype_injective f.range)
  rw [← hfac, exteriorPower.map_comp,
    LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hsurj),
    LinearMap.finrank_range_of_inj hinj, exteriorPower.finrank_eq]
  rw [hfac]

/-- The exterior square vanishes exactly when the original map has rank at most one. -/
theorem exteriorSquare_zero_iff_rank_le_one (f : Module.End K V) :
    exteriorPower.map 2 f = 0 ↔ Module.finrank K f.range ≤ 1 := by
  rw [← LinearMap.range_eq_bot, ← Submodule.finrank_eq_zero,
    finrank_range_exteriorPower_map, Nat.choose_eq_zero_iff]
  omega

omit [FiniteDimensional K V] in
/-- Exterior powers commute with the project's existing word-product convention. -/
theorem linearWord_exteriorPower (T : A → Module.End K V) (r : ℕ) (w : List A) :
    linearWord (fun a => exteriorPower.map r (T a)) w =
      exteriorPower.map r (linearWord T w) := by
  induction w with
  | nil => exact (exteriorPower.map_id (n := r)).symm
  | cons a w ih =>
      rw [linearWord_cons, linearWord_cons, ih]
      exact (exteriorPower.map_comp (n := r) (linearWord T w) (T a)).symm

/-- Universal rank at most one, if eventually attained, is attained by `choose(n,2)`. -/
theorem eventual_rankOne_cutoff_choose_two (T : A → Module.End K V)
    (heventual : ∃ N : ℕ, ∀ w : List A, w.length = N →
      Module.finrank K (linearWord T w).range ≤ 1) :
    ∀ w : List A, w.length = (Module.finrank K V).choose 2 →
      Module.finrank K (linearWord T w).range ≤ 1 := by
  have hnil : ∃ N : ℕ, ∀ w : List A, w.length = N →
      linearWord (fun a => exteriorPower.map 2 (T a)) w = 0 := by
    obtain ⟨N, hN⟩ := heventual
    refine ⟨N, fun w hw => ?_⟩
    rw [linearWord_exteriorPower]
    exact (exteriorSquare_zero_iff_rank_le_one _).mpr (hN w hw)
  intro w hw
  apply (exteriorSquare_zero_iff_rank_le_one _).mp
  rw [← linearWord_exteriorPower]
  exact uniformNilpotence_cutoff_finrank _ hnil w
    (by simpa only [exteriorPower.finrank_eq] using hw)

end IndependentZeroBlocks
