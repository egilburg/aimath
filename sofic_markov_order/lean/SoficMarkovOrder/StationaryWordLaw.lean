import SoficMarkovOrder.HankelRankCriterion
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false

namespace SoficMarkovOrder
open scoped BigOperators

variable {A : Type*} [Fintype A]

/-- Nonnegative normalized stationary cylinder weights on finite words. -/
structure StationaryWordLaw (A : Type*) [Fintype A] where
  mass : List A → ℝ
  nonneg : ∀ w, 0 ≤ mass w
  mass_nil : mass [] = 1
  sum_append : ∀ w, ∑ a, mass (w ++ [a]) = mass w
  sum_prepend : ∀ w, ∑ a, mass (a :: w) = mass w

namespace StationaryWordLaw

theorem append_singleton_le (L : StationaryWordLaw A) (w : List A) (a : A) :
    L.mass (w ++ [a]) ≤ L.mass w := by
  classical
  rw [← L.sum_append w]
  exact Finset.single_le_sum (fun b _ => L.nonneg (w ++ [b])) (Finset.mem_univ a)

theorem cons_le (L : StationaryWordLaw A) (w : List A) (a : A) :
    L.mass (a :: w) ≤ L.mass w := by
  classical
  rw [← L.sum_prepend w]
  exact Finset.single_le_sum (fun b _ => L.nonneg (b :: w)) (Finset.mem_univ a)

theorem append_le (L : StationaryWordLaw A) (u v : List A) :
    L.mass (u ++ v) ≤ L.mass u := by
  induction v using List.reverseRecOn with
  | nil => simp
  | append_singleton v a ih =>
      rw [← List.append_assoc]
      exact (L.append_singleton_le (u ++ v) a).trans ih

theorem prepend_le (L : StationaryWordLaw A) (u v : List A) :
    L.mass (u ++ v) ≤ L.mass v := by
  induction u with
  | nil => simp
  | cons a u ih => exact (L.cons_le (u ++ v) a).trans ih

theorem context_le (L : StationaryWordLaw A) (u v z : List A) :
    L.mass (u ++ v ++ z) ≤ L.mass v :=
  (L.append_le (u ++ v) z).trans (L.prepend_le u v)

theorem forbidden_context (L : StationaryWordLaw A) (v : List A)
    (hv : L.mass v = 0) (u z : List A) : L.mass (u ++ v ++ z) = 0 :=
  le_antisymm (hv ▸ L.context_le u v z) (L.nonneg _)

/-- Conditional finite-future probabilities after any positive-mass history
depend only on its last `k` symbols. Zero-mass histories impose no condition. -/
def ConditionalMarkov (L : StationaryWordLaw A) (k : ℕ) : Prop :=
  ∀ u v z : List A, v.length = k → 0 < L.mass (u ++ v) →
    L.mass (u ++ v ++ z) / L.mass (u ++ v) = L.mass (v ++ z) / L.mass v

theorem conditionalMarkov_iff_contextMarkov (L : StationaryWordLaw A) (k : ℕ) :
    L.ConditionalMarkov k ↔ ContextMarkov L.mass k := by
  constructor
  · intro h u v z hv
    by_cases hp : 0 < L.mass (u ++ v)
    · have hvp : 0 < L.mass v := hp.trans_le (L.prepend_le u v)
      have he := (div_eq_div_iff hp.ne' hvp.ne').mp (h u v z hv hp)
      simpa only [mul_comm] using he
    · have hzero : L.mass (u ++ v) = 0 :=
        le_antisymm (le_of_not_gt hp) (L.nonneg _)
      have hext : L.mass (u ++ v ++ z) = 0 :=
        le_antisymm (hzero ▸ L.append_le (u ++ v) z) (L.nonneg _)
      simp only [hzero, hext, zero_mul]
  · intro h u v z hv hp
    have hvp : 0 < L.mass v := hp.trans_le (L.prepend_le u v)
    apply (div_eq_div_iff hp.ne' hvp.ne').mpr
    simpa only [mul_comm] using h u v z hv

theorem conditionalMarkov_iff_rankOne
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (L : StationaryWordLaw A) (T : A → Module.End ℝ V) (l : Module.Dual ℝ V) (g : V)
    (hrep : L.mass = representedWord T l g) (hr : WordReduced T l g) (k : ℕ) :
    L.ConditionalMarkov k ↔
      ∀ v : List A, v.length = k → Module.finrank ℝ (linearWord T v).range ≤ 1 := by
  rw [L.conditionalMarkov_iff_contextMarkov, hrep]
  exact contextMarkov_iff_rankOne hr (by simpa only [← hrep] using L.forbidden_context) k

theorem conditionalMarkov_cutoff_hankel
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (L : StationaryWordLaw A) (T : A → Module.End ℝ V) (l : Module.Dual ℝ V) (g : V)
    (hrep : L.mass = representedWord T l g) (hr : WordReduced T l g)
    (hfinite : ∃ k, L.ConditionalMarkov k) :
    L.ConditionalMarkov ((Module.finrank ℝ (wordHankelSpan L.mass)).choose 2) := by
  rw [hrep, hr.finrank_wordHankelSpan]
  apply (L.conditionalMarkov_iff_rankOne T l g hrep hr _).mpr
  apply eventual_rankOne_cutoff_choose_two
  obtain ⟨k, hk⟩ := hfinite
  exact ⟨k, (L.conditionalMarkov_iff_rankOne T l g hrep hr k).mp hk⟩

end StationaryWordLaw
end SoficMarkovOrder
