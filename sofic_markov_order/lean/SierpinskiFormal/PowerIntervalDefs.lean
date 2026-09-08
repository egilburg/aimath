import SierpinskiFormal.SparseIntervalDefs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

namespace IndependentZeroBlocks

/-- Positive real powers of natural numbers are unbounded.  This local form
avoids imposing any continuity or asymptotic API on downstream statements. -/
lemma exists_nat_rpow_gt (K β : ℝ) (hβ : 0 < β) :
    ∃ R : ℕ, K < (R : ℝ) ^ β := by
  have hbase : (1 : ℝ) < (2 : ℝ) ^ β :=
    Real.one_lt_rpow (by norm_num) hβ
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt K hbase
  refine ⟨2 ^ m, ?_⟩
  calc
    K < ((2 : ℝ) ^ β) ^ m := hm
    _ = ((2 : ℝ) ^ m) ^ β := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      rw [mul_comm]
      rw [Real.rpow_mul (by positivity), Real.rpow_natCast]
    _ = ((2 ^ m : ℕ) : ℝ) ^ β := by norm_num

/-- Arbitrarily late intervals on which `Z` holds, with length bounded below
by a fixed positive multiple of a real power of the right endpoint. -/
def HasPowerIntervals (ρ : ℝ) (Z : ℕ → Prop) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ start : ℕ, ∃ a length : ℕ,
    start ≤ a ∧ 0 < length ∧
      c * ((a + length : ℕ) : ℝ) ^ ρ ≤ (length : ℝ) ∧
      ∀ j : ℕ, j < length → Z (a + j)

/-- An eventual power upper bound for the counting function of a predicate. -/
def HasPowerPredicateBound (α : ℝ) (bad : ℕ → Prop) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    (predicateCount bad N : ℝ) ≤ C * (N : ℝ) ^ α

/-- Proportional intervals are exactly power intervals of exponent one. -/
theorem hasPowerIntervals_one_iff (Z : ℕ → Prop) :
    HasPowerIntervals 1 Z ↔ HasProportionalIntervals Z := by
  simp only [HasPowerIntervals, HasProportionalIntervals, Real.rpow_one]

/-- Every positive power interval hypothesis implies the earlier qualitative
conclusion of arbitrarily late intervals of every prescribed finite length. -/
theorem HasPowerIntervals.arbitrarilyLongIntervals
    {ρ : ℝ} {Z : ℕ → Prop} (hZ : HasPowerIntervals ρ Z) (hρ : 0 < ρ) :
    ∀ length start : ℕ, ∃ N : ℕ, start ≤ N ∧
      ∀ j : ℕ, j < length → Z (N + j) := by
  obtain ⟨c, hc, hinterval⟩ := hZ
  intro length start
  obtain ⟨R, hR⟩ := exists_nat_rpow_gt ((length : ℝ) / c) ρ hρ
  obtain ⟨a, M, ha, hM, hpower, hZa⟩ := hinterval (max start R)
  have hRa : R ≤ a := le_trans (le_max_right start R) ha
  have hRendpoint : R ≤ a + M := le_trans hRa (Nat.le_add_right a M)
  have hlength_real : (length : ℝ) ≤ (M : ℝ) := by
    have hcast : (R : ℝ) ≤ ((a + M : ℕ) : ℝ) := by exact_mod_cast hRendpoint
    have hlarge : (length : ℝ) / c < ((a + M : ℕ) : ℝ) ^ ρ :=
      hR.trans_le (Real.rpow_le_rpow (by positivity) hcast hρ.le)
    have : (length : ℝ) < c * ((a + M : ℕ) : ℝ) ^ ρ := by
      simpa [mul_comm] using (div_lt_iff₀ hc).mp hlarge
    exact le_trans this.le hpower
  have hlength : length ≤ M := by exact_mod_cast hlength_real
  refine ⟨a, le_trans (le_max_left start R) ha, ?_⟩
  intro j hj
  exact hZa j (lt_of_lt_of_le hj hlength)

end IndependentZeroBlocks
