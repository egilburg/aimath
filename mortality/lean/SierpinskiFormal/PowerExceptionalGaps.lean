import SierpinskiFormal.PowerIntervalDefs
import SierpinskiFormal.FiniteExceptionalGaps

set_option autoImplicit false

namespace IndependentZeroBlocks

open Filter
open scoped Topology

/-- Quantitative finite-gap extraction from power-sized host intervals.  The
constant in the conclusion records the factor two used to absorb the integer
rounding loss in `exists_clean_subinterval_real_bound`. -/
theorem exists_clean_subinterval_power_bound
    {ρ α : ℝ} {bad : ℕ → Prop} {c C : ℝ} {N₀ : ℕ}
    (hc : 0 < c) (hC : 0 ≤ C)
    (hbad : ∀ N : ℕ, N₀ ≤ N →
      (predicateCount bad N : ℝ) ≤ C * (N : ℝ) ^ α)
    (halpha : 0 ≤ α) (hgap : α < ρ) :
    ∃ cutoff : ℕ, ∀ a M : ℕ, cutoff ≤ a + M →
      c * ((a + M : ℕ) : ℝ) ^ ρ ≤ (M : ℝ) →
      ∃ n L : ℕ, a ≤ n ∧ n + L ≤ a + M ∧ 0 < L ∧
        c / (2 * (C + 1)) * ((a + M : ℕ) : ℝ) ^ (ρ - α) ≤ (L : ℝ) ∧
        ∀ j : ℕ, j < L → ¬bad (n + j) := by
  have hβ : 0 < ρ - α := sub_pos.mpr hgap
  have hCp : 0 < C + 1 := by linarith
  obtain ⟨R, hR⟩ :=
    exists_nat_rpow_gt (2 * (C + 1) / c) (ρ - α) hβ
  refine ⟨max R (max N₀ 1), ?_⟩
  intro a M hlate hhost
  let N := a + M
  have hRN : R ≤ N := by
    exact le_trans (le_max_left _ _) hlate
  have hN₀N : N₀ ≤ N := by
    exact le_trans (le_trans (le_max_left N₀ 1) (le_max_right R _)) hlate
  have h1N : 1 ≤ N := by
    exact le_trans (le_trans (le_max_right N₀ 1) (le_max_right R _)) hlate
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hNalpha_one : (1 : ℝ) ≤ (N : ℝ) ^ α := by
    exact Real.one_le_rpow (by exact_mod_cast h1N) halpha
  have hcount := hbad N hN₀N
  have hdenom_upper :
      (predicateCount bad N : ℝ) + 1 ≤ (C + 1) * (N : ℝ) ^ α := by
    nlinarith [mul_nonneg hC (Real.rpow_nonneg hNpos.le α)]
  have hdenom_pos : (0 : ℝ) < (predicateCount bad N : ℝ) + 1 := by positivity
  have hRcast : (R : ℝ) ≤ (N : ℝ) := by exact_mod_cast hRN
  have hlarge : 2 * (C + 1) / c < (N : ℝ) ^ (ρ - α) :=
    hR.trans_le (Real.rpow_le_rpow (by positivity) hRcast hβ.le)
  have hscaled_large :
      2 ≤ c / (C + 1) * (N : ℝ) ^ (ρ - α) := by
    have hmul : 2 * (C + 1) < c * (N : ℝ) ^ (ρ - α) := by
      have := (div_lt_iff₀ hc).mp hlarge
      nlinarith
    apply le_of_lt
    rw [div_mul_eq_mul_div]
    exact (lt_div_iff₀ hCp).2 hmul
  obtain ⟨n, L, han, hnright, hLlower, hclean⟩ :=
    exists_clean_subinterval_real_bound bad a M
  have hquot_lower :
      c / (C + 1) * (N : ℝ) ^ (ρ - α) ≤
        (M : ℝ) / ((predicateCount bad N : ℝ) + 1) := by
    have hNalpha_pos : 0 < (N : ℝ) ^ α := Real.rpow_pos_of_pos hNpos _
    have hCpow_pos : 0 < (C + 1) * (N : ℝ) ^ α := mul_pos hCp hNalpha_pos
    have hdiv_mono :
        (M : ℝ) / ((C + 1) * (N : ℝ) ^ α) ≤
          (M : ℝ) / ((predicateCount bad N : ℝ) + 1) := by
      exact div_le_div_of_nonneg_left (by positivity) hdenom_pos hdenom_upper
    calc
      c / (C + 1) * (N : ℝ) ^ (ρ - α) =
          (c * (N : ℝ) ^ ρ) / ((C + 1) * (N : ℝ) ^ α) := by
            rw [Real.rpow_sub hNpos]
            field_simp
      _ ≤ (M : ℝ) / ((C + 1) * (N : ℝ) ^ α) := by
        exact div_le_div_of_nonneg_right hhost hCpow_pos.le
      _ ≤ (M : ℝ) / ((predicateCount bad N : ℝ) + 1) := hdiv_mono
  have hhalf_lower :
      c / (2 * (C + 1)) * (N : ℝ) ^ (ρ - α) ≤ (L : ℝ) := by
    have hround :
        c / (C + 1) * (N : ℝ) ^ (ρ - α) - 1 < (L : ℝ) :=
      lt_of_le_of_lt (sub_le_sub_right hquot_lower 1) (by simpa [N] using hLlower)
    have hsplit :
        c / (2 * (C + 1)) * (N : ℝ) ^ (ρ - α) =
          (c / (C + 1) * (N : ℝ) ^ (ρ - α)) / 2 := by
      field_simp [ne_of_gt hCp]
    rw [hsplit]
    linarith
  refine ⟨n, L, han, hnright, ?_, ?_, hclean⟩
  · have hbound_pos :
        0 < c / (2 * (C + 1)) * (N : ℝ) ^ (ρ - α) := by positivity
    have : (0 : ℝ) < (L : ℝ) := lt_of_lt_of_le hbound_pos hhalf_lower
    exact_mod_cast this
  · simpa [N] using hhalf_lower

/-- Removing a set with counting exponent `α` from intervals of exponent `ρ`
leaves intervals of exponent `ρ - α`, whenever `α < ρ`. -/
theorem HasPowerIntervals.avoid_powerBound
    {ρ α : ℝ} {Z bad : ℕ → Prop}
    (hZ : HasPowerIntervals ρ Z)
    (hbad : HasPowerPredicateBound α bad)
    (halpha : 0 ≤ α) (hgap : α < ρ) :
    HasPowerIntervals (ρ - α) (fun n => Z n ∧ ¬bad n) := by
  obtain ⟨c, hc, hZc⟩ := hZ
  obtain ⟨C, hC, N₀, hbadC⟩ := hbad
  obtain ⟨cutoff, hcutoff⟩ :=
    exists_clean_subinterval_power_bound hc hC hbadC halpha hgap
  refine ⟨c / (2 * (C + 1)), by positivity, ?_⟩
  intro start
  obtain ⟨a, M, ha, hM, hhost, hZa⟩ := hZc (max start cutoff)
  have hlate : cutoff ≤ a + M :=
    le_trans (le_trans (le_max_right start cutoff) ha) (Nat.le_add_right a M)
  obtain ⟨n, L, han, hnright, hL, hhostpow, hclean⟩ :=
    hcutoff a M hlate hhost
  have hnL_host : n + L ≤ a + M := hnright
  have hendpoint_rpow :
      (((n + L : ℕ) : ℝ) ^ (ρ - α)) ≤
        (((a + M : ℕ) : ℝ) ^ (ρ - α)) := by
    apply Real.rpow_le_rpow
    · positivity
    · exact_mod_cast hnL_host
    · exact (sub_nonneg.mpr hgap.le)
  have hconstant_nonneg : 0 ≤ c / (2 * (C + 1)) := by positivity
  refine ⟨n, L, le_trans (le_trans (le_max_left start cutoff) ha) han,
    hL, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_left hendpoint_rpow hconstant_nonneg).trans hhostpow
  · intro j hj
    constructor
    · have hnj_right : n + j < a + M := by omega
      have hnj_left : a ≤ n + j := le_trans han (Nat.le_add_right n j)
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hnj_left
      rw [hk]
      apply hZa k
      omega
    · exact hclean j hj

/-- Proportional host intervals are the exponent-one specialization of the
power-gap theorem. -/
theorem HasProportionalIntervals.avoid_powerBound
    {α : ℝ} {Z bad : ℕ → Prop}
    (hZ : HasProportionalIntervals Z)
    (hbad : HasPowerPredicateBound α bad)
    (halpha : 0 ≤ α) (hgap : α < 1) :
    HasPowerIntervals (1 - α) (fun n => Z n ∧ ¬bad n) := by
  apply HasPowerIntervals.avoid_powerBound (ρ := 1) (α := α)
    (Z := Z) (bad := bad) ((hasPowerIntervals_one_iff Z).2 hZ) hbad halpha hgap

end IndependentZeroBlocks
