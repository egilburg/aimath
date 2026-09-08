import SierpinskiFormal.PowerSupportFamilies

set_option autoImplicit false

namespace IndependentZeroBlocks

/-- Sublinear power growth of an exceptional counting function implies
ordinary density zero. No lower bound on the exponent is required. -/
theorem HasPowerPredicateBound.toZeroPredicateDensity
    {bad : ℕ → Prop} {α : ℝ} (h : HasPowerPredicateBound α bad)
    (hα : α < 1) : HasZeroPredicateDensity bad := by
  obtain ⟨C, hC, N₀, hcount⟩ := h
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨R, hR⟩ := exists_nat_rpow_gt (C / ε) (1 - α) (by linarith)
  refine ⟨max N₀ (max R 1), ?_⟩
  intro N hN
  have hN₀ : N₀ ≤ N := (le_max_left _ _).trans hN
  have hRN : R ≤ N := (le_max_left R 1).trans ((le_max_right _ _).trans hN)
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast (show 0 < N by omega)
  have hlarge : C / ε < (N : ℝ) ^ (1 - α) :=
    hR.trans_le (Real.rpow_le_rpow (by positivity)
      (by exact_mod_cast hRN) (by linarith))
  have hClt : C < ε * (N : ℝ) ^ (1 - α) := by
    simpa [mul_comm] using (div_lt_iff₀ hε).mp hlarge
  have hprod : (N : ℝ) ^ (1 - α) * (N : ℝ) ^ α = N := by
    rw [← Real.rpow_add hNpos]
    simp
  have hupper : (predicateCount bad N : ℝ) < ε * N := by
    calc
      (predicateCount bad N : ℝ) ≤ C * (N : ℝ) ^ α := hcount N hN₀
      _ < (ε * (N : ℝ) ^ (1 - α)) * (N : ℝ) ^ α :=
        mul_lt_mul_of_pos_right hClt (Real.rpow_pos_of_pos hNpos α)
      _ = ε * N := by rw [mul_assoc, hprod]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
  exact (div_lt_iff₀ hNpos).mpr hupper

/-- The predicate and series formulations count the same coefficient support. -/
theorem zeroPredicateDensity_support_iff
    {K : Type*} [Semiring K] (F : PowerSeries K) :
    HasZeroPredicateDensity (fun n => PowerSeries.coeff n F ≠ 0) ↔
      HasZeroSupportDensity F := by
  classical
  have heq (N : ℕ) :
      predicateCount (fun n => PowerSeries.coeff n F ≠ 0) N = supportCount F N := by
    unfold predicateCount supportCount
    congr
  simp only [HasZeroPredicateDensity, HasZeroSupportDensity, heq]

end IndependentZeroBlocks
