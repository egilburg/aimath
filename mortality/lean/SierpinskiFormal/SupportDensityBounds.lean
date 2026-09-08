import SierpinskiFormal.SupportDensityDefs
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

namespace IndependentZeroBlocks

open Filter
open scoped Topology

theorem supportCount_congr_below {K : Type*} [Semiring K]
    {F G : PowerSeries K} (N : ℕ)
    (h : ∀ n : ℕ, n < N → PowerSeries.coeff n F = PowerSeries.coeff n G) :
    supportCount F N = supportCount G N := by
  classical
  unfold supportCount
  congr 1
  ext n
  by_cases hn : n < N
  · simp only [Finset.mem_filter, Finset.mem_range, hn, true_and, h n hn]
  · simp [Finset.mem_filter, Finset.mem_range, hn]

private theorem supportCount_mono_bound {K : Type*} [Semiring K]
    (F : PowerSeries K) {M N : ℕ} (h : M ≤ N) :
    supportCount F M ≤ supportCount F N := by
  classical
  unfold supportCount
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
  exact ⟨lt_of_lt_of_le hn.1 h, hn.2⟩

/-- A lower counting estimate at every radix power gives an affine estimate
at every positive cutoff. -/
theorem supportCount_lower_bound_of_powers
    {K : Type*} [Semiring K] (F : PowerSeries K)
    (b : ℕ) (hb : 2 ≤ b) (k C B : ℝ)
    (hk : 0 ≤ k) (hC : 0 ≤ C)
    (hp : ∀ e : ℕ, k * (b ^ e : ℕ) ≤ C * (supportCount F (b ^ e) : ℝ) + B)
    (N : ℕ) (hN : 0 < N) :
    k * (N : ℝ) ≤ (b : ℝ) * C * (supportCount F N : ℝ) + (b : ℝ) * B := by
  let e := Nat.log b N
  have hpow : b ^ e ≤ N := Nat.pow_log_le_self b (by omega)
  have hnext : N < b * b ^ e := by
    simpa [e, pow_succ, Nat.mul_comm] using Nat.lt_pow_succ_log_self (by omega : 1 < b) N
  have hn : (N : ℝ) ≤ (b : ℝ) * (b ^ e : ℕ) := by exact_mod_cast hnext.le
  have hc : (supportCount F (b ^ e) : ℝ) ≤ (supportCount F N : ℝ) := by
    exact_mod_cast supportCount_mono_bound F hpow
  have hp' := hp e
  have hbc : 0 ≤ (b : ℝ) := Nat.cast_nonneg b
  calc
    k * (N : ℝ) ≤ k * ((b : ℝ) * (b ^ e : ℕ)) := mul_le_mul_of_nonneg_left hn hk
    _ = (b : ℝ) * (k * (b ^ e : ℕ)) := by ring
    _ ≤ (b : ℝ) * (C * (supportCount F (b ^ e) : ℝ) + B) :=
      mul_le_mul_of_nonneg_left hp' hbc
    _ ≤ (b : ℝ) * (C * (supportCount F N : ℝ) + B) := by
      gcongr
    _ = (b : ℝ) * C * (supportCount F N : ℝ) + (b : ℝ) * B := by ring

/-- The precise lower-limit bound is stated without assuming that a density
exists. -/
theorem supportDensity_eventually_lower_of_powers
    {K : Type*} [Semiring K] (F : PowerSeries K)
    (b : ℕ) (hb : 2 ≤ b) (k C B : ℝ)
    (hk : 0 ≤ k) (hC : 0 < C)
    (hp : ∀ e : ℕ, k * (b ^ e : ℕ) ≤ C * (supportCount F (b ^ e) : ℝ) + B) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      k / ((b : ℝ) * C) - ε ≤ (supportCount F N : ℝ) / (N : ℝ) := by
  intro ε hε
  have ht : Tendsto (fun N : ℕ => (B / C) / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (B / C)
  have he : ∀ᶠ N : ℕ in atTop, (B / C) / (N : ℝ) < ε :=
    ht.eventually (gt_mem_nhds hε)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 he
  refine ⟨max N₀ 1, ?_⟩
  intro N hN
  have hn : 0 < N := by omega
  have hnR : (0 : ℝ) < N := by exact_mod_cast hn
  have hbR : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have ha := supportCount_lower_bound_of_powers F b hb k C B hk hC.le hp N hn
  have heN := hN₀ N (by omega)
  have hr : k / ((b : ℝ) * C) - (B / C) / (N : ℝ) ≤
      (supportCount F N : ℝ) / (N : ℝ) := by
    apply (le_div_iff₀ hnR).2
    have heq : (k / ((b : ℝ) * C) - (B / C) / (N : ℝ)) * (N : ℝ) =
        (k * (N : ℝ) - (b : ℝ) * B) / ((b : ℝ) * C) := by
      field_simp [ne_of_gt hbR, ne_of_gt hC, ne_of_gt hnR]
    rw [heq]
    apply (div_le_iff₀ (mul_pos hbR hC)).2
    nlinarith
  linarith

theorem hasPositiveLowerSupportDensity_of_powers
    {K : Type*} [Semiring K] (F : PowerSeries K)
    (b : ℕ) (hb : 2 ≤ b) (k C B : ℝ)
    (hk : 0 < k) (hC : 0 < C)
    (hp : ∀ e : ℕ, k * (b ^ e : ℕ) ≤ C * (supportCount F (b ^ e) : ℝ) + B) :
    HasPositiveLowerSupportDensity F := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  let c := k / ((b : ℝ) * C) / 2
  have hc : 0 < c := div_pos (div_pos hk (mul_pos hbR hC)) (by norm_num)
  obtain ⟨N₀, hN₀⟩ := supportDensity_eventually_lower_of_powers F b hb k C B hk.le hC hp c hc
  refine ⟨c, hc, max N₀ 1, ?_⟩
  intro N hN
  have hnR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h := hN₀ N (by omega)
  have heq : k / ((b : ℝ) * C) - c = c := by dsimp [c]; ring
  rw [heq] at h
  exact (le_div_iff₀ hnR).1 h

theorem HasPositiveLowerSupportDensity.not_zero
    {K : Type*} [Semiring K] {F : PowerSeries K}
    (h : HasPositiveLowerSupportDensity F) : ¬ HasZeroSupportDensity F := by
  obtain ⟨c, hc, N₀, hN₀⟩ := h
  intro hz
  have he : ∀ᶠ N : ℕ in atTop, (supportCount F N : ℝ) / (N : ℝ) < c :=
    hz.eventually (gt_mem_nhds hc)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 he
  let N := max (max N₀ N₁) 1
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by dsimp [N]; omega)
  have hlow := hN₀ N (by dsimp [N]; omega)
  have hhigh := hN₁ N (by dsimp [N]; omega)
  have hlow' : c ≤ (supportCount F N : ℝ) / (N : ℝ) := (le_div_iff₀ hn).2 hlow
  linarith

end IndependentZeroBlocks
