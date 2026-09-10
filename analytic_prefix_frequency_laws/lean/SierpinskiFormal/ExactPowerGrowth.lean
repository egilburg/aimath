import SierpinskiFormal.DigitSupportGrowth
import SierpinskiFormal.PowerSupportFamilies

set_option autoImplicit false

/-!
# Two-sided power growth from exact radix counts

This module interpolates exact support counts along a shifted sequence of
radix powers to all sufficiently large cutoffs.
-/

namespace IndependentZeroBlocks

/-- The coefficient support has two-sided power growth with positive
constants from some cutoff onward. -/
def HasPowerSupportGrowth {K : Type*} [Semiring K]
    (F : PowerSeries K) (α : ℝ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    c * (N : ℝ) ^ α ≤ (supportCount F N : ℝ) ∧
      (supportCount F N : ℝ) ≤ C * (N : ℝ) ^ α

/-- A series with positive two-sided power support growth is nonzero. -/
theorem HasPowerSupportGrowth.ne_zero
    {K : Type*} [Semiring K] {F : PowerSeries K} {α : ℝ}
    (h : HasPowerSupportGrowth F α) : F ≠ 0 := by
  rintro rfl
  obtain ⟨c, C, hc, hC, N₀, hgrowth⟩ := h
  let N := max N₀ 1
  have hN₀ : N₀ ≤ N := le_max_left _ _
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 0 < N by simp [N])
  have hlower := (hgrowth N hN₀).1
  have hleft : 0 < c * (N : ℝ) ^ α :=
    mul_pos hc (Real.rpow_pos_of_pos hNpos α)
  have hcount_zero : supportCount (0 : PowerSeries K) N = 0 := by
    simp [supportCount]
  rw [hcount_zero, Nat.cast_zero] at hlower
  linarith

/-- Two different support-growth exponents cannot be strictly ordered. -/
theorem HasPowerSupportGrowth.not_lt_exponent
    {K : Type*} [Semiring K] {F : PowerSeries K} {α β : ℝ}
    (hαgrowth : HasPowerSupportGrowth F α)
    (hβgrowth : HasPowerSupportGrowth F β) : ¬α < β := by
  intro hαβ
  obtain ⟨cα, Cα, hcα, hCα, Nα, hα⟩ := hαgrowth
  obtain ⟨cβ, Cβ, hcβ, hCβ, Nβ, hβ⟩ := hβgrowth
  have hdiff : 0 < β - α := sub_pos.mpr hαβ
  obtain ⟨R, hR⟩ := exists_nat_rpow_gt (Cα / cβ) (β - α) hdiff
  let N := max R (max Nα (max Nβ 1))
  have hRN : R ≤ N := le_max_left _ _
  have hNα : Nα ≤ N :=
    le_trans (le_max_left Nα (max Nβ 1)) (le_max_right R _)
  have hNβ : Nβ ≤ N :=
    le_trans (le_trans (le_max_left Nβ 1) (le_max_right Nα _))
      (le_max_right R _)
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 0 < N by
      exact lt_of_lt_of_le (by simp : 0 < 1)
        (le_trans (le_max_right Nβ 1)
          (le_trans (le_max_right Nα _) (le_max_right R _))))
  have hRcast : (R : ℝ) ≤ (N : ℝ) := by exact_mod_cast hRN
  have hlarge : Cα / cβ < (N : ℝ) ^ (β - α) :=
    hR.trans_le (Real.rpow_le_rpow (by positivity) hRcast hdiff.le)
  have hcoeff : Cα < cβ * (N : ℝ) ^ (β - α) := by
    simpa [mul_comm] using (div_lt_iff₀ hcβ).mp hlarge
  have hNαpow : 0 < (N : ℝ) ^ α := Real.rpow_pos_of_pos hNpos α
  have hstrict :
      Cα * (N : ℝ) ^ α < cβ * (N : ℝ) ^ β := by
    have hmul := mul_lt_mul_of_pos_right hcoeff hNαpow
    calc
      Cα * (N : ℝ) ^ α <
          (cβ * (N : ℝ) ^ (β - α)) * (N : ℝ) ^ α := hmul
      _ = cβ * (N : ℝ) ^ β := by
        rw [show β = (β - α) + α by ring, Real.rpow_add hNpos]
        ring_nf
  have hlower := (hβ N hNβ).1
  have hupper := (hα N hNα).2
  linarith

/-- The exponent in a two-sided power support-growth estimate is unique. -/
theorem HasPowerSupportGrowth.exponent_eq
    {K : Type*} [Semiring K] {F : PowerSeries K} {α β : ℝ}
    (hα : HasPowerSupportGrowth F α)
    (hβ : HasPowerSupportGrowth F β) : α = β := by
  exact le_antisymm
    (not_lt.mp (hβ.not_lt_exponent hα))
    (not_lt.mp (hα.not_lt_exponent hβ))

private lemma cast_radix_pow_rpow
    (b s e : ℕ) (α : ℝ) (hscale : (b : ℝ) ^ α = (s : ℝ)) :
    (((b ^ e : ℕ) : ℝ) ^ α) = (s : ℝ) ^ e := by
  calc
    (((b ^ e : ℕ) : ℝ) ^ α) = ((b : ℝ) ^ e) ^ α := by norm_num
    _ = ((b : ℝ) ^ α) ^ e := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      rw [mul_comm]
      rw [Real.rpow_mul (by positivity), Real.rpow_natCast]
    _ = (s : ℝ) ^ e := by rw [hscale]

/-- Exact support counts at the shifted radix cutoffs `b^(E+n)` imply
two-sided power growth at every sufficiently large cutoff. -/
theorem hasPowerSupportGrowth_of_shifted_radix_counts
    {K : Type*} [Semiring K] (F : PowerSeries K)
    (b s t E : ℕ) (hb : 2 ≤ b) (hs : 1 ≤ s) (ht : 1 ≤ t)
    (α : ℝ) (hα : 0 ≤ α) (hscale : (b : ℝ) ^ α = (s : ℝ))
    (hexact : ∀ n : ℕ,
      supportCount F (b ^ (E + n)) = t * s ^ n) :
    HasPowerSupportGrowth F α := by
  let c : ℝ := (t : ℝ) / (s : ℝ) ^ (E + 1)
  let C : ℝ := (t : ℝ) * (s : ℝ)
  have hspos : (0 : ℝ) < (s : ℝ) := by positivity
  have htpos : (0 : ℝ) < (t : ℝ) := by positivity
  refine ⟨c, C, by simp only [c]; positivity, by simp only [C]; positivity,
    b ^ E, ?_⟩
  intro N hN
  let e := Nat.log b N
  have hb1 : 1 < b := by omega
  have hNne : N ≠ 0 := by
    have hbEpos : 0 < b ^ E := pow_pos (by omega) _
    omega
  have hE_e : E ≤ e := by
    dsimp [e]
    exact Nat.le_log_of_pow_le hb1 hN
  let n := e - E
  have hEn : E + n = e := by simp only [n, Nat.add_sub_of_le hE_e]
  have hn_e : n ≤ e := Nat.sub_le e E
  have hpow_le : b ^ e ≤ N := by
    simpa [e] using Nat.pow_log_le_self b hNne
  have hN_lt : N < b ^ (e + 1) := by
    simpa [e, Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self hb1 N
  have hcount_lower_nat : t * s ^ n ≤ supportCount F N := by
    calc
      t * s ^ n = supportCount F (b ^ (E + n)) := (hexact n).symm
      _ = supportCount F (b ^ e) := by rw [hEn]
      _ ≤ supportCount F N := supportCount_mono F hpow_le
  have hcount_upper_nat : supportCount F N ≤ t * s ^ (e + 1) := by
    calc
      supportCount F N ≤ supportCount F (b ^ (e + 1)) :=
        supportCount_mono F hN_lt.le
      _ = t * s ^ ((e + 1) - E) := by
        convert hexact ((e + 1) - E) using 1
        congr 2
        omega
      _ ≤ t * s ^ (e + 1) := by
        gcongr
        omega
  have hpow_lower_real : (s : ℝ) ^ e ≤ (N : ℝ) ^ α := by
    rw [← cast_radix_pow_rpow b s e α hscale]
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hpow_le) hα
  have hpow_upper_real : (N : ℝ) ^ α ≤ (s : ℝ) ^ (e + 1) := by
    rw [← cast_radix_pow_rpow b s (e + 1) α hscale]
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hN_lt.le) hα
  constructor
  · have hcount_lower_real : (t : ℝ) * (s : ℝ) ^ n ≤
        (supportCount F N : ℝ) := by exact_mod_cast hcount_lower_nat
    apply le_trans ?_ hcount_lower_real
    calc
      c * (N : ℝ) ^ α ≤ c * (s : ℝ) ^ (e + 1) :=
        mul_le_mul_of_nonneg_left hpow_upper_real (by simp only [c]; positivity)
      _ = (t : ℝ) * (s : ℝ) ^ n := by
        simp only [c]
        rw [← hEn]
        field_simp
        ring
  · have hcount_upper_real : (supportCount F N : ℝ) ≤
        (t : ℝ) * (s : ℝ) ^ (e + 1) := by exact_mod_cast hcount_upper_nat
    apply le_trans hcount_upper_real
    calc
      (t : ℝ) * (s : ℝ) ^ (e + 1) =
          C * (s : ℝ) ^ e := by simp only [C]; rw [pow_succ]; ring
      _ ≤ C * (N : ℝ) ^ α :=
        mul_le_mul_of_nonneg_left hpow_lower_real (by simp only [C]; positivity)

/-- Two-sided support growth gives the corresponding upper power bound for
the nonzero-coefficient predicate. -/
theorem HasPowerSupportGrowth.toPowerPredicateBound
    {K : Type*} [Semiring K] {F : PowerSeries K} {α : ℝ}
    (h : HasPowerSupportGrowth F α) :
    HasPowerPredicateBound α
      (fun n => PowerSeries.coeff n F ≠ 0) := by
  obtain ⟨c, C, hc, hC, N₀, hgrowth⟩ := h
  exact (powerPredicateBound_support_iff F α).2
    ⟨C, hC.le, N₀, fun N hN => (hgrowth N hN).2⟩

private lemma supportCount_le_cutoff
    {K : Type*} [Semiring K] (F : PowerSeries K) (N : ℕ) :
    supportCount F N ≤ N := by
  classical
  unfold supportCount
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range N)

/-- Linear two-sided power growth is equivalent to an eventual positive
lower support density; the universal upper bound is `supportCount F N ≤ N`. -/
theorem hasPositiveLowerSupportDensity_iff_powerSupportGrowth_one
    {K : Type*} [Semiring K] (F : PowerSeries K) :
    HasPositiveLowerSupportDensity F ↔ HasPowerSupportGrowth F 1 := by
  constructor
  · rintro ⟨c, hc, N₀, hlower⟩
    refine ⟨c, 1, hc, by norm_num, N₀, ?_⟩
    intro N hN
    constructor
    · simpa only [Real.rpow_one] using hlower N hN
    · simpa only [Real.rpow_one, one_mul] using
        (show (supportCount F N : ℝ) ≤ (N : ℝ) by
          exact_mod_cast supportCount_le_cutoff F N)
  · rintro ⟨c, C, hc, hC, N₀, hgrowth⟩
    exact ⟨c, hc, N₀, fun N hN => by
      simpa only [Real.rpow_one] using (hgrowth N hN).1⟩

end IndependentZeroBlocks
