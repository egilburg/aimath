import SierpinskiFormal.PowerIntervalDefs
import SierpinskiFormal.SupportCounting

set_option autoImplicit false

/-!
# Power bounds for digit-product supports

This file turns support estimates at radix powers into eventual real-power
bounds at every cutoff.  It then applies the transfer to canonical digit-product
series, including the binary-digit series in radix four.
-/

namespace IndependentZeroBlocks

open SierpinskiFormal

/-- A support bound at every radix power gives an eventual power bound at all
cutoffs.  The resulting constant is the digit bound `s`, and the estimate
holds from cutoff one onward. -/
theorem powerSupportBound_of_radix_counts
    {K : Type*} [Semiring K] (F : PowerSeries K)
    (b s : ℕ) (hb : 2 ≤ b) (hs : 1 ≤ s)
    (α : ℝ) (hα : 0 ≤ α)
    (hscale : (s : ℝ) ≤ (b : ℝ) ^ α)
    (hpow : ∀ e : ℕ, supportCount F (b ^ e) ≤ s ^ e) :
    HasPowerPredicateBound α
      (fun n => PowerSeries.coeff n F ≠ 0) := by
  classical
  refine ⟨s, by positivity, 1, ?_⟩
  intro N hN
  let e := Nat.log b N
  have hNne : N ≠ 0 := by omega
  have hNnext : N ≤ b ^ (e + 1) :=
    Nat.le_of_lt (by
      simpa [e, Nat.succ_eq_add_one] using
        Nat.lt_pow_succ_log_self (by omega : 1 < b) N)
  have hcountNat : supportCount F N ≤ s ^ (e + 1) :=
    (supportCount_mono F hNnext).trans (hpow (e + 1))
  have hcountReal : (supportCount F N : ℝ) ≤ (s : ℝ) ^ (e + 1) := by
    exact_mod_cast hcountNat
  have hscalePow : (s : ℝ) ^ e ≤ ((b : ℝ) ^ α) ^ e :=
    pow_le_pow_left₀ (by positivity) hscale e
  have hpowN : b ^ e ≤ N := by
    simpa [e] using Nat.pow_log_le_self b hNne
  have hrpowN : (((b : ℝ) ^ e) : ℝ) ^ α ≤ (N : ℝ) ^ α :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hpowN) hα
  have hradix :
      ((b : ℝ) ^ α) ^ e = (((b : ℝ) ^ e) : ℝ) ^ α := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    rw [mul_comm]
    rw [Real.rpow_mul (by positivity), Real.rpow_natCast]
  have hfinal : (supportCount F N : ℝ) ≤ (s : ℝ) * (N : ℝ) ^ α := by
    calc
      (supportCount F N : ℝ) ≤ (s : ℝ) ^ (e + 1) := hcountReal
      _ = (s : ℝ) * (s : ℝ) ^ e := by rw [pow_succ]; ring
      _ ≤ (s : ℝ) * (((b : ℝ) ^ α) ^ e) :=
        mul_le_mul_of_nonneg_left hscalePow (by positivity)
      _ = (s : ℝ) * (((b : ℝ) ^ e) : ℝ) ^ α := by rw [hradix]
      _ ≤ (s : ℝ) * (N : ℝ) ^ α :=
        mul_le_mul_of_nonneg_left hrpowN (by positivity)
  have hcountEq :
      predicateCount (fun n => PowerSeries.coeff n F ≠ 0) N =
        supportCount F N := by
    unfold predicateCount supportCount
    congr
  rw [hcountEq]
  exact hfinal

/-- If `1 ≤ s < b`, the base-`b` logarithmic exponent for `s` lies in
`[0, 1)`. -/
theorem radixLogExponent_mem_Ico
    (b s : ℕ) (hb : 2 ≤ b) (hs : 1 ≤ s) (hsb : s < b) :
    Real.log (s : ℝ) / Real.log (b : ℝ) ∈ Set.Ico (0 : ℝ) 1 := by
  have hbpos : (0 : ℝ) < (b : ℝ) := by positivity
  have hspos : (0 : ℝ) < (s : ℝ) := by positivity
  have hlogb : 0 < Real.log (b : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < b by omega))
  have hlogs : 0 ≤ Real.log (s : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hs)
  refine ⟨div_nonneg hlogs hlogb.le, (div_lt_one hlogb).2 ?_⟩
  exact Real.strictMonoOn_log hspos hbpos (by exact_mod_cast hsb)

/-- Raising the radix to its logarithmic support exponent recovers the digit
bound. -/
theorem rpow_radixLogExponent
    (b s : ℕ) (hb : 2 ≤ b) (hs : 1 ≤ s) :
    (b : ℝ) ^ (Real.log (s : ℝ) / Real.log (b : ℝ)) = (s : ℝ) := by
  have hbpos : (0 : ℝ) < (b : ℝ) := by positivity
  have hspos : (0 : ℝ) < (s : ℝ) := by positivity
  have hlogb : Real.log (b : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < b by omega)))
  rw [Real.rpow_def_of_pos hbpos]
  have hmul :
      Real.log (b : ℝ) * (Real.log (s : ℝ) / Real.log (b : ℝ)) =
        Real.log (s : ℝ) := by
    field_simp
  rw [hmul, Real.exp_log hspos]

/-- The canonical series inherits a power support bound whenever the number of
available digits is at most the radix raised to the proposed exponent. -/
theorem canonicalSeries_powerSupportBound
    {K : Type*} [Field K]
    (b : ℕ) (hb : 2 ≤ b) (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (α : ℝ) (hα : 0 ≤ α)
    (hscale : ((A.natDegree + 1 : ℕ) : ℝ) ≤ (b : ℝ) ^ α) :
    HasPowerPredicateBound α
      (fun n => PowerSeries.coeff n (canonicalSeries b A) ≠ 0) := by
  apply powerSupportBound_of_radix_counts
    (canonicalSeries b A) b (A.natDegree + 1) hb (by omega) α hα hscale
  exact supportCount_canonicalSeries_pow_le b hb A hA0

/-- When the canonical digit set is strictly smaller than the radix, its
support satisfies the exact logarithmic power bound. -/
theorem canonicalSeries_radixLog_powerSupportBound
    {K : Type*} [Field K]
    (b : ℕ) (hb : 2 ≤ b) (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree + 1 < b) :
    HasPowerPredicateBound
      (Real.log ((A.natDegree + 1 : ℕ) : ℝ) / Real.log (b : ℝ))
      (fun n => PowerSeries.coeff n (canonicalSeries b A) ≠ 0) := by
  have hexponent := radixLogExponent_mem_Ico
    b (A.natDegree + 1) hb (by omega) hdegree
  apply canonicalSeries_powerSupportBound b hb A hA0
    (Real.log ((A.natDegree + 1 : ℕ) : ℝ) / Real.log (b : ℝ))
    hexponent.1
  rw [rpow_radixLogExponent b (A.natDegree + 1) hb (by omega)]

/-- In radix four, the canonical series with digit polynomial `1 + X` has at
most a constant times the square root of the cutoff many nonzero
coefficients. -/
theorem canonicalSeries_four_one_add_X_powerSupportBound
    {K : Type*} [Field K] :
    HasPowerPredicateBound (1 / 2 : ℝ)
      (fun n =>
        PowerSeries.coeff n
          (canonicalSeries 4 (1 + Polynomial.X : Polynomial K)) ≠ 0) := by
  apply canonicalSeries_powerSupportBound 4 (by omega)
    (1 + Polynomial.X : Polynomial K) (by simp) (1 / 2 : ℝ) (by positivity)
  have hdegree :
      (1 + Polynomial.X : Polynomial K).natDegree = 1 := by
    rw [add_comm]
    simpa using Polynomial.natDegree_X_add_C (1 : K)
  rw [hdegree]
  change (2 : ℝ) ≤ (4 : ℝ) ^ (1 / 2 : ℝ)
  rw [← Real.sqrt_eq_rpow]
  have hsqrt : Real.sqrt 4 = 2 :=
    (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).2 (by norm_num)
  rw [hsqrt]

end IndependentZeroBlocks
