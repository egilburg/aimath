import SierpinskiFormal.DigitSupportGrowth

set_option autoImplicit false

/-!
# Counting the actual radix digit support

The canonical series only reads coefficients of its digit polynomial at
indices below the radix.  This file bounds its support using the number of
those coefficients that are actually nonzero, which can be much smaller than
the degree-based bound.
-/

namespace IndependentZeroBlocks

open SierpinskiFormal

/-- The number of nonzero coefficients of `A` at digit positions strictly
below the radix `b`. -/
noncomputable def radixDigitSupportCount
    {K : Type*} [Semiring K] (b : ℕ) (A : Polynomial K) : ℕ := by
  classical
  exact ((Finset.range b).filter fun d => A.coeff d ≠ 0).card

/-- A nonzero constant digit ensures that the radix digit support is
nonempty. -/
theorem one_le_radixDigitSupportCount
    {K : Type*} [Semiring K] [Nontrivial K] (b : ℕ) (hb : 0 < b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1) :
    1 ≤ radixDigitSupportCount b A := by
  classical
  apply Finset.card_pos.mpr
  refine ⟨0, ?_⟩
  simp [radixDigitSupportCount, hb, hA0]

private theorem canonical_supportCount_radix_step_digitSupport
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1) (e : ℕ) :
    supportCount (canonicalSeries b A) (b ^ (e + 1)) ≤
      radixDigitSupportCount b A *
        supportCount (canonicalSeries b A) (b ^ e) := by
  classical
  let S := (Finset.range (b ^ (e + 1))).filter fun n =>
    PowerSeries.coeff n (canonicalSeries b A) ≠ 0
  let D := (Finset.range b).filter fun d => A.coeff d ≠ 0
  let T := D ×ˢ
    ((Finset.range (b ^ e)).filter fun n =>
      PowerSeries.coeff n (canonicalSeries b A) ≠ 0)
  let f : ℕ → ℕ × ℕ := fun n => (n % b, n / b)
  have hf : ∀ n ∈ S, f n ∈ T := by
    intro n hn
    have hnmem := hn
    simp only [S, Finset.mem_filter, Finset.mem_range] at hnmem
    have hrem : n % b < b := Nat.mod_lt n (by omega)
    have hsplit : b * (n / b) + n % b = n := Nat.div_add_mod n b
    have hcoeff :
        PowerSeries.coeff (n / b) (canonicalSeries b A) *
            A.coeff (n % b) ≠ 0 := by
      rw [← coeff_canonicalSeries_mul_add b hb A hA0
        (n / b) (n % b) hrem]
      simpa [hsplit] using hnmem.2
    have hquot : n / b < b ^ e := by
      have hnlt : n < b ^ e * b := by
        simpa [pow_succ, Nat.mul_comm] using hnmem.1
      exact (Nat.div_lt_iff_lt_mul (by omega)).2 hnlt
    simp only [f, T, D, Finset.mem_product, Finset.mem_filter,
      Finset.mem_range]
    exact ⟨⟨hrem, right_ne_zero_of_mul hcoeff⟩,
      ⟨hquot, left_ne_zero_of_mul hcoeff⟩⟩
  have finj : (S : Set ℕ).InjOn f := by
    intro m hm n hn hmn
    have hmod : m % b = n % b := congrArg Prod.fst hmn
    have hdiv : m / b = n / b := congrArg Prod.snd hmn
    calc
      m = m % b + b * (m / b) := (Nat.mod_add_div m b).symm
      _ = n % b + b * (n / b) := by rw [hmod, hdiv]
      _ = n := Nat.mod_add_div n b
  have hcard := Finset.card_le_card_of_injOn f hf finj
  simpa [S, T, D, supportCount, radixDigitSupportCount,
    Finset.card_product] using hcard

/-- At the cutoff containing the first `e` radix digits, the canonical-series
support is bounded by the `e`th power of the number of genuinely available
digits. -/
theorem supportCount_canonicalSeries_pow_le_digitSupport
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1) (e : ℕ) :
    supportCount (canonicalSeries b A) (b ^ e) ≤
      radixDigitSupportCount b A ^ e := by
  classical
  induction e with
  | zero =>
      change ((Finset.range 1).filter fun n =>
        PowerSeries.coeff n (canonicalSeries b A) ≠ 0).card ≤ 1
      exact (Finset.card_filter_le _ _).trans_eq (by simp)
  | succ e ih =>
      calc
        supportCount (canonicalSeries b A) (b ^ (e + 1)) ≤
            radixDigitSupportCount b A *
              supportCount (canonicalSeries b A) (b ^ e) :=
          canonical_supportCount_radix_step_digitSupport b hb A hA0 e
        _ ≤ radixDigitSupportCount b A *
              radixDigitSupportCount b A ^ e :=
          Nat.mul_le_mul_left _ ih
        _ = radixDigitSupportCount b A ^ (e + 1) := by
          rw [pow_succ]
          ac_rfl

/-- Any exponent large enough for the actual digit count gives an eventual
power upper bound for the canonical-series support. -/
theorem canonicalSeries_digitSupport_powerSupportBound
    {K : Type*} [Field K]
    (b : ℕ) (hb : 2 ≤ b) (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (α : ℝ) (hα : 0 ≤ α)
    (hscale :
      (radixDigitSupportCount b A : ℝ) ≤ (b : ℝ) ^ α) :
    HasPowerPredicateBound α
      (fun n => PowerSeries.coeff n (canonicalSeries b A) ≠ 0) := by
  apply powerSupportBound_of_radix_counts
    (canonicalSeries b A) b (radixDigitSupportCount b A) hb
    (one_le_radixDigitSupportCount b (by omega) A hA0) α hα hscale
  exact supportCount_canonicalSeries_pow_le_digitSupport b hb A hA0

/-- If the actual digit support is smaller than the radix, its logarithmic
upper-bound exponent lies in `[0, 1)`. -/
theorem radixDigitLogExponent_mem_Ico
    {K : Type*} [Field K]
    (b : ℕ) (hb : 2 ≤ b) (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hsmall : radixDigitSupportCount b A < b) :
    Real.log (radixDigitSupportCount b A : ℝ) / Real.log (b : ℝ) ∈
      Set.Ico (0 : ℝ) 1 := by
  exact radixLogExponent_mem_Ico b (radixDigitSupportCount b A) hb
    (one_le_radixDigitSupportCount b (by omega) A hA0) hsmall

/-- If at least one radix digit is absent, the canonical-series support has an
eventual upper bound with the exact logarithmic exponent of its actual digit
count.  This is only an upper growth bound; no matching lower bound is asserted.
-/
theorem canonicalSeries_digitLog_powerSupportBound
    {K : Type*} [Field K]
    (b : ℕ) (hb : 2 ≤ b) (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hsmall : radixDigitSupportCount b A < b) :
    HasPowerPredicateBound
      (Real.log (radixDigitSupportCount b A : ℝ) / Real.log (b : ℝ))
      (fun n => PowerSeries.coeff n (canonicalSeries b A) ≠ 0) := by
  have hs := one_le_radixDigitSupportCount b (by omega) A hA0
  have hexponent :=
    radixDigitLogExponent_mem_Ico b hb A hA0 hsmall
  apply canonicalSeries_digitSupport_powerSupportBound b hb A hA0
    (Real.log (radixDigitSupportCount b A : ℝ) / Real.log (b : ℝ))
    hexponent.1
  rw [rpow_radixLogExponent b (radixDigitSupportCount b A) hb hs]

end IndependentZeroBlocks
