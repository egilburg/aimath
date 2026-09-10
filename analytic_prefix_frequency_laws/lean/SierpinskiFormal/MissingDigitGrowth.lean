import SierpinskiFormal.MissingDigitFiber
import SierpinskiFormal.PowerFilterBounds
import SierpinskiFormal.RationalRelativeHoles

set_option autoImplicit false
namespace IndependentZeroBlocks
open SierpinskiFormal

/-- A missing digit suffices for the absorbed upper bound at the actual
digit exponent; no terminal degree gap is needed. -/
theorem missingDigit_rational_digitUpperGrowth_of_absorbed
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b) (hmissing : ∃ m < b, A.coeff m = 0)
    (P D : Polynomial K) (hD0 : D.coeff 0 ≠ 0)
    (habs : ∃ e, D ∣ P * kernelPrefix b A e) :
    HasPowerPredicateBound (digitSupportExponent b A)
      (fun n => PowerSeries.coeff n (rationalMultiple P D (canonicalSeries b A)) ≠ 0) := by
  obtain ⟨m, hm, hAm⟩ := hmissing
  have hsmall := radixDigitSupportCount_lt_of_missingDigit b A m hm hAm
  have hcanonical := canonicalSeries_digitLog_powerSupportBound b hb A hA0 hsmall
  obtain ⟨e, he⟩ := habs
  obtain ⟨H, hrep⟩ := rationalMultiple_eq_polynomial_mul_dilate_of_dvd
    b hb A hA0 hdegree e P D hD0 he
  rw [hrep]
  exact hcanonical.polynomial_mul_dilate H (b ^ e) (pow_pos (by omega) e)

/-- Every nonzero absorbed missing-digit filter has the exact original digit
exponent, including kernels of degree `b-1`. -/
theorem missingDigit_rational_powerSupportGrowth_of_absorbed
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b) (hmissing : ∃ m < b, A.coeff m = 0)
    (P D : Polynomial K) (hP : P ≠ 0) (hD0 : D.coeff 0 ≠ 0)
    (habs : ∃ e, D ∣ P * kernelPrefix b A e) :
    HasPowerSupportGrowth (rationalMultiple P D (canonicalSeries b A))
      (digitSupportExponent b A) := by
  obtain ⟨E, R, c, hR, hc, hf⟩ := absorbed_rational_canonical_exists_exact_fiber
    b hb A hA0 hdegree hmissing P D hP hD0 habs
  have hs := one_le_radixDigitSupportCount b (by omega) A hA0
  obtain ⟨m, hm, hAm⟩ := hmissing
  have hsmall := radixDigitSupportCount_lt_of_missingDigit b A m hm hAm
  apply hasPowerSupportGrowth_of_radix_lower_bound _ b
    (radixDigitSupportCount b A) E hb hs (digitSupportExponent b A)
    (radixDigitLogExponent_mem_Ico b hb A hA0 hsmall).1
    (rpow_radixLogExponent b (radixDigitSupportCount b A) hb hs)
    (missingDigit_rational_digitUpperGrowth_of_absorbed
      b hb A hA0 hdegree ⟨m, hm, hAm⟩ P D hD0 habs)
  intro n
  have h := supportCount_le_of_coefficient_fiber (canonicalSeries b A)
    (rationalMultiple P D (canonicalSeries b A))
    (b ^ E) R (pow_pos (by omega) E) hR c hc hf (b ^ n)
  rwa [supportCount_canonicalSeries_pow_eq_digitSupport b hb A hA0 n, ← pow_add] at h

end IndependentZeroBlocks
