import SierpinskiFormal.MissingDigitPrefixes
import SierpinskiFormal.RationalPrefixTransfer
import SierpinskiFormal.SupportGeometryEquivalence

set_option autoImplicit false
namespace IndependentZeroBlocks
open SierpinskiFormal

/-- Two internal missing-digit gaps replace the terminal degree gap in the
rational-tail support obstruction. -/
theorem missingDigit_rational_supportCount_shifted_pow_lower
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b) (hApos : 0 < A.natDegree)
    (hmissing : ∃ m < b, A.coeff m = 0)
    (P D : Polynomial K) (hD0 : D.coeff 0 ≠ 0)
    (hnot : ∀ e, ¬D ∣ P * kernelPrefix b A e) (e : ℕ) :
    b ^ e ≤ D.natDegree *
      supportCount (rationalMultiple P D (canonicalSeries b A)) (b ^ (e + 2)) +
      P.natDegree + D.natDegree := by
  obtain ⟨m, hm, hAm⟩ := hmissing
  obtain ⟨k, hk, hkb, hAk, hprior⟩ := exists_first_nonzero_kernel_digit A b hApos hdegree
  obtain ⟨hcoeff1, hcoeff2, hdeg1, hdeg2, hend1, hend2, _, hdiv⟩ :=
    missingDigit_twoGap_numerator_data b hb A P hA0 hdegree
      hm hAm hk hkb hAk hprior e
  by_cases hfirst : D ∣ missingDigitFirstNumerator b A P e m
  · have hsecond : ¬D ∣ missingDigitSecondNumerator b A P e m k := by
      intro hsecond
      exact hnot (e + 1) (hdiv D hfirst hsecond)
    exact rational_prefix_gap_support_bound P D (missingDigitSecondNumerator b A P e m k)
      (canonicalSeries b A) hD0 hsecond ((k * b + m) * b ^ e)
      (b ^ e) (b ^ (e + 2)) hdeg2 hend2 hcoeff2
  · exact rational_prefix_gap_support_bound P D (missingDigitFirstNumerator b A P e m)
      (canonicalSeries b A) hD0 hfirst (m * b ^ e)
      (b ^ e) (b ^ (e + 2)) hdeg1 hend1 hcoeff1

/-- A missing digit alone forces positive lower density outside absorption,
with no strict gap below degree `b-1`. -/
theorem missingDigit_rational_positive_lower_density
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b) (hmissing : ∃ m < b, A.coeff m = 0)
    (P D : Polynomial K) (hD0 : D.coeff 0 ≠ 0)
    (hnot : ∀ e, ¬D ∣ P * kernelPrefix b A e) :
    HasPositiveLowerSupportDensity (rationalMultiple P D (canonicalSeries b A)) := by
  by_cases hApos : 0 < A.natDegree
  · have hproper : ¬D ∣ P := by simpa [kernelPrefix] using hnot 0
    have hDpos := (rational_tail_window_nonzero P D (rationalMultiple P D 1) hD0
      (by simpa using rationalMultiple_denominator P D 1 hD0) hproper).1
    apply positiveLowerSupportDensity_of_shifted_radix_bound _ b 2 D.natDegree
      (P.natDegree + D.natDegree) hb hDpos
    intro e
    simpa [Nat.add_assoc] using missingDigit_rational_supportCount_shifted_pow_lower
      b hb A hA0 hdegree hApos hmissing P D hD0 hnot e
  · exact digitProduct_rational_positive_lower_density b hb A hA0 (by omega) P D hD0 hnot

/-- The exact density criterion extends to every kernel below the radix with
an actual missing digit. -/
theorem missingDigit_rational_density_zero_iff
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b) (hmissing : ∃ m < b, A.coeff m = 0)
    (P D : Polynomial K) (hD0 : D.coeff 0 ≠ 0) :
    HasZeroSupportDensity (rationalMultiple P D (canonicalSeries b A)) ↔
      ∃ e, D ∣ P * kernelPrefix b A e := by
  constructor
  · intro hz
    by_contra habs
    have hnot : ∀ e, ¬D ∣ P * kernelPrefix b A e := by simpa using habs
    exact (missingDigit_rational_positive_lower_density b hb A hA0 hdegree hmissing
      P D hD0 hnot).not_zero hz
  · intro habs
    obtain ⟨m, hm, hAm⟩ := hmissing
    exact (digitProduct_rational_hasUniformRelativeHoles_of_absorbed b hb A hA0 hdegree
      (radixDigitSupportCount_lt_of_missingDigit b A m hm hAm) P D hD0 habs).toZeroSupportDensity

theorem missingDigit_rational_positive_lower_density_iff
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b) (hmissing : ∃ m < b, A.coeff m = 0)
    (P D : Polynomial K) (hD0 : D.coeff 0 ≠ 0) :
    HasPositiveLowerSupportDensity (rationalMultiple P D (canonicalSeries b A)) ↔
      ∀ e, ¬D ∣ P * kernelPrefix b A e := by
  constructor
  · intro hp e he
    exact hp.not_zero ((missingDigit_rational_density_zero_iff b hb A hA0 hdegree
      hmissing P D hD0).mpr ⟨e, he⟩)
  · exact missingDigit_rational_positive_lower_density b hb A hA0 hdegree hmissing P D hD0

/-- Algebraic absorption and uniform local holes now share exactly the same
missing-digit hypotheses. -/
theorem missingDigit_rational_uniformRelativeHoles_iff
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b) (hmissing : ∃ m < b, A.coeff m = 0)
    (P D : Polynomial K) (hD0 : D.coeff 0 ≠ 0) :
    HasUniformRelativeHoles (fun n => PowerSeries.coeff n
        (rationalMultiple P D (canonicalSeries b A)) ≠ 0) ↔
      ∃ e, D ∣ P * kernelPrefix b A e := by
  constructor
  · intro hholes
    exact (missingDigit_rational_density_zero_iff b hb A hA0 hdegree hmissing P D hD0).mp
      hholes.toZeroSupportDensity
  · intro habs
    obtain ⟨m, hm, hAm⟩ := hmissing
    exact digitProduct_rational_hasUniformRelativeHoles_of_absorbed b hb A hA0 hdegree
      (radixDigitSupportCount_lt_of_missingDigit b A m hm hAm) P D hD0 habs

end IndependentZeroBlocks
