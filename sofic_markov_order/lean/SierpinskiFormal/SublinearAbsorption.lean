import SierpinskiFormal.PowerDensityBridge
import SierpinskiFormal.RationalSupportGrowth

set_option autoImplicit false

namespace IndependentZeroBlocks
open SierpinskiFormal

/-- Even the upper bound at the digit exponent characterizes absorption.
Unlike two-sided growth, this includes the zero numerator. -/
theorem digitProduct_rational_digitUpperGrowth_iff
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b - 1) (P D : Polynomial K)
    (hD0 : D.coeff 0 ≠ 0) :
    HasPowerPredicateBound (digitSupportExponent b A)
        (fun n => PowerSeries.coeff n
          (rationalMultiple P D (canonicalSeries b A)) ≠ 0) ↔
      ∃ e, D ∣ P * kernelPrefix b A e := by
  constructor
  · intro hbound
    have hα : digitSupportExponent b A < 1 :=
      (radixDigitLogExponent_mem_Ico b hb A hA0
        (radixDigitSupportCount_lt_of_degree b A hdegree)).2
    have hz := (zeroPredicateDensity_support_iff _).mp
      (hbound.toZeroPredicateDensity hα)
    exact (digitProduct_rational_density_zero_iff b hb A hA0 hdegree P D hD0).mp hz
  · intro habs
    by_cases hP : P = 0
    · have hz : rationalMultiple P D (canonicalSeries b A) = 0 := by
        simp [hP, rationalMultiple]
      rw [hz]
      refine ⟨0, le_rfl, 0, ?_⟩
      intro N _
      simp [predicateCount]
    · exact (digitProduct_rational_powerSupportGrowth_of_absorbed
        b hb A hA0 hdegree P D hP hD0 habs).toPowerPredicateBound

/-- Any sublinear power upper bound is equivalent to finite-prefix absorption;
if one exists, the bound at the actual digit exponent already holds. -/
theorem digitProduct_rational_sublinearGrowth_iff
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b - 1) (P D : Polynomial K)
    (hD0 : D.coeff 0 ≠ 0) :
    (∃ α : ℝ, α < 1 ∧ HasPowerPredicateBound α
      (fun n => PowerSeries.coeff n
        (rationalMultiple P D (canonicalSeries b A)) ≠ 0)) ↔
      ∃ e, D ∣ P * kernelPrefix b A e := by
  constructor
  · rintro ⟨α, hα, hbound⟩
    exact (digitProduct_rational_density_zero_iff b hb A hA0 hdegree P D hD0).mp
      ((zeroPredicateDensity_support_iff _).mp (hbound.toZeroPredicateDensity hα))
  · intro habs
    exact ⟨digitSupportExponent b A,
      (radixDigitLogExponent_mem_Ico b hb A hA0
        (radixDigitSupportCount_lt_of_degree b A hdegree)).2,
      (digitProduct_rational_digitUpperGrowth_iff b hb A hA0 hdegree P D hD0).mpr habs⟩

end IndependentZeroBlocks
