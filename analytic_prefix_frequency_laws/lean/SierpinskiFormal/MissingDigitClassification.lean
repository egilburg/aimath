import SierpinskiFormal.MissingDigitDensity
import SierpinskiFormal.MissingDigitGrowth

set_option autoImplicit false
namespace IndependentZeroBlocks
open SierpinskiFormal

/-- Outside absorption the exact support-growth exponent is one. -/
theorem missingDigit_rational_linearGrowth_iff
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b) (hmissing : ∃ m < b, A.coeff m = 0) (P D : Polynomial K)
    (hD0 : D.coeff 0 ≠ 0) :
    HasPowerSupportGrowth (rationalMultiple P D (canonicalSeries b A)) 1 ↔
      ∀ e, ¬ D ∣ P * kernelPrefix b A e := by
  rw [← hasPositiveLowerSupportDensity_iff_powerSupportGrowth_one]
  exact missingDigit_rational_positive_lower_density_iff b hb A hA0 hdegree hmissing P D hD0

/-- Complete growth classification: zero numerator, unchanged digit exponent
under absorption, or linear support growth outside absorption. -/
theorem missingDigit_rational_supportGrowth_classification
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b) (hmissing : ∃ m < b, A.coeff m = 0) (P D : Polynomial K)
    (hD0 : D.coeff 0 ≠ 0) :
    (P = 0 ∧ rationalMultiple P D (canonicalSeries b A) = 0) ∨
    (P ≠ 0 ∧ (∃ e, D ∣ P * kernelPrefix b A e) ∧
      HasPowerSupportGrowth (rationalMultiple P D (canonicalSeries b A))
        (digitSupportExponent b A)) ∨
    ((∀ e, ¬ D ∣ P * kernelPrefix b A e) ∧
      HasPowerSupportGrowth (rationalMultiple P D (canonicalSeries b A)) 1) := by
  by_cases hP : P = 0
  · exact Or.inl ⟨hP, by simp [hP, rationalMultiple]⟩
  · by_cases habs : ∃ e, D ∣ P * kernelPrefix b A e
    · exact Or.inr (Or.inl ⟨hP, habs,
        missingDigit_rational_powerSupportGrowth_of_absorbed b hb A hA0 hdegree hmissing P D hP hD0 habs⟩)
    · have hnot : ∀ e, ¬ D ∣ P * kernelPrefix b A e := by simpa using habs
      exact Or.inr (Or.inr ⟨hnot,
        (missingDigit_rational_linearGrowth_iff b hb A hA0 hdegree hmissing P D hD0).2 hnot⟩)

/-- The digit exponent characterizes exactly the nonzero absorbed filters. -/
theorem missingDigit_rational_digitGrowth_iff
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b) (hmissing : ∃ m < b, A.coeff m = 0) (P D : Polynomial K)
    (hD0 : D.coeff 0 ≠ 0) :
    HasPowerSupportGrowth (rationalMultiple P D (canonicalSeries b A))
        (digitSupportExponent b A) ↔
      P ≠ 0 ∧ ∃ e, D ∣ P * kernelPrefix b A e := by
  constructor
  · intro hgrowth
    have hP : P ≠ 0 := by
      intro hzero
      apply hgrowth.ne_zero
      simp [hzero, rationalMultiple]
    refine ⟨hP, ?_⟩
    by_contra habs
    have hnot : ∀ e, ¬D ∣ P * kernelPrefix b A e := by simpa using habs
    have hlinear :=
      (missingDigit_rational_linearGrowth_iff b hb A hA0 hdegree hmissing P D hD0).2 hnot
    have heq := hgrowth.exponent_eq hlinear
    have hlt : digitSupportExponent b A < 1 :=
      (radixDigitLogExponent_mem_Ico b hb A hA0
        (by obtain ⟨m, hm, hAm⟩ := hmissing; exact radixDigitSupportCount_lt_of_missingDigit b A m hm hAm)).2
    linarith
  · rintro ⟨hP, habs⟩
    exact missingDigit_rational_powerSupportGrowth_of_absorbed
      b hb A hA0 hdegree hmissing P D hP hD0 habs

/-- Even the upper bound at the digit exponent characterizes absorption.
Unlike two-sided growth, this includes the zero numerator. -/
theorem missingDigit_rational_digitUpperGrowth_iff
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b) (hmissing : ∃ m < b, A.coeff m = 0) (P D : Polynomial K)
    (hD0 : D.coeff 0 ≠ 0) :
    HasPowerPredicateBound (digitSupportExponent b A)
        (fun n => PowerSeries.coeff n
          (rationalMultiple P D (canonicalSeries b A)) ≠ 0) ↔
      ∃ e, D ∣ P * kernelPrefix b A e := by
  constructor
  · intro hbound
    have hα : digitSupportExponent b A < 1 :=
      (radixDigitLogExponent_mem_Ico b hb A hA0
        (by obtain ⟨m, hm, hAm⟩ := hmissing; exact radixDigitSupportCount_lt_of_missingDigit b A m hm hAm)).2
    have hz := (zeroPredicateDensity_support_iff _).mp
      (hbound.toZeroPredicateDensity hα)
    exact (missingDigit_rational_density_zero_iff b hb A hA0 hdegree hmissing P D hD0).mp hz
  · intro habs
    by_cases hP : P = 0
    · have hz : rationalMultiple P D (canonicalSeries b A) = 0 := by
        simp [hP, rationalMultiple]
      rw [hz]
      refine ⟨0, le_rfl, 0, ?_⟩
      intro N _
      simp [predicateCount]
    · exact (missingDigit_rational_powerSupportGrowth_of_absorbed
        b hb A hA0 hdegree hmissing P D hP hD0 habs).toPowerPredicateBound

/-- Any sublinear power upper bound is equivalent to finite-prefix absorption;
if one exists, the bound at the actual digit exponent already holds. -/
theorem missingDigit_rational_sublinearGrowth_iff
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b) (hmissing : ∃ m < b, A.coeff m = 0) (P D : Polynomial K)
    (hD0 : D.coeff 0 ≠ 0) :
    (∃ α : ℝ, α < 1 ∧ HasPowerPredicateBound α
      (fun n => PowerSeries.coeff n
        (rationalMultiple P D (canonicalSeries b A)) ≠ 0)) ↔
      ∃ e, D ∣ P * kernelPrefix b A e := by
  constructor
  · rintro ⟨α, hα, hbound⟩
    exact (missingDigit_rational_density_zero_iff b hb A hA0 hdegree hmissing P D hD0).mp
      ((zeroPredicateDensity_support_iff _).mp (hbound.toZeroPredicateDensity hα))
  · intro habs
    exact ⟨digitSupportExponent b A,
      (radixDigitLogExponent_mem_Ico b hb A hA0
        (by obtain ⟨m, hm, hAm⟩ := hmissing; exact radixDigitSupportCount_lt_of_missingDigit b A m hm hAm)).2,
      (missingDigit_rational_digitUpperGrowth_iff b hb A hA0 hdegree hmissing P D hD0).mpr habs⟩

/-- Uniform translated-interval sublinear counting is another equivalent
description of the absorbed filters. The constant is uniform in the location. -/
theorem missingDigit_rational_uniformSublinearGrowth_iff
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b) (hmissing : ∃ m < b, A.coeff m = 0) (P D : Polynomial K)
    (hD0 : D.coeff 0 ≠ 0) :
    (∃ α : ℝ, α < 1 ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ a N : ℕ, 1 ≤ N →
      (intervalPredicateCount (fun n => PowerSeries.coeff n
        (rationalMultiple P D (canonicalSeries b A)) ≠ 0) a N : ℝ) ≤
          C * (N : ℝ) ^ α) ↔
      ∃ e, D ∣ P * kernelPrefix b A e := by
  constructor
  · rintro ⟨α, hα, C, hC, hlocal⟩
    apply (missingDigit_rational_sublinearGrowth_iff b hb A hA0 hdegree hmissing P D hD0).mp
    refine ⟨α, hα, C, hC, 1, ?_⟩
    intro N hN
    have heq : predicateCount (fun n => PowerSeries.coeff n
        (rationalMultiple P D (canonicalSeries b A)) ≠ 0) N =
      intervalPredicateCount (fun n => PowerSeries.coeff n
        (rationalMultiple P D (canonicalSeries b A)) ≠ 0) 0 N := by
      classical
      unfold predicateCount intervalPredicateCount
      congr 1
      ext n
      simp
    rw [heq]
    exact hlocal 0 N hN
  · intro habs
    obtain ⟨α, _, hα, C, hC, hlocal⟩ :=
      ((missingDigit_rational_uniformRelativeHoles_iff b hb A hA0 hdegree hmissing P D hD0).mpr
        habs).exists_uniform_interval_power_bound
    exact ⟨α, hα, C, hC, hlocal⟩

/-- Density, sharp digit upper growth, any sublinear upper growth, and uniform
relative holes coincide on the rational digit-product family. -/
theorem missingDigit_rational_sparse_geometry_equivalences
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b) (hmissing : ∃ m < b, A.coeff m = 0) (P D : Polynomial K)
    (hD0 : D.coeff 0 ≠ 0) :
    (HasZeroSupportDensity (rationalMultiple P D (canonicalSeries b A)) ↔
      HasUniformRelativeHoles (fun n => PowerSeries.coeff n
        (rationalMultiple P D (canonicalSeries b A)) ≠ 0)) ∧
    (HasUniformRelativeHoles (fun n => PowerSeries.coeff n
        (rationalMultiple P D (canonicalSeries b A)) ≠ 0) ↔
      HasPowerPredicateBound (digitSupportExponent b A)
        (fun n => PowerSeries.coeff n
          (rationalMultiple P D (canonicalSeries b A)) ≠ 0)) ∧
    ((∃ α : ℝ, α < 1 ∧ HasPowerPredicateBound α
        (fun n => PowerSeries.coeff n
          (rationalMultiple P D (canonicalSeries b A)) ≠ 0)) ↔
      ∃ e, D ∣ P * kernelPrefix b A e) := by
  have hh := missingDigit_rational_uniformRelativeHoles_iff b hb A hA0 hdegree hmissing P D hD0
  exact ⟨(missingDigit_rational_density_zero_iff b hb A hA0 hdegree hmissing P D hD0).trans hh.symm,
    hh.trans (missingDigit_rational_digitUpperGrowth_iff b hb A hA0 hdegree hmissing P D hD0).symm,
    missingDigit_rational_sublinearGrowth_iff b hb A hA0 hdegree hmissing P D hD0⟩


/-- One central zero/sparse/dense statement under a genuine missing digit.
The sparse branch retains both exact exponent and exact coefficient self-copy. -/
theorem missingDigit_rational_central_classification
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b) (hmissing : ∃ m < b, A.coeff m = 0)
    (P D : Polynomial K) (hD0 : D.coeff 0 ≠ 0) :
    (P = 0 ∧ rationalMultiple P D (canonicalSeries b A) = 0) ∨
    (P ≠ 0 ∧ (∃ e, D ∣ P * kernelPrefix b A e) ∧
      HasPowerSupportGrowth (rationalMultiple P D (canonicalSeries b A))
        (digitSupportExponent b A) ∧
      HasUniformRelativeHoles (fun n => PowerSeries.coeff n
        (rationalMultiple P D (canonicalSeries b A)) ≠ 0) ∧
      ∃ E R : ℕ, ∃ c : K, R < b ^ E ∧ c ≠ 0 ∧ ∀ n : ℕ,
        PowerSeries.coeff (b ^ E * n + R)
          (rationalMultiple P D (canonicalSeries b A)) =
            c * PowerSeries.coeff n (canonicalSeries b A)) ∨
    ((∀ e, ¬D ∣ P * kernelPrefix b A e) ∧
      HasPositiveLowerSupportDensity (rationalMultiple P D (canonicalSeries b A)) ∧
      HasPowerSupportGrowth (rationalMultiple P D (canonicalSeries b A)) 1 ∧
      ¬HasUniformRelativeHoles (fun n => PowerSeries.coeff n
        (rationalMultiple P D (canonicalSeries b A)) ≠ 0)) := by
  by_cases hP : P = 0
  · exact Or.inl ⟨hP, by simp [hP, rationalMultiple]⟩
  · by_cases habs : ∃ e, D ∣ P * kernelPrefix b A e
    · exact Or.inr (Or.inl ⟨hP, habs,
        missingDigit_rational_powerSupportGrowth_of_absorbed b hb A hA0 hdegree
          hmissing P D hP hD0 habs,
        (missingDigit_rational_uniformRelativeHoles_iff b hb A hA0 hdegree
          hmissing P D hD0).mpr habs,
        absorbed_rational_canonical_exists_exact_fiber b hb A hA0 hdegree
          hmissing P D hP hD0 habs⟩)
    · have hnot : ∀ e, ¬D ∣ P * kernelPrefix b A e := by simpa using habs
      have hd := missingDigit_rational_positive_lower_density
        b hb A hA0 hdegree hmissing P D hD0 hnot
      exact Or.inr (Or.inr ⟨hnot, hd,
        (hasPositiveLowerSupportDensity_iff_powerSupportGrowth_one _).mp hd,
        hd.not_uniformRelativeHoles⟩)

/-- Finite-field absorption is a single divisibility test at the degree boundary. -/
theorem missingDigit_finiteField_density_zero_iff_finite_test
    {K : Type*} [Field K] [Fintype K]
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < Fintype.card K)
    (hmissing : ∃ m < Fintype.card K, A.coeff m = 0)
    (P D : Polynomial K) (hD0 : D.coeff 0 ≠ 0) :
    HasZeroSupportDensity
      (rationalMultiple P D (canonicalSeries (Fintype.card K) A)) ↔
      D ∣ P * A ^ D.natDegree := by
  exact (missingDigit_rational_density_zero_iff (Fintype.card K)
    Fintype.one_lt_card A hA0 hdegree hmissing P D hD0).trans
      (exists_dvd_mul_kernelPrefix_iff_dvd_mul_pow_natDegree
        (show D ≠ 0 by intro hz; apply hD0; simp [hz]))

theorem missingDigit_finiteField_uniformRelativeHoles_iff_finite_test
    {K : Type*} [Field K] [Fintype K]
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < Fintype.card K)
    (hmissing : ∃ m < Fintype.card K, A.coeff m = 0)
    (P D : Polynomial K) (hD0 : D.coeff 0 ≠ 0) :
    HasUniformRelativeHoles (fun n => PowerSeries.coeff n
      (rationalMultiple P D (canonicalSeries (Fintype.card K) A)) ≠ 0) ↔
      D ∣ P * A ^ D.natDegree := by
  exact (missingDigit_rational_uniformRelativeHoles_iff (Fintype.card K)
    Fintype.one_lt_card A hA0 hdegree hmissing P D hD0).trans
      (exists_dvd_mul_kernelPrefix_iff_dvd_mul_pow_natDegree
        (show D ≠ 0 by intro hz; apply hD0; simp [hz]))

theorem missingDigit_finiteField_digitGrowth_iff_finite_test
    {K : Type*} [Field K] [Fintype K]
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < Fintype.card K)
    (hmissing : ∃ m < Fintype.card K, A.coeff m = 0)
    (P D : Polynomial K) (hD0 : D.coeff 0 ≠ 0) :
    HasPowerSupportGrowth
      (rationalMultiple P D (canonicalSeries (Fintype.card K) A))
      (digitSupportExponent (Fintype.card K) A) ↔
      P ≠ 0 ∧ D ∣ P * A ^ D.natDegree := by
  rw [missingDigit_rational_digitGrowth_iff (Fintype.card K)
    Fintype.one_lt_card A hA0 hdegree hmissing P D hD0]
  exact and_congr_right fun _ =>
    exists_dvd_mul_kernelPrefix_iff_dvd_mul_pow_natDegree
      (show D ≠ 0 by intro hz; apply hD0; simp [hz])

/-- The same finite test for an equation-specified normalized algebraic branch. -/
theorem missingDigit_normalized_branch_digitGrowth_iff_finite_test
    {K : Type*} [Field K] [Fintype K]
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < Fintype.card K)
    (hmissing : ∃ m < Fintype.card K, A.coeff m = 0)
    (T : PowerSeries K) (hT0 : PowerSeries.coeff 0 T = 1)
    (hbranch : (A : PowerSeries K) * T ^ (Fintype.card K - 1) = 1)
    (P D : Polynomial K) (hD0 : D.coeff 0 ≠ 0) :
    HasPowerSupportGrowth (rationalMultiple P D T)
      (digitSupportExponent (Fintype.card K) A) ↔
      P ≠ 0 ∧ D ∣ P * A ^ D.natDegree := by
  rw [eq_canonicalSeries_of_normalized_branch A hA0 hdegree T hT0 hbranch]
  exact missingDigit_finiteField_digitGrowth_iff_finite_test
    A hA0 hdegree hmissing P D hD0

end IndependentZeroBlocks
