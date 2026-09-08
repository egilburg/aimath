import SierpinskiFormal.ExactDigitSupport
import SierpinskiFormal.ExactPowerGrowth
import SierpinskiFormal.PolynomialBlockSupport
import SierpinskiFormal.AbsorbedBlockForm
import SierpinskiFormal.FiniteFieldDensity

set_option autoImplicit false

namespace IndependentZeroBlocks
open SierpinskiFormal

/-- The digit exponent determined by the actual nonzero digit coefficients. -/
noncomputable def digitSupportExponent
    {K : Type*} [Semiring K] (b : ℕ) (A : Polynomial K) : ℝ :=
  Real.log (radixDigitSupportCount b A : ℝ) / Real.log (b : ℝ)

/-- The degree gap forces a genuinely missing digit. -/
theorem radixDigitSupportCount_lt_of_degree
    {K : Type*} [Semiring K] (b : ℕ) (A : Polynomial K)
    (hdegree : A.natDegree < b - 1) : radixDigitSupportCount b A < b := by
  classical
  have hle : radixDigitSupportCount b A ≤ A.natDegree + 1 := by
    unfold radixDigitSupportCount
    apply le_trans (Finset.card_le_card ?_) (Finset.card_range _).le
    intro d hd
    simp only [Finset.mem_filter, Finset.mem_range] at hd ⊢
    exact Nat.lt_succ_of_le (Polynomial.le_natDegree_of_ne_zero hd.2)
  omega

/-- Exact support counts for all sufficiently deep radix cutoffs of an
absorbed nonzero filter. The finite multiplier and the depth are supplied by
the theorem, not imposed as representation hypotheses. -/
theorem digitProduct_rational_exact_radix_counts
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b - 1) (P D : Polynomial K)
    (hP : P ≠ 0) (hD0 : D.coeff 0 ≠ 0)
    (habs : ∃ e, D ∣ P * kernelPrefix b A e) :
    ∃ E t : ℕ, 0 < t ∧ ∀ n : ℕ,
      supportCount (rationalMultiple P D (canonicalSeries b A)) (b ^ (E + n)) =
        t * radixDigitSupportCount b A ^ n := by
  obtain ⟨E, H, hH, hshort, hpoly, hform⟩ :=
    rationalMultiple_exists_disjoint_block_form b hb A hA0 hdegree P D hP hD0 habs
  refine ⟨E, H.support.card, Finset.card_pos.mpr (Polynomial.support_nonempty.mpr hH), ?_⟩
  intro n
  rw [hform, pow_add, supportCount_polynomial_mul_dilate_blocks
    (b ^ E) (pow_pos (by omega) E) H hshort]
  rw [supportCount_canonicalSeries_pow_eq_digitSupport b hb A hA0 n]

/-- Absorption preserves exactly the original digit-support growth exponent,
including exponent zero for a constant kernel. -/
theorem digitProduct_rational_powerSupportGrowth_of_absorbed
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b - 1) (P D : Polynomial K)
    (hP : P ≠ 0) (hD0 : D.coeff 0 ≠ 0)
    (habs : ∃ e, D ∣ P * kernelPrefix b A e) :
    HasPowerSupportGrowth (rationalMultiple P D (canonicalSeries b A))
      (digitSupportExponent b A) := by
  obtain ⟨E, t, ht, hexact⟩ := digitProduct_rational_exact_radix_counts
    b hb A hA0 hdegree P D hP hD0 habs
  have hs := one_le_radixDigitSupportCount b (by omega) A hA0
  have hsmall := radixDigitSupportCount_lt_of_degree b A hdegree
  exact hasPowerSupportGrowth_of_shifted_radix_counts _ b
    (radixDigitSupportCount b A) t E hb hs ht
    (digitSupportExponent b A)
    (radixDigitLogExponent_mem_Ico b hb A hA0 hsmall).1
    (rpow_radixLogExponent b (radixDigitSupportCount b A) hb hs) hexact

/-- Outside absorption the exact support-growth exponent is one. -/
theorem digitProduct_rational_linearGrowth_iff
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b - 1) (P D : Polynomial K)
    (hD0 : D.coeff 0 ≠ 0) :
    HasPowerSupportGrowth (rationalMultiple P D (canonicalSeries b A)) 1 ↔
      ∀ e, ¬ D ∣ P * kernelPrefix b A e := by
  rw [← hasPositiveLowerSupportDensity_iff_powerSupportGrowth_one]
  exact digitProduct_rational_positive_lower_density_iff b hb A hA0 hdegree P D hD0

/-- Complete growth classification: zero numerator, unchanged digit exponent
under absorption, or linear support growth outside absorption. -/
theorem digitProduct_rational_supportGrowth_classification
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b - 1) (P D : Polynomial K)
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
        digitProduct_rational_powerSupportGrowth_of_absorbed b hb A hA0 hdegree P D hP hD0 habs⟩)
    · have hnot : ∀ e, ¬ D ∣ P * kernelPrefix b A e := by simpa using habs
      exact Or.inr (Or.inr ⟨hnot,
        (digitProduct_rational_linearGrowth_iff b hb A hA0 hdegree P D hD0).2 hnot⟩)

/-- The digit exponent characterizes exactly the nonzero absorbed filters. -/
theorem digitProduct_rational_digitGrowth_iff
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b - 1) (P D : Polynomial K)
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
      (digitProduct_rational_linearGrowth_iff b hb A hA0 hdegree P D hD0).2 hnot
    have heq := hgrowth.exponent_eq hlinear
    have hlt : digitSupportExponent b A < 1 :=
      (radixDigitLogExponent_mem_Ico b hb A hA0
        (radixDigitSupportCount_lt_of_degree b A hdegree)).2
    linarith
  · rintro ⟨hP, habs⟩
    exact digitProduct_rational_powerSupportGrowth_of_absorbed
      b hb A hA0 hdegree P D hP hD0 habs

/-- Over a finite field, the exact digit growth has a single finite
divisibility test, without requiring a reduced fraction. -/
theorem finiteField_rational_digitGrowth_iff_finite_test
    {K : Type*} [Field K] [Fintype K]
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < Fintype.card K - 1)
    (P D : Polynomial K) (hD0 : D.coeff 0 ≠ 0) :
    HasPowerSupportGrowth
        (rationalMultiple P D (canonicalSeries (Fintype.card K) A))
        (digitSupportExponent (Fintype.card K) A) ↔
      P ≠ 0 ∧ D ∣ P * A ^ D.natDegree := by
  rw [digitProduct_rational_digitGrowth_iff (Fintype.card K)
    Fintype.one_lt_card A hA0 hdegree P D hD0]
  have hequiv :=
    (digitProduct_rational_density_zero_iff (Fintype.card K)
      Fintype.one_lt_card A hA0 hdegree P D hD0).symm.trans
      (finiteField_rational_density_zero_iff_finite_test A hA0 hdegree P D hD0)
  exact and_congr_right fun _ => hequiv

/-- Failure of the finite-field test gives exactly exponent one. -/
theorem finiteField_rational_linearGrowth_iff_finite_test
    {K : Type*} [Field K] [Fintype K]
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < Fintype.card K - 1)
    (P D : Polynomial K) (hD0 : D.coeff 0 ≠ 0) :
    HasPowerSupportGrowth
        (rationalMultiple P D (canonicalSeries (Fintype.card K) A)) 1 ↔
      ¬D ∣ P * A ^ D.natDegree := by
  rw [← hasPositiveLowerSupportDensity_iff_powerSupportGrowth_one]
  exact finiteField_rational_positive_lower_density_iff A hA0 hdegree P D hD0

/-- Equation-based interface for the normalized finite-field algebraic branch.
No separately supplied digit-product representation is needed. -/
theorem normalized_branch_rational_digitGrowth_iff_finite_test
    {K : Type*} [Field K] [Fintype K]
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < Fintype.card K - 1)
    (T : PowerSeries K) (hT0 : PowerSeries.coeff 0 T = 1)
    (hbranch : (A : PowerSeries K) * T ^ (Fintype.card K - 1) = 1)
    (P D : Polynomial K) (hD0 : D.coeff 0 ≠ 0) :
    HasPowerSupportGrowth (rationalMultiple P D T)
        (digitSupportExponent (Fintype.card K) A) ↔
      P ≠ 0 ∧ D ∣ P * A ^ D.natDegree := by
  rw [eq_canonicalSeries_of_normalized_branch A hA0 (by omega) T hT0 hbranch]
  exact finiteField_rational_digitGrowth_iff_finite_test A hA0 hdegree P D hD0

end IndependentZeroBlocks
