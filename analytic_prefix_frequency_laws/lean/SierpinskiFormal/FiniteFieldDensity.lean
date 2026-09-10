import SierpinskiFormal.RationalDensityCriterion
import SierpinskiFormal.FiniteFieldPrefixSaturation
import SierpinskiFormal.ArbitraryRational

set_option autoImplicit false

/-! # Exact finite-field density classification with a single divisibility test -/
namespace IndependentZeroBlocks

theorem finiteField_rational_density_zero_iff
    {K : Type*} [Field K] [Fintype K]
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < Fintype.card K - 1)
    (P D : Polynomial K) (hD0 : D.coeff 0 ≠ 0) :
    HasZeroSupportDensity
        (rationalMultiple P D (canonicalSeries (Fintype.card K) A)) ↔
      ∃ N : ℕ, D ∣ P * A ^ N :=
  (digitProduct_rational_density_zero_iff (Fintype.card K) Fintype.one_lt_card
    A hA0 hdegree P D hD0).trans
    exists_dvd_mul_kernelPrefix_iff_exists_dvd_mul_pow

/-- A single finite algebraic test characterizes density zero. Fractions need
not be reduced, and the numerator may be zero. -/
theorem finiteField_rational_density_zero_iff_finite_test
    {K : Type*} [Field K] [Fintype K]
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < Fintype.card K - 1)
    (P D : Polynomial K) (hD0 : D.coeff 0 ≠ 0) :
    HasZeroSupportDensity
        (rationalMultiple P D (canonicalSeries (Fintype.card K) A)) ↔
      D ∣ P * A ^ D.natDegree := by
  have hD : D ≠ 0 := by intro h; apply hD0; simp [h]
  exact (finiteField_rational_density_zero_iff A hA0 hdegree P D hD0).trans
    (SierpinskiFormal.exists_dvd_mul_pow_iff_dvd_mul_pow_natDegree hD)

/-- Failure of the finite test is exactly positive lower support density;
existence of an ordinary density is not an assumption or a conclusion. -/
theorem finiteField_rational_positive_lower_density_iff
    {K : Type*} [Field K] [Fintype K]
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < Fintype.card K - 1)
    (P D : Polynomial K) (hD0 : D.coeff 0 ≠ 0) :
    HasPositiveLowerSupportDensity
        (rationalMultiple P D (canonicalSeries (Fintype.card K) A)) ↔
      ¬ D ∣ P * A ^ D.natDegree := by
  constructor
  · intro hp hd
    exact hp.not_zero ((finiteField_rational_density_zero_iff_finite_test
      A hA0 hdegree P D hD0).2 hd)
  · intro hnot
    apply digitProduct_rational_positive_lower_density
      (Fintype.card K) Fintype.one_lt_card A hA0 hdegree P D hD0
    intro e he
    have hz := (digitProduct_rational_density_zero_iff (Fintype.card K)
      Fintype.one_lt_card A hA0 hdegree P D hD0).2 ⟨e, he⟩
    exact hnot ((finiteField_rational_density_zero_iff_finite_test
      A hA0 hdegree P D hD0).1 hz)

/-- Equation-based form for the normalized algebraic branch. Its existence
and uniqueness are already proved by the canonical construction. -/
theorem normalized_branch_rational_density_zero_iff_finite_test
    {K : Type*} [Field K] [Fintype K]
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < Fintype.card K - 1)
    (T : PowerSeries K) (hT0 : PowerSeries.coeff 0 T = 1)
    (hbranch : (A : PowerSeries K) * T ^ (Fintype.card K - 1) = 1)
    (P D : Polynomial K) (hD0 : D.coeff 0 ≠ 0) :
    HasZeroSupportDensity (rationalMultiple P D T) ↔
      D ∣ P * A ^ D.natDegree := by
  rw [eq_canonicalSeries_of_normalized_branch A hA0 (by omega) T hT0 hbranch]
  exact finiteField_rational_density_zero_iff_finite_test A hA0 hdegree P D hD0

/-- For a reduced fraction the numerator drops out of the finite test. -/
theorem finiteField_rational_density_zero_iff_of_isCoprime
    {K : Type*} [Field K] [Fintype K]
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < Fintype.card K - 1)
    (P D : Polynomial K) (hD0 : D.coeff 0 ≠ 0) (hPD : IsCoprime P D) :
    HasZeroSupportDensity
        (rationalMultiple P D (canonicalSeries (Fintype.card K) A)) ↔
      D ∣ A ^ D.natDegree :=
  (finiteField_rational_density_zero_iff_finite_test A hA0 hdegree P D hD0).trans
    (SierpinskiFormal.dvd_mul_pow_iff_dvd_pow_of_isCoprime hPD)

end IndependentZeroBlocks
