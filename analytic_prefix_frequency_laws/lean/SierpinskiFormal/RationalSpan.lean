import SierpinskiFormal.SimultaneousRational
import SierpinskiFormal.DenominatorShift

set_option autoImplicit false

namespace IndependentZeroBlocks
open SierpinskiFormal
open scoped BigOperators

/-- Regular rational division distributes over a finite polynomial
combination of power series. -/
theorem rationalMultiple_one_sum
    {K ι : Type*} [Field K] [Fintype ι]
    (P : ι → Polynomial K) (E : Polynomial K) (T : ι → PowerSeries K) :
    rationalMultiple 1 E (∑ i, (P i : PowerSeries K) * T i) =
      ∑ i, rationalMultiple (P i) E (T i) := by
  unfold rationalMultiple
  simp only [Polynomial.coe_one, one_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Every power series in the rational span of compatible canonical
branches has long late zero blocks. A cleared denominator need only be
nonzero: poles at the origin may cancel across the combination. -/
theorem compatible_rational_span_zeroBlocks
    {K ι : Type*} [Field K] [Fintype K] [Fintype ι]
    (A P : ι → Polynomial K) (D : Polynomial K) (U : PowerSeries K)
    (d : ℕ) (hdpos : 0 < d)
    (hA0 : ∀ i, (A i).coeff 0 = 1)
    (hAdegree : ∀ i, (A i).natDegree < Fintype.card K - 1)
    (hdne : ∀ i, (A i).coeff d ≠ 0)
    (hdprior : ∀ i j, 0 < j → j < d → (A i).coeff j = 0)
    (hD : D ≠ 0)
    (hDU : (D : PowerSeries K) * U =
      ∑ i, (P i : PowerSeries K) * canonicalSeries (Fintype.card K) (A i)) :
    HasArbitrarilyLongZeroBlocks (fun n => PowerSeries.coeff n U) := by
  obtain ⟨k, E, _, hE0, hshift⟩ :=
    exists_shift_rationalMultiple_of_denominator D U _ hD hDU
  apply hasArbitrarilyLongZeroBlocks_of_X_pow_mul k U
  rw [hshift, rationalMultiple_one_sum]
  exact compatible_rational_sum_zeroBlocks A P (fun _ => E) d hdpos
    hA0 hAdegree hdne hdprior (fun _ => hE0)

/-- Normalization of a branch already forces the kernel's constant term
to be one, so that condition need not be supplied separately. -/
theorem kernel_coeff_zero_of_normalized_branch
    {K : Type*} [Field K] [Fintype K] (A : Polynomial K) (T : PowerSeries K)
    (hT0 : PowerSeries.coeff 0 T = 1)
    (hbranch : (A : PowerSeries K) * T ^ (Fintype.card K - 1) = 1) :
    A.coeff 0 = 1 := by
  have h := congrArg (PowerSeries.coeff 0) hbranch
  have hTconst : PowerSeries.constantCoeff T = 1 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hT0
  simpa [PowerSeries.coeff_zero_eq_constantCoeff, hTconst] using h

/-- Equation-based rational-span theorem, including origin-pole
cancellation. The only denominator hypothesis is nonvanishing. -/
theorem normalized_branch_rational_span_zeroBlocks
    {K ι : Type*} [Field K] [Fintype K] [Fintype ι]
    (A P : ι → Polynomial K) (T : ι → PowerSeries K)
    (D : Polynomial K) (U : PowerSeries K) (d : ℕ) (hdpos : 0 < d)
    (hAdegree : ∀ i, (A i).natDegree < Fintype.card K - 1)
    (hdne : ∀ i, (A i).coeff d ≠ 0)
    (hdprior : ∀ i j, 0 < j → j < d → (A i).coeff j = 0)
    (hT0 : ∀ i, PowerSeries.coeff 0 (T i) = 1)
    (hbranch : ∀ i, (A i : PowerSeries K) * (T i) ^ (Fintype.card K - 1) = 1)
    (hD : D ≠ 0)
    (hDU : (D : PowerSeries K) * U = ∑ i, (P i : PowerSeries K) * T i) :
    HasArbitrarilyLongZeroBlocks (fun n => PowerSeries.coeff n U) := by
  have hA0 (i : ι) : (A i).coeff 0 = 1 :=
    kernel_coeff_zero_of_normalized_branch (A i) (T i) (hT0 i) (hbranch i)
  have hTeq (i : ι) : T i = canonicalSeries (Fintype.card K) (A i) :=
    eq_canonicalSeries_of_normalized_branch (A i) (hA0 i)
      (lt_trans (hAdegree i) (Nat.sub_lt Fintype.card_pos (by decide)))
      (T i) (hT0 i) (hbranch i)
  apply compatible_rational_span_zeroBlocks A P D U d hdpos
    hA0 hAdegree hdne hdprior hD
  simpa only [hTeq] using hDU

end IndependentZeroBlocks
