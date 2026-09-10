import SierpinskiFormal.UniversalRational
import SierpinskiFormal.SeedFamilies

set_option autoImplicit false

namespace IndependentZeroBlocks
open SierpinskiFormal
open scoped BigOperators

/-- The radix and seed can be chosen from the denominators and the shared
first positive degree, before choosing any of the compatible kernels or
polynomial numerators. -/
theorem exists_simultaneous_rational_seed
    {K ι : Type*} [Field K] [Fintype K] [Fintype ι]
    (d : ℕ) (hdpos : 0 < d)
    (D : ι → Polynomial K) (hD : ∀ i, (D i).coeff 0 ≠ 0) :
    ∃ Q seed : ℕ, 2 ≤ Q ∧ 1 ≤ seed ∧
      ∀ A : ι → Polynomial K,
        (∀ i, (A i).coeff 0 = 1) →
        (∀ i, (A i).natDegree < Fintype.card K - 1) →
        (∀ i, (A i).coeff d ≠ 0) →
        (∀ i j, 0 < j → j < d → (A i).coeff j = 0) →
        ∀ P : ι → Polynomial K, ∀ i,
          HasSeedBlocks Q seed
            (rationalMultiple (P i) (D i)
              (canonicalSeries (Fintype.card K) (A i))) := by
  obtain ⟨Q, hQ, hradix⟩ := exists_universal_rational_denominator_radix
    (commonDenominator D) (commonDenominator_coeff_zero_ne_zero D hD)
  obtain ⟨hseed, hkernel⟩ := hradix d hdpos
  refine ⟨Q, commonSeed (ringChar K) Q d, hQ, hseed, ?_⟩
  intro A hA0 hAdegree hdne hdprior P i
  rw [rationalMultiple_eq_commonDenominator P D
    (fun i => canonicalSeries (Fintype.card K) (A i)) hD i]
  exact hkernel (A i) (hA0 i) (hAdegree i) (hdne i) (hdprior i)
    (commonNumerator P D i)

/-- Arbitrary rational multiples of finitely many compatible normalized
branches have arbitrarily long, arbitrarily late simultaneous zero blocks. -/
theorem simultaneous_arbitrary_rational_zeroBlocks
    {K ι : Type*} [Field K] [Fintype K] [Fintype ι]
    (A P D : ι → Polynomial K) (d : ℕ) (hdpos : 0 < d)
    (hA0 : ∀ i, (A i).coeff 0 = 1)
    (hAdegree : ∀ i, (A i).natDegree < Fintype.card K - 1)
    (hdne : ∀ i, (A i).coeff d ≠ 0)
    (hdprior : ∀ i j, 0 < j → j < d → (A i).coeff j = 0)
    (hD : ∀ i, (D i).coeff 0 ≠ 0) :
    ∀ length start, ∃ N, start ≤ N ∧ ∀ i, ∀ j, j < length →
      PowerSeries.coeff (N + j)
        (rationalMultiple (P i) (D i)
          (canonicalSeries (Fintype.card K) (A i))) = 0 := by
  obtain ⟨Q, seed, hQ, hseed, hfamily⟩ :=
    exists_simultaneous_rational_seed d hdpos D hD
  exact has_simultaneous_zeroBlocks _ (hfamily A hA0 hAdegree hdne hdprior P) hQ hseed

/-- Equation-based formulation: the normalized branches and rational
multiples may be supplied by their defining identities. -/
theorem simultaneous_rational_zeroBlocks_of_equations
    {K ι : Type*} [Field K] [Fintype K] [Fintype ι]
    (A P D : ι → Polynomial K) (T U : ι → PowerSeries K)
    (d : ℕ) (hdpos : 0 < d)
    (hA0 : ∀ i, (A i).coeff 0 = 1)
    (hAdegree : ∀ i, (A i).natDegree < Fintype.card K - 1)
    (hdne : ∀ i, (A i).coeff d ≠ 0)
    (hdprior : ∀ i j, 0 < j → j < d → (A i).coeff j = 0)
    (hD : ∀ i, (D i).coeff 0 ≠ 0)
    (hT0 : ∀ i, PowerSeries.coeff 0 (T i) = 1)
    (hbranch : ∀ i, (A i : PowerSeries K) * (T i) ^ (Fintype.card K - 1) = 1)
    (hU : ∀ i, (D i : PowerSeries K) * U i = (P i : PowerSeries K) * T i) :
    ∀ length start, ∃ N, start ≤ N ∧ ∀ i, ∀ j, j < length →
      PowerSeries.coeff (N + j) (U i) = 0 := by
  have hTeq (i : ι) : T i = canonicalSeries (Fintype.card K) (A i) :=
    eq_canonicalSeries_of_normalized_branch (A i) (hA0 i)
      (lt_trans (hAdegree i) (Nat.sub_lt Fintype.card_pos (by decide)))
      (T i) (hT0 i) (hbranch i)
  have hUeq (i : ι) : U i =
      rationalMultiple (P i) (D i) (canonicalSeries (Fintype.card K) (A i)) := by
    rw [eq_rationalMultiple_of_denominator (P i) (D i) (T i) (U i) (hD i) (hU i),
      hTeq i]
  intro length start
  obtain ⟨N, hN, hzero⟩ :=
    simultaneous_arbitrary_rational_zeroBlocks A P D d hdpos hA0 hAdegree
      hdne hdprior hD length start
  refine ⟨N, hN, ?_⟩
  intro i j hj
  rw [hUeq i]
  exact hzero i j hj

/-- Every finite sum of arbitrary rational multiples from a compatible
family inherits the common zero intervals. -/
theorem compatible_rational_sum_zeroBlocks
    {K ι : Type*} [Field K] [Fintype K] [Fintype ι]
    (A P D : ι → Polynomial K) (d : ℕ) (hdpos : 0 < d)
    (hA0 : ∀ i, (A i).coeff 0 = 1)
    (hAdegree : ∀ i, (A i).natDegree < Fintype.card K - 1)
    (hdne : ∀ i, (A i).coeff d ≠ 0)
    (hdprior : ∀ i j, 0 < j → j < d → (A i).coeff j = 0)
    (hD : ∀ i, (D i).coeff 0 ≠ 0) :
    HasArbitrarilyLongZeroBlocks (fun n => PowerSeries.coeff n
      (∑ i : ι, rationalMultiple (P i) (D i)
        (canonicalSeries (Fintype.card K) (A i)))) := by
  obtain ⟨Q, seed, hQ, hseed, hfamily⟩ :=
    exists_simultaneous_rational_seed d hdpos D hD
  apply HasSeedBlocks.zeroBlocks _ hQ hseed
  exact HasSeedBlocks.sum Finset.univ _
    (fun i _ => hfamily A hA0 hAdegree hdne hdprior P i)

end IndependentZeroBlocks
