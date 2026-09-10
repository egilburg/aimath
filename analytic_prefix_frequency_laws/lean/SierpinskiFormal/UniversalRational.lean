import SierpinskiFormal.ArbitraryRational
import SierpinskiFormal.CompatibleKernels
import SierpinskiFormal.UniversalAuxiliaryField

set_option autoImplicit false

namespace IndependentZeroBlocks
open SierpinskiFormal
open scoped BigOperators

/-- For each positive step period, one radix works for all kernels.
Kernels with the same first positive degree use the same explicit seed. -/
theorem exists_universal_stepGeometric_radix
    {K : Type*} [Field K] [Fintype K] (m : ℕ) (hmpos : 0 < m) :
    ∃ Q : ℕ, 2 ≤ Q ∧ ∀ d : ℕ, 0 < d →
      1 ≤ commonSeed (ringChar K) Q d ∧
      ∀ A : Polynomial K, A.coeff 0 = 1 →
        A.natDegree < Fintype.card K - 1 → A.coeff d ≠ 0 →
        (∀ j, 0 < j → j < d → A.coeff j = 0) →
        HasSeedBlocks Q (commonSeed (ringChar K) Q d)
          (stepGeometric m * canonicalSeries (Fintype.card K) A) := by
  let p := ringChar K
  have hp : p.Prime := CharP.char_is_prime K p
  obtain ⟨e, s, hs, hm, hps, hcop⟩ :=
    exists_primePower_coprime_decomposition p m hp hmpos
  obtain ⟨L, hLfield, hLfintype, hLalg, zeta, hzeta, hevals⟩ :=
    exists_universal_auxiliary_field (K := K) s hs hps
  letI : Field L := hLfield
  letI : Fintype L := hLfintype
  letI : Algebra K L := hLalg
  letI : CharP L p := charP_of_injective_algebraMap' K p
  let r := radixExtensionExponent K L
  have hQ : 2 ≤ Fintype.card L := Fintype.one_lt_card
  have hrpos : 0 < r := by
    have hcard := card_eq_pred_mul_radixExtensionExponent_add_one K L
    by_contra h
    have hrzero : radixExtensionExponent K L = 0 := by change r = 0; omega
    rw [hrzero, Nat.mul_zero] at hcard
    omega
  refine ⟨Fintype.card L, hQ, ?_⟩
  intro d hdpos
  have hseedpos : 1 ≤ commonSeed p (Fintype.card L) d := by
    unfold commonSeed
    omega
  refine ⟨hseedpos, ?_⟩
  intro A hA0 hAdegree hdne hdprior
  have hApos : 0 < A.natDegree :=
    lt_of_lt_of_le hdpos (Polynomial.le_natDegree_of_ne_zero hdne)
  let B := (A.map (algebraMap K L)) ^ r
  let T := PowerSeries.map (algebraMap K L)
    (canonicalSeries (Fintype.card K) A)
  obtain ⟨hT0, _, hBdegree, hT⟩ :=
    mapped_canonicalSeries_radixExtension_data (L := L) A hA0 hApos hAdegree
  have hB0 : B.coeff 0 = 1 := by
    rw [show B.coeff 0 = algebraMap K L (A.coeff 0) by
      exact coeff_radixExtensionKernel_of_lt_card A hA0 hAdegree 0 Fintype.card_pos]
    simp [hA0]
  obtain ⟨hBdne, hBdprior⟩ :=
    radixExtensionKernel_first_degree (L := L) A hA0 hAdegree d hdne hdprior
  obtain ⟨_, _, hfilters⟩ :=
    commonSeed_periodic_filters_of_first_degree p hp.pos B T d hdpos
      hBdne hBdprior hBdegree hB0 hT0 hT
  have hperiod : Function.Periodic (divisorSelector (K := L) (p ^ e))
      (Fintype.card L ^ e) := by
    change Function.Periodic (fun n => if p ^ e ∣ n then (1 : L) else 0)
      (Fintype.card L ^ e)
    exact divisibility_indicator_period_cardPow (K := L) p e
  have hfilter : ∀ i ∈ Finset.range s,
      HasSeedBlocks (Fintype.card L) (commonSeed p (Fintype.card L) d)
        (PeriodicConvolution.weightedSeries
          (divisorSelector (K := L) (p ^ e)) (zeta ^ i) * T) := by
    intro i _
    apply hfilters (zeta ^ i) (pow_ne_zero i (hzeta.ne_zero (Nat.ne_of_gt hs)))
    · rcases hevals A i with hzero | hone
      · left
        change ((A.map (algebraMap K L)) ^ r).eval ((zeta ^ i)⁻¹) = 0
        rw [Polynomial.eval_pow, hzero, zero_pow (Nat.ne_of_gt hrpos)]
      · right
        change ((A.map (algebraMap K L)) ^ r).eval ((zeta ^ i)⁻¹) = 1
        simpa only [Polynomial.eval_pow, r, radixExtensionExponent] using hone
    · exact hperiod
  have hsum := HasSeedBlocks.sum (Finset.range s)
    (fun i => PeriodicConvolution.weightedSeries
      (divisorSelector (K := L) (p ^ e)) (zeta ^ i) * T) hfilter
  have hsCast : (s : L) ≠ 0 := by
    intro hz
    exact hps ((CharP.cast_eq_zero_iff L p s).mp hz)
  have hfiltered : HasSeedBlocks (Fintype.card L) (commonSeed p (Fintype.card L) d)
      (stepGeometric m * T) := by
    rw [hm, stepGeometric_mul_eq_sum_weightedSeries_of_isPrimitiveRoot
      (p ^ e) s zeta hcop hzeta hsCast, mul_assoc, Finset.sum_mul]
    simpa using hsum.polynomial_mul (Polynomial.C (s : L)⁻¹)
  apply HasSeedBlocks.of_map (algebraMap K L) (algebraMap K L).injective
  simpa only [map_mul, map_stepGeometric] using hfiltered

/-- A fixed denominator admits one radix, independent of both the kernel
and the numerator. The seed depends only on that radix and the first
positive degree of the kernel; the finite left trim may depend on the input. -/
theorem exists_universal_rational_denominator_radix
    {K : Type*} [Field K] [Fintype K]
    (D : Polynomial K) (hD : D.coeff 0 ≠ 0) :
    ∃ Q : ℕ, 2 ≤ Q ∧ ∀ d : ℕ, 0 < d →
      1 ≤ commonSeed (ringChar K) Q d ∧
      ∀ A : Polynomial K, A.coeff 0 = 1 →
        A.natDegree < Fintype.card K - 1 → A.coeff d ≠ 0 →
        (∀ j, 0 < j → j < d → A.coeff j = 0) →
        ∀ P : Polynomial K,
          HasSeedBlocks Q (commonSeed (ringChar K) Q d)
            (rationalMultiple P D (canonicalSeries (Fintype.card K) A)) := by
  obtain ⟨m, E, hmpos, hE⟩ :=
    exists_denominatorInverse_eq_polynomial_stepGeometric D hD
  obtain ⟨Q, hQ, hstep⟩ := exists_universal_stepGeometric_radix (K := K) m hmpos
  refine ⟨Q, hQ, ?_⟩
  intro d hdpos
  obtain ⟨hseed, hstepd⟩ := hstep d hdpos
  refine ⟨hseed, ?_⟩
  intro A hA0 hAdegree hdne hdprior P
  have hrep : rationalMultiple P D (canonicalSeries (Fintype.card K) A) =
      ((P * E : Polynomial K) : PowerSeries K) *
        (stepGeometric m * canonicalSeries (Fintype.card K) A) := by
    rw [← eq_rationalMultiple_of_denominator P D
      (canonicalSeries (Fintype.card K) A)
      (rationalMultiplierSeries P D (canonicalSeries (Fintype.card K) A) hD) hD
      (coe_mul_rationalMultiplierSeries P D (canonicalSeries (Fintype.card K) A) hD)]
    unfold rationalMultiplierSeries
    rw [hE, Polynomial.coe_mul]
    ring
  rw [hrep]
  exact (hstepd A hA0 hAdegree hdne hdprior).polynomial_mul (P * E)

end IndependentZeroBlocks
