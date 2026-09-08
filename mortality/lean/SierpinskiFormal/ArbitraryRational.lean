import SierpinskiFormal.AuxiliaryField
import SierpinskiFormal.RadixExtension
import SierpinskiFormal.PrimePeriod
import SierpinskiFormal.FourierBridge
import SierpinskiFormal.KernelPeriodic

set_option autoImplicit false

namespace IndependentZeroBlocks
open SierpinskiFormal
open scoped BigOperators

@[simp] theorem map_stepGeometric {K L : Type*} [Field K] [Field L]
    (f : K →+* L) (m : ℕ) :
    PowerSeries.map f (stepGeometric (K := K) m) = stepGeometric m := by
  ext n
  simp [PowerSeries.coeff_map, stepGeometric]

/-- Arbitrary positive step-geometric filters admit a common descendant
zero seed after a finite extension and radix enlargement.  The conclusion
is descended back to the original coefficient field. -/
theorem exists_stepGeometric_seed
    {K : Type*} [Field K] [Fintype K]
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hApos : 0 < A.natDegree) (hAdegree : A.natDegree < Fintype.card K - 1)
    (m : ℕ) (hmpos : 0 < m) :
    ∃ Q seed : ℕ, 2 ≤ Q ∧ 1 ≤ seed ∧
      HasSeedBlocks Q seed
        (stepGeometric m * canonicalSeries (Fintype.card K) A) := by
  let p := ringChar K
  have hp : p.Prime := CharP.char_is_prime K p
  obtain ⟨e, s, hs, hm, hps, hcop⟩ :=
    exists_primePower_coprime_decomposition p m hp hmpos
  obtain ⟨L, hLfield, hLfintype, hLalg, zeta, hzeta, hevals⟩ :=
    exists_auxiliary_field_with_eval_zero_or_one A s hs hps
  letI : Field L := hLfield
  letI : Fintype L := hLfintype
  letI : Algebra K L := hLalg
  letI : CharP L p := charP_of_injective_algebraMap' K p
  let r := radixExtensionExponent K L
  let B := (A.map (algebraMap K L)) ^ r
  let T := PowerSeries.map (algebraMap K L)
    (canonicalSeries (Fintype.card K) A)
  have hQ : 2 ≤ Fintype.card L := Fintype.one_lt_card
  have hrpos : 0 < r := by
    have hcard := card_eq_pred_mul_radixExtensionExponent_add_one K L
    by_contra h
    have hrzero : radixExtensionExponent K L = 0 := by change r = 0; omega
    rw [hrzero, Nat.mul_zero] at hcard
    omega
  obtain ⟨hT0, hBpos, hBdegree, hT⟩ :=
    mapped_canonicalSeries_radixExtension_data (L := L) A hA0 hApos hAdegree
  have hB0 : B.coeff 0 = 1 := by
    rw [show B.coeff 0 = algebraMap K L (A.coeff 0) by
      exact coeff_radixExtensionKernel_of_lt_card A hA0 hAdegree 0 Fintype.card_pos]
    simp [hA0]
  obtain ⟨seed, hseed, hbare, hfilters⟩ :=
    exists_common_seed_periodic_filters p hp.pos B T hBpos hBdegree hB0 hT0 hT
  have hperiod : Function.Periodic (divisorSelector (K := L) (p ^ e))
      (Fintype.card L ^ e) := by
    change Function.Periodic (fun n => if p ^ e ∣ n then (1 : L) else 0)
      (Fintype.card L ^ e)
    exact divisibility_indicator_period_cardPow (K := L) p e
  have hfilter : ∀ i ∈ Finset.range s,
      HasSeedBlocks (Fintype.card L) seed
        (PeriodicConvolution.weightedSeries
          (divisorSelector (K := L) (p ^ e)) (zeta ^ i) * T) := by
    intro i _
    apply hfilters (zeta ^ i) (pow_ne_zero i (hzeta.ne_zero (Nat.ne_of_gt hs)))
    · rcases hevals i with hzero | hone
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
  have hfiltered : HasSeedBlocks (Fintype.card L) seed (stepGeometric m * T) := by
    rw [hm, stepGeometric_mul_eq_sum_weightedSeries_of_isPrimitiveRoot
      (p ^ e) s zeta hcop hzeta hsCast, mul_assoc, Finset.sum_mul]
    simpa using hsum.polynomial_mul (Polynomial.C (s : L)⁻¹)
  refine ⟨Fintype.card L, seed, hQ, hseed, ?_⟩
  apply HasSeedBlocks.of_map (algebraMap K L) (algebraMap K L).injective
  simpa only [map_mul, map_stepGeometric] using hfiltered

/-- For a fixed arbitrary denominator, one descendant seed works for all
polynomial numerators.  The finite left trim may depend on the numerator. -/
theorem exists_rational_denominator_seed
    {K : Type*} [Field K] [Fintype K]
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hApos : 0 < A.natDegree) (hAdegree : A.natDegree < Fintype.card K - 1)
    (D : Polynomial K) (hD : D.coeff 0 ≠ 0) :
    ∃ Q seed : ℕ, 2 ≤ Q ∧ 1 ≤ seed ∧
      ∀ P : Polynomial K, HasSeedBlocks Q seed
        (rationalMultiple P D (canonicalSeries (Fintype.card K) A)) := by
  obtain ⟨m, E, hmpos, hE⟩ :=
    exists_denominatorInverse_eq_polynomial_stepGeometric D hD
  obtain ⟨Q, seed, hQ, hseed, hstep⟩ :=
    exists_stepGeometric_seed A hA0 hApos hAdegree m hmpos
  refine ⟨Q, seed, hQ, hseed, ?_⟩
  intro P
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
  exact hstep.polynomial_mul (P * E)

/-- The unconditional finite-field rational-multiplier theorem. -/
theorem arbitrary_rational_multiplier_zeroBlocks
    {K : Type*} [Field K] [Fintype K]
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hApos : 0 < A.natDegree) (hAdegree : A.natDegree < Fintype.card K - 1)
    (P D : Polynomial K) (hD : D.coeff 0 ≠ 0) :
    HasArbitrarilyLongZeroBlocks (fun n => PowerSeries.coeff n
      (rationalMultiple P D (canonicalSeries (Fintype.card K) A))) := by
  obtain ⟨Q, seed, hQ, hseed, hzero⟩ :=
    exists_rational_denominator_seed A hA0 hApos hAdegree D hD
  exact (hzero P).zeroBlocks hQ hseed

/-- Every normalized algebraic branch in the kernel degree range is the
canonical series constructed from its digits. -/
theorem eq_canonicalSeries_of_normalized_branch
    {K : Type*} [Field K] [Fintype K]
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < Fintype.card K)
    (T : PowerSeries K) (hT0 : PowerSeries.coeff 0 T = 1)
    (hbranch : (A : PowerSeries K) * T ^ (Fintype.card K - 1) = 1) :
    T = canonicalSeries (Fintype.card K) A := by
  have hq : 2 ≤ Fintype.card K := Fintype.one_lt_card
  have hcard : Fintype.card K = (Fintype.card K - 1) * 1 + 1 := by omega
  have hbranch' : (A : PowerSeries K) ^ 1 * T ^ (Fintype.card K - 1) = 1 := by
    simpa using hbranch
  have hdilation : T = (A : PowerSeries K) * dilate (Fintype.card K) T := by
    simpa using finiteField_dilation_equation A T 1 (Fintype.card K - 1) 1 hcard hbranch'
  exact eq_canonicalSeries_of_dilation_equation _ hq A hA0 hdegree T hT0 hdilation

theorem existsUnique_normalized_algebraic_branch
    {K : Type*} [Field K] [Fintype K]
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < Fintype.card K) :
    ∃! T : PowerSeries K, PowerSeries.coeff 0 T = 1 ∧
      (A : PowerSeries K) * T ^ (Fintype.card K - 1) = 1 := by
  refine ⟨canonicalSeries (Fintype.card K) A,
    ⟨coeff_zero_canonicalSeries _ _, canonicalSeries_finiteField_branch A hA0 hdegree⟩, ?_⟩
  intro T hT
  exact eq_canonicalSeries_of_normalized_branch A hA0 hdegree T hT.1 hT.2

/-- A representation-independent version: the algebraic branch and rational
product are characterized by their exact defining equations. -/
theorem rational_multiplier_zeroBlocks_of_equations
    {K : Type*} [Field K] [Fintype K]
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hApos : 0 < A.natDegree) (hAdegree : A.natDegree < Fintype.card K - 1)
    (P D : Polynomial K) (hD : D.coeff 0 ≠ 0)
    (T U : PowerSeries K) (hT0 : PowerSeries.coeff 0 T = 1)
    (hbranch : (A : PowerSeries K) * T ^ (Fintype.card K - 1) = 1)
    (hproduct : (D : PowerSeries K) * U = (P : PowerSeries K) * T) :
    HasArbitrarilyLongZeroBlocks (fun n => PowerSeries.coeff n U) := by
  have hq : 2 ≤ Fintype.card K := Fintype.one_lt_card
  rw [eq_rationalMultiple_of_denominator P D T U hD hproduct,
    eq_canonicalSeries_of_normalized_branch A hA0 (by omega) T hT0 hbranch]
  exact arbitrary_rational_multiplier_zeroBlocks A hA0 hApos hAdegree P D hD

end IndependentZeroBlocks

#print axioms IndependentZeroBlocks.arbitrary_rational_multiplier_zeroBlocks
#print axioms IndependentZeroBlocks.rational_multiplier_zeroBlocks_of_equations
