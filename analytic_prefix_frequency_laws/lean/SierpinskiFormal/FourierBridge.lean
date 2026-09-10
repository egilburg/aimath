import SierpinskiFormal.RationalBridge
import SierpinskiFormal.PeriodicConvolution
import Mathlib.Algebra.Field.GeomSum
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

set_option autoImplicit false

/-!
# Fourier decomposition of step-geometric coefficients

If `H` and `s` are coprime and `ζ` is a primitive `s`th root of unity, the
indicator of divisibility by `H * s` is a finite Fourier sum.  Each summand is
an exponential twist of the `H`-periodic divisibility indicator.  In the
finite-field application, `H` is a power of the characteristic and `s` is
prime to the characteristic.

The primitive-root hypothesis is stated through its exact computational
interface `ζ ^ n = 1 ↔ s ∣ n`.  A caller with mathlib's `IsPrimitiveRoot ζ s`
can supply this using `IsPrimitiveRoot.pow_eq_one_iff_dvd`.
-/

namespace SierpinskiFormal

open scoped BigOperators

/-- The coefficient-valued indicator of multiples of `H`. -/
def divisorSelector {K : Type*} [Zero K] [One K] (H : ℕ) : ℕ → K :=
  fun n => if H ∣ n then 1 else 0

@[simp] theorem divisorSelector_apply
    {K : Type*} [Zero K] [One K] (H n : ℕ) :
    divisorSelector (K := K) H n = if H ∣ n then 1 else 0 := rfl

theorem divisorSelector_periodic
    {K : Type*} [Zero K] [One K] (H : ℕ) :
    Function.Periodic (divisorSelector (K := K) H) H := by
  intro n
  simp only [divisorSelector_apply, Nat.dvd_add_self_right]

/-- Geometric-sum orthogonality from the computational primitive-root
property. -/
theorem primitiveRoot_sum_pow
    {K : Type*} [Field K] (s : ℕ) (zeta : K)
    (hprimitive : ∀ n : ℕ, zeta ^ n = 1 ↔ s ∣ n) (n : ℕ) :
    (∑ i ∈ Finset.range s, (zeta ^ i) ^ n) =
      if s ∣ n then (s : K) else 0 := by
  by_cases hsn : s ∣ n
  · have hz : zeta ^ n = 1 := (hprimitive n).2 hsn
    rw [if_pos hsn]
    calc
      (∑ i ∈ Finset.range s, (zeta ^ i) ^ n) =
          ∑ i ∈ Finset.range s, (1 : K) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← pow_mul, Nat.mul_comm i n, pow_mul, hz, one_pow]
      _ = (s : K) := by simp
  · have hz_ne : zeta ^ n ≠ 1 := fun h => hsn ((hprimitive n).1 h)
    have hz_s : (zeta ^ n) ^ s = 1 := by
      rw [← pow_mul, Nat.mul_comm n s, pow_mul]
      have hzeta_s : zeta ^ s = 1 := (hprimitive s).2 (dvd_refl s)
      rw [hzeta_s, one_pow]
    have hgeom : (∑ i ∈ Finset.range s, (zeta ^ n) ^ i) = 0 := by
      have hmul := geom_sum_mul (zeta ^ n) s
      rw [hz_s, sub_self] at hmul
      exact (mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr hz_ne)
    rw [if_neg hsn]
    calc
      (∑ i ∈ Finset.range s, (zeta ^ i) ^ n) =
          ∑ i ∈ Finset.range s, (zeta ^ n) ^ i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← pow_mul, Nat.mul_comm i n, pow_mul]
      _ = 0 := hgeom

/-- Normalized root-of-unity orthogonality. -/
theorem primitiveRoot_fourier_indicator
    {K : Type*} [Field K] (s : ℕ) (zeta : K)
    (hprimitive : ∀ n : ℕ, zeta ^ n = 1 ↔ s ∣ n)
    (hs_cast : (s : K) ≠ 0) (n : ℕ) :
    (if s ∣ n then (1 : K) else 0) =
      (s : K)⁻¹ * ∑ i ∈ Finset.range s, (zeta ^ i) ^ n := by
  rw [primitiveRoot_sum_pow s zeta hprimitive n]
  split_ifs <;> simp [hs_cast]

/-- Divisibility by a product of coprime numbers is the conjunction of the
two divisibility conditions. -/
theorem coprime_mul_dvd_iff
    {H s n : ℕ} (hcoprime : H.Coprime s) :
    H * s ∣ n ↔ H ∣ n ∧ s ∣ n := by
  constructor
  · intro h
    exact ⟨(dvd_mul_right H s).trans h, (dvd_mul_left s H).trans h⟩
  · rintro ⟨hH, hs⟩
    exact hcoprime.mul_dvd_of_dvd_of_dvd hH hs

/-- Fourier decomposition of the `H*s` divisibility indicator.  Every
summand is an exponential `(zeta^i)^n` multiplied by the same `H`-periodic
selector. -/
theorem coprime_mul_fourier_indicator
    {K : Type*} [Field K] (H s : ℕ) (zeta : K)
    (hcoprime : H.Coprime s)
    (hprimitive : ∀ n : ℕ, zeta ^ n = 1 ↔ s ∣ n)
    (hs_cast : (s : K) ≠ 0) (n : ℕ) :
    (if H * s ∣ n then (1 : K) else 0) =
      ∑ i ∈ Finset.range s,
        (s : K)⁻¹ * divisorSelector (K := K) H n * (zeta ^ i) ^ n := by
  simp only [coprime_mul_dvd_iff hcoprime]
  by_cases hH : H ∣ n
  · simp only [hH, true_and, if_true, divisorSelector_apply]
    rw [← Finset.mul_sum]
    simpa using primitiveRoot_fourier_indicator s zeta hprimitive hs_cast n
  · simp [hH]

/-- Coefficients of `stepGeometric (H*s)` are a finite sum of geometric
twists of one `H`-periodic weight. -/
theorem coeff_stepGeometric_mul_eq_fourier
    {K : Type*} [Field K] (H s : ℕ) (zeta : K)
    (hcoprime : H.Coprime s)
    (hprimitive : ∀ n : ℕ, zeta ^ n = 1 ↔ s ∣ n)
    (hs_cast : (s : K) ≠ 0) (n : ℕ) :
    PowerSeries.coeff n (stepGeometric (H * s)) =
      ∑ i ∈ Finset.range s,
        (s : K)⁻¹ * divisorSelector (K := K) H n * (zeta ^ i) ^ n := by
  simp only [stepGeometric, PowerSeries.coeff_mk]
  exact coprime_mul_fourier_indicator H s zeta hcoprime hprimitive hs_cast n

/-- Power-series form of the Fourier decomposition.  This is the interface
used by the periodic-convolution zero-block theorem. -/
theorem stepGeometric_mul_eq_sum_weightedSeries
    {K : Type*} [Field K] (H s : ℕ) (zeta : K)
    (hcoprime : H.Coprime s)
    (hprimitive : ∀ n : ℕ, zeta ^ n = 1 ↔ s ∣ n)
    (hs_cast : (s : K) ≠ 0) :
    stepGeometric (K := K) (H * s) =
      PowerSeries.C (s : K)⁻¹ *
        ∑ i ∈ Finset.range s,
          PeriodicConvolution.weightedSeries
            (divisorSelector (K := K) H) (zeta ^ i) := by
  ext n
  rw [coeff_stepGeometric_mul_eq_fourier H s zeta hcoprime hprimitive hs_cast]
  simp only [map_mul, PowerSeries.coeff_C_mul,
    map_sum, PeriodicConvolution.coeff_weightedSeries]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The preceding power-series identity with mathlib's standard primitive
root predicate. -/
theorem stepGeometric_mul_eq_sum_weightedSeries_of_isPrimitiveRoot
    {K : Type*} [Field K] (H s : ℕ) (zeta : K)
    (hcoprime : H.Coprime s) (hprimitive : IsPrimitiveRoot zeta s)
    (hs_cast : (s : K) ≠ 0) :
    stepGeometric (K := K) (H * s) =
      PowerSeries.C (s : K)⁻¹ *
        ∑ i ∈ Finset.range s,
          PeriodicConvolution.weightedSeries
            (divisorSelector (K := K) H) (zeta ^ i) :=
  stepGeometric_mul_eq_sum_weightedSeries H s zeta hcoprime
    hprimitive.pow_eq_one_iff_dvd hs_cast

end SierpinskiFormal

#print axioms SierpinskiFormal.coprime_mul_fourier_indicator
#print axioms SierpinskiFormal.coeff_stepGeometric_mul_eq_fourier
#print axioms SierpinskiFormal.stepGeometric_mul_eq_sum_weightedSeries
#print axioms SierpinskiFormal.stepGeometric_mul_eq_sum_weightedSeries_of_isPrimitiveRoot
