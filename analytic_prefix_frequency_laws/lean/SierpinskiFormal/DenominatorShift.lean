import SierpinskiFormal.SeedBlocks
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.Polynomial.Div

set_option autoImplicit false

/-!
# Removing a power of `X` from a denominator

A nonzero polynomial is a power of `X` times a polynomial regular at the
origin.  Multiplication of a power series by that power of `X` is only a
coefficient shift, so zero blocks transfer back across it.
-/

namespace IndependentZeroBlocks

open SierpinskiFormal
open Polynomial

/-- Remove the exact initial power of `X` from a nonzero polynomial. -/
theorem exists_eq_X_pow_mul_coeff_zero_ne_zero
    {K : Type*} [Field K] (D : Polynomial K) (hD : D ≠ 0) :
    ∃ (k : ℕ) (E : Polynomial K),
      D = X ^ k * E ∧ E.coeff 0 ≠ 0 := by
  let k := D.natTrailingDegree
  have hdiv : X ^ k ∣ D := by
    rw [X_pow_dvd_iff]
    intro d hd
    exact coeff_eq_zero_of_lt_natTrailingDegree hd
  obtain ⟨E, hfactor⟩ := hdiv
  refine ⟨k, E, hfactor, ?_⟩
  have htrail : D.coeff k ≠ 0 := by
    simpa [k, trailingCoeff] using
      (trailingCoeff_nonzero_iff_nonzero.mpr hD)
  have hcoeff : D.coeff k = E.coeff 0 := by
    rw [hfactor]
    simpa using coeff_X_pow_mul E k 0
  rwa [hcoeff] at htrail

/-- A zero-block theorem for a shifted series transfers to the original
series. -/
theorem hasArbitrarilyLongZeroBlocks_of_X_pow_mul
    {K : Type*} [Semiring K] (k : ℕ) (U : PowerSeries K)
    (hshift : HasArbitrarilyLongZeroBlocks
      (fun n => PowerSeries.coeff n (PowerSeries.X ^ k * U))) :
    HasArbitrarilyLongZeroBlocks (fun n => PowerSeries.coeff n U) := by
  intro length start
  obtain ⟨s, hs, hzero⟩ := hshift length (start + k)
  have hks : k ≤ s := by omega
  refine ⟨s - k, by omega, ?_⟩
  intro i hi
  change PowerSeries.coeff (s - k + i) U = 0
  rw [← PowerSeries.coeff_X_pow_mul U k (s - k + i)]
  have hindex : (s - k + i) + k = s + i := by omega
  rw [hindex]
  exact hzero i hi

/-- Equation-level bridge after removing an initial power of `X` from the
denominator. -/
theorem X_pow_mul_eq_rationalMultiple_of_denominator_eq
    {K : Type*} [Field K]
    (D E : Polynomial K) (k : ℕ) (U S : PowerSeries K)
    (hfactor : D = X ^ k * E) (hE0 : E.coeff 0 ≠ 0)
    (hDU : (D : PowerSeries K) * U = S) :
    PowerSeries.X ^ k * U = rationalMultiple 1 E S := by
  apply eq_rationalMultiple_of_denominator 1 E S
    (PowerSeries.X ^ k * U) hE0
  have hfactorPS : (D : PowerSeries K) =
      PowerSeries.X ^ k * (E : PowerSeries K) := by
    rw [hfactor, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X]
  calc
    (E : PowerSeries K) * (PowerSeries.X ^ k * U) =
        (PowerSeries.X ^ k * (E : PowerSeries K)) * U := by ring
    _ = (D : PowerSeries K) * U := by rw [← hfactorPS]
    _ = S := hDU
    _ = ((1 : Polynomial K) : PowerSeries K) * S := by simp

/-- Combined factorization and equation bridge for an arbitrary nonzero
polynomial denominator. -/
theorem exists_shift_rationalMultiple_of_denominator
    {K : Type*} [Field K]
    (D : Polynomial K) (U S : PowerSeries K) (hD : D ≠ 0)
    (hDU : (D : PowerSeries K) * U = S) :
    ∃ (k : ℕ) (E : Polynomial K),
      D = X ^ k * E ∧ E.coeff 0 ≠ 0 ∧
      PowerSeries.X ^ k * U = rationalMultiple 1 E S := by
  obtain ⟨k, E, hfactor, hE0⟩ :=
    exists_eq_X_pow_mul_coeff_zero_ne_zero D hD
  exact ⟨k, E, hfactor, hE0,
    X_pow_mul_eq_rationalMultiple_of_denominator_eq
      D E k U S hfactor hE0 hDU⟩

end IndependentZeroBlocks

#print axioms IndependentZeroBlocks.exists_eq_X_pow_mul_coeff_zero_ne_zero
#print axioms IndependentZeroBlocks.hasArbitrarilyLongZeroBlocks_of_X_pow_mul
#print axioms IndependentZeroBlocks.exists_shift_rationalMultiple_of_denominator
