import SierpinskiFormal.Convolution
import Mathlib.RingTheory.PowerSeries.Basic

set_option autoImplicit false

/-!
# Geometric power-series filters

This file identifies the abstract constant-weight convolution with the
coefficients obtained by multiplying by a genuine simple-pole geometric series.
-/

namespace SierpinskiFormal

/-- The geometric power series with coefficient `beta ^ n` in degree `n`. -/
def poleSeries {K : Type*} [Semiring K] (beta : K) : PowerSeries K :=
  PowerSeries.mk fun n => beta ^ n

@[simp] theorem coeff_poleSeries
    {K : Type*} [Semiring K] (beta : K) (n : ℕ) :
    PowerSeries.coeff n (poleSeries beta) = beta ^ n := by
  simp [poleSeries]

/-- Multiplication by a geometric series is exactly the constant-polynomial
weighted convolution after twisting the coefficients by `beta⁻¹`. -/
theorem coeff_poleSeries_mul_eq_weighted
    {K : Type*} [Field K] (beta : K) (hbeta : beta ≠ 0)
    (T : PowerSeries K) (n : ℕ) :
    PowerSeries.coeff n (poleSeries beta * T) =
      beta ^ n * Convolution.weighted (Polynomial.C 1)
        (fun r => PowerSeries.coeff r T * (beta⁻¹) ^ r) n := by
  rw [mul_comm, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_poleSeries, Convolution.weighted, Polynomial.eval_C, one_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hrle : r ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
  have hpow : beta ^ n * (beta⁻¹) ^ r = beta ^ (n - r) := by
    rw [← Nat.sub_add_cancel hrle, pow_add, mul_assoc, ← mul_pow]
    simp [hbeta]
  rw [← hpow]
  ring

/-- `poleSeries beta` is the inverse of the simple denominator
`1 - beta * X` inside the power-series ring. -/
theorem one_sub_C_mul_X_mul_poleSeries
    {K : Type*} [Field K] (beta : K) :
    (1 - PowerSeries.C beta * PowerSeries.X) * poleSeries beta = 1 := by
  rw [mul_comm, mul_sub, mul_one, ← mul_assoc]
  ext n
  cases n with
  | zero => simp [poleSeries]
  | succ n =>
      rw [map_sub, coeff_poleSeries, PowerSeries.coeff_one]
      simp only [Nat.succ_ne_zero, ↓reduceIte]
      rw [show (PowerSeries.X : PowerSeries K) = PowerSeries.X ^ 1 by
        exact (pow_one (PowerSeries.X : PowerSeries K)).symm]
      rw [PowerSeries.coeff_mul_X_pow, PowerSeries.coeff_mul_C,
        coeff_poleSeries, pow_succ, sub_self]

end SierpinskiFormal

#print axioms SierpinskiFormal.coeff_poleSeries_mul_eq_weighted
#print axioms SierpinskiFormal.one_sub_C_mul_X_mul_poleSeries
