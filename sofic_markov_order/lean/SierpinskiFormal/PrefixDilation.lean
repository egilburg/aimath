import SierpinskiFormal.ProductPrefixes

open scoped BigOperators
open SierpinskiFormal

set_option autoImplicit false

/-!
# Dilation equations for repeated prefix filters

Dividing a dilation solution by `(1 - X)^r` changes its polynomial kernel by
the `r`-th power of the length-`b` geometric sum. The argument is purely
formal and works over every field, with no characteristic assumption.
-/

namespace IndependentZeroBlocks

/-- The polynomial kernel obtained after applying `r` inclusive-prefix
filters to a base-`b` dilation solution with kernel `A`. -/
noncomputable def prefixDilationKernel {K : Type*} [Field K]
    (b r : ℕ) (A : Polynomial K) : Polynomial K :=
  A * (∑ j ∈ Finset.range b, (Polynomial.X : Polynomial K) ^ j) ^ r

private theorem one_sub_X_mul_geomSum {K : Type*} [Field K] (b : ℕ) :
    (1 - Polynomial.X : Polynomial K) *
        (∑ j ∈ Finset.range b, (Polynomial.X : Polynomial K) ^ j) =
      1 - Polynomial.X ^ b := by
  calc
    (1 - Polynomial.X : Polynomial K) *
        (∑ j ∈ Finset.range b, (Polynomial.X : Polynomial K) ^ j) =
      -((∑ j ∈ Finset.range b, (Polynomial.X : Polynomial K) ^ j) *
        (Polynomial.X - 1)) := by ring
    _ = -(Polynomial.X ^ b - 1) := by rw [geom_sum_mul]
    _ = 1 - Polynomial.X ^ b := by ring

private theorem expand_one_sub_X_pow {K : Type*} [Field K] (b r : ℕ) :
    Polynomial.expand K b ((1 - Polynomial.X) ^ r) =
      ((1 - Polynomial.X) *
        (∑ j ∈ Finset.range b, (Polynomial.X : Polynomial K) ^ j)) ^ r := by
  rw [map_pow, map_sub, map_one, Polynomial.expand_X,
    one_sub_X_mul_geomSum]

/-- Repeated inclusive-prefix filtering preserves a polynomial dilation
equation, multiplying its kernel by the appropriate geometric-sum power. -/
theorem prefixFilter_dilation_equation
    {K : Type*} [Field K]
    (b r : ℕ) (hb : 2 ≤ b) (A : Polynomial K) (F : PowerSeries K)
    (hF : F = (A : PowerSeries K) * dilate b F) :
    rationalMultiple 1 ((1 - Polynomial.X) ^ r) F =
      (prefixDilationKernel b r A : PowerSeries K) *
        dilate b (rationalMultiple 1 ((1 - Polynomial.X) ^ r) F) := by
  let D : Polynomial K := (1 - Polynomial.X) ^ r
  let U : PowerSeries K := rationalMultiple 1 D F
  have hD0 : D.coeff 0 ≠ 0 := by
    dsimp [D]
    rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_pow,
      Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X]
    simp
  have hDU : (D : PowerSeries K) * U = F := by
    simpa [U] using rationalMultiple_denominator 1 D F hD0
  have hdilated :
      (Polynomial.expand K b D : PowerSeries K) * dilate b U = dilate b F := by
    have h := congrArg (dilate b) hDU
    rw [dilate_polynomial_mul b (by omega) D U] at h
    exact h
  have hpoly : D * prefixDilationKernel b r A =
      A * Polynomial.expand K b D := by
    dsimp [D, prefixDilationKernel]
    rw [expand_one_sub_X_pow]
    rw [mul_pow]
    ring
  have htarget :
      (D : PowerSeries K) *
          ((prefixDilationKernel b r A : PowerSeries K) * dilate b U) = F := by
    calc
      (D : PowerSeries K) *
          ((prefixDilationKernel b r A : PowerSeries K) * dilate b U) =
        ((D * prefixDilationKernel b r A : Polynomial K) : PowerSeries K) *
          dilate b U := by simp only [Polynomial.coe_mul]; ring
      _ = ((A * Polynomial.expand K b D : Polynomial K) : PowerSeries K) *
          dilate b U := by rw [hpoly]
      _ = (A : PowerSeries K) *
          ((Polynomial.expand K b D : PowerSeries K) * dilate b U) := by
            simp only [Polynomial.coe_mul]
            ring
      _ = (A : PowerSeries K) * dilate b F := by rw [hdilated]
      _ = F := hF.symm
  have hunique := eq_rationalMultiple_of_denominator 1 D F
    ((prefixDilationKernel b r A : PowerSeries K) * dilate b U) hD0
      (by simpa only [Polynomial.coe_one, one_mul] using htarget)
  simpa [U, D] using hunique.symm

/-- If the original kernel is supported below the radix, the filtered kernel
has degree at most `(r + 1) * (b - 1)`. -/
theorem prefixDilationKernel_natDegree_le
    {K : Type*} [Field K]
    (b r : ℕ) (hb : 2 ≤ b) (A : Polynomial K)
    (hdegree : A.natDegree < b) :
    (prefixDilationKernel b r A).natDegree ≤ (r + 1) * (b - 1) := by
  let S : Polynomial K :=
    ∑ j ∈ Finset.range b, (Polynomial.X : Polynomial K) ^ j
  have hA : A.natDegree ≤ b - 1 := by omega
  have hS : S.natDegree ≤ b - 1 := by
    dsimp [S]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j hj
    exact (Polynomial.natDegree_X_pow_le j).trans (by
      have hjb : j < b := Finset.mem_range.mp hj
      omega)
  have hSpow : (S ^ r).natDegree ≤ r * (b - 1) :=
    Polynomial.natDegree_pow_le_of_le r hS
  have hmul : (A * S ^ r).natDegree ≤ (b - 1) + r * (b - 1) :=
    Polynomial.natDegree_mul_le_of_le hA hSpow
  dsimp [prefixDilationKernel]
  dsimp [S] at hmul
  calc
    (A * (∑ j ∈ Finset.range b, (Polynomial.X : Polynomial K) ^ j) ^ r).natDegree
        ≤ (b - 1) + r * (b - 1) := hmul
    _ = (r + 1) * (b - 1) := by
      rw [Nat.add_mul, one_mul, Nat.add_comm]

/-- The one-fold prefix-filter specialization. -/
theorem prefixFilter_dilation_equation_one
    {K : Type*} [Field K]
    (b : ℕ) (hb : 2 ≤ b) (A : Polynomial K) (F : PowerSeries K)
    (hF : F = (A : PowerSeries K) * dilate b F) :
    rationalMultiple 1 (1 - Polynomial.X) F =
      (A * (∑ j ∈ Finset.range b, (Polynomial.X : Polynomial K) ^ j) :
          Polynomial K) * dilate b (rationalMultiple 1 (1 - Polynomial.X) F) := by
  simpa [prefixDilationKernel] using
    prefixFilter_dilation_equation b 1 hb A F hF

/-- Canonical-series wrapper for repeated prefix filtering. -/
theorem canonicalSeries_prefixFilter_dilation_equation
    {K : Type*} [Field K]
    (b r : ℕ) (hb : 2 ≤ b) (A : Polynomial K)
    (hA0 : A.coeff 0 = 1) (hdegree : A.natDegree < b) :
    rationalMultiple 1 ((1 - Polynomial.X) ^ r) (canonicalSeries b A) =
      (prefixDilationKernel b r A : PowerSeries K) *
        dilate b
          (rationalMultiple 1 ((1 - Polynomial.X) ^ r) (canonicalSeries b A)) := by
  apply prefixFilter_dilation_equation b r hb A
  exact canonicalSeries_dilation_equation b hb A hA0 hdegree

end IndependentZeroBlocks
