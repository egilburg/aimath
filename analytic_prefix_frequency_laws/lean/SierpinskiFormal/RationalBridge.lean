import SierpinskiFormal.GeometricFilter
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Fintype.Units

set_option autoImplicit false

/-!
# Rational denominators over finite fields

Every polynomial over a finite field whose constant coefficient is nonzero
divides `1 - X ^ m` for some positive `m`.  Consequently its inverse as a
power series is a polynomial times a step-geometric (hence periodic) series.
This avoids a partial-fraction decomposition and also handles repeated
factors in positive characteristic.
-/

namespace SierpinskiFormal

open Polynomial

/-- A nonzero-constant polynomial over a finite field divides a positive
power of `X` minus one. -/
theorem exists_dvd_X_pow_sub_one
    {K : Type*} [Field K] [Finite K]
    (D : Polynomial K) (hD0 : D.coeff 0 ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ D ∣ X ^ m - 1 := by
  have hDne : D ≠ 0 := by
    intro h
    apply hD0
    rw [h]
    simp
  let g : Polynomial K := D * C D.leadingCoeff⁻¹
  have hgmonic : g.Monic := by
    simpa [g] using D.monic_mul_leadingCoeff_inv hDne
  letI : Module.Finite K (AdjoinRoot g) := hgmonic.finite_adjoinRoot
  letI : Finite (AdjoinRoot g) := Module.finite_of_finite K
  have hg0 : g.coeff 0 ≠ 0 := by
    simp only [g, mul_coeff_zero, coeff_C_zero]
    exact mul_ne_zero hD0 (inv_ne_zero (leadingCoeff_ne_zero.mpr hDne))
  have hroot : IsUnit (AdjoinRoot.root g) := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨-(g.coeff 0)⁻¹ * AdjoinRoot.mk g (g.divX), ?_⟩
    have hrel := congrArg (AdjoinRoot.mk g) (X_mul_divX_add g)
    simp only [map_add, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C,
      AdjoinRoot.mk_self] at hrel
    calc
      AdjoinRoot.root g * (-(g.coeff 0)⁻¹ * AdjoinRoot.mk g (g.divX)) =
          -(g.coeff 0)⁻¹ *
            (AdjoinRoot.root g * AdjoinRoot.mk g (g.divX)) := by ring
      _ = -(g.coeff 0)⁻¹ * (-(g.coeff 0)) := by rw [eq_neg_of_add_eq_zero_left hrel]
      _ = 1 := by
        have hscalar : -(g.coeff 0)⁻¹ * (-(g.coeff 0)) = (1 : K) := by
          field_simp
        simpa using congrArg (AdjoinRoot.of g) hscalar
  let u : (AdjoinRoot g)ˣ := hroot.unit
  let m : ℕ := orderOf u
  refine ⟨m, orderOf_pos u, ?_⟩
  have hu : ((u : (AdjoinRoot g)) ^ m) = 1 := by
    exact congrArg ((↑) : (AdjoinRoot g)ˣ → AdjoinRoot g) (pow_orderOf_eq_one u)
  have hrootpow : (AdjoinRoot.root g) ^ m = 1 := by
    simpa [u, IsUnit.unit_spec] using hu
  have hgdiv : g ∣ X ^ m - 1 := by
    rw [← AdjoinRoot.mk_eq_zero]
    simp [hrootpow]
  exact (dvd_mul_right D (C D.leadingCoeff⁻¹)).trans (by simpa [g] using hgdiv)

/-- Denominator form suited to a geometric series with ratio `X ^ m`. -/
theorem exists_mul_eq_one_sub_X_pow
    {K : Type*} [Field K] [Finite K]
    (D : Polynomial K) (hD0 : D.coeff 0 ≠ 0) :
    ∃ (m : ℕ) (E : Polynomial K), 0 < m ∧ D * E = 1 - X ^ m := by
  obtain ⟨m, hm, E, hE⟩ := exists_dvd_X_pow_sub_one D hD0
  refine ⟨m, -E, hm, ?_⟩
  rw [mul_neg, ← hE]
  abel

/-- The series `1 + X^m + X^(2m) + ⋯`, expressed coefficientwise. -/
def stepGeometric {K : Type*} [Semiring K] (m : ℕ) : PowerSeries K :=
  PowerSeries.mk fun n => if m ∣ n then 1 else 0

@[simp] theorem coeff_stepGeometric
    {K : Type*} [Semiring K] (m n : ℕ) :
    PowerSeries.coeff n (stepGeometric m) = if m ∣ n then 1 else 0 := by
  simp [stepGeometric]

theorem coeff_stepGeometric_add_period
    {K : Type*} [Semiring K] (m n : ℕ) :
    PowerSeries.coeff (n + m) (stepGeometric m : PowerSeries K) =
      PowerSeries.coeff n (stepGeometric m : PowerSeries K) := by
  simp [stepGeometric, Nat.dvd_add_self_right]

theorem coeff_stepGeometric_mul
    {K : Type*} [Semiring K] (m : ℕ) (T : PowerSeries K) (n : ℕ) :
    PowerSeries.coeff n (stepGeometric m * T) =
      ∑ r ∈ Finset.range (n + 1),
        if m ∣ r then PowerSeries.coeff (n - r) T else 0 := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [stepGeometric]

/-- The step-geometric series is inverse to `1 - X^m` when `m > 0`. -/
theorem one_sub_X_pow_mul_stepGeometric
    {K : Type*} [CommRing K] (m : ℕ) (hm : 0 < m) :
    (1 - (PowerSeries.X : PowerSeries K) ^ m) * stepGeometric m = 1 := by
  ext n
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_one]
  by_cases hn : n = 0
  · subst n
    simp [stepGeometric, hm.ne']
  · rw [PowerSeries.coeff_X_pow_mul']
    by_cases hmn : m ≤ n
    · have hdiv : m ∣ n ↔ m ∣ n - m := by
        constructor
        · intro h
          exact Nat.dvd_sub h (dvd_refl m)
        · intro h
          have hadd : m ∣ (n - m) + m := dvd_add h (dvd_refl m)
          rwa [Nat.sub_add_cancel hmn] at hadd
      simp only [if_pos hmn]
      simp only [stepGeometric, PowerSeries.coeff_mk]
      rw [if_congr hdiv rfl rfl]
      split <;> simp [hn]
    · have hnotdiv : ¬m ∣ n := by
        intro hdiv
        exact hmn (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdiv)
      simp [stepGeometric, hmn, hnotdiv, hn]

/-- A concrete power-series inverse for an arbitrary denominator with
nonzero constant coefficient: a polynomial times a periodic series. -/
theorem exists_polynomial_stepGeometric_inverse
    {K : Type*} [Field K] [Finite K]
    (D : Polynomial K) (hD0 : D.coeff 0 ≠ 0) :
    ∃ (m : ℕ) (E : Polynomial K), 0 < m ∧
      (D : PowerSeries K) * ((E : PowerSeries K) * stepGeometric m) = 1 := by
  obtain ⟨m, E, hm, hDE⟩ := exists_mul_eq_one_sub_X_pow D hD0
  refine ⟨m, E, hm, ?_⟩
  rw [← mul_assoc, ← Polynomial.coe_mul, hDE,
    Polynomial.coe_sub, Polynomial.coe_one, Polynomial.coe_pow, Polynomial.coe_X]
  exact one_sub_X_pow_mul_stepGeometric m hm

/-- Existence of a power-series inverse, obtained from the periodic
construction. -/
theorem exists_denominatorInverse
    {K : Type*} [Field K] [Finite K]
    (D : Polynomial K) (hD0 : D.coeff 0 ≠ 0) :
    ∃ V : PowerSeries K, (D : PowerSeries K) * V = 1 := by
  obtain ⟨m, E, _, hE⟩ := exists_polynomial_stepGeometric_inverse D hD0
  exact ⟨(E : PowerSeries K) * stepGeometric m, hE⟩

/-- A chosen power-series inverse of a finite-field polynomial denominator. -/
noncomputable def denominatorInverse
    {K : Type*} [Field K] [Finite K]
    (D : Polynomial K) (hD0 : D.coeff 0 ≠ 0) : PowerSeries K :=
  Classical.choose (exists_denominatorInverse D hD0)

@[simp] theorem coe_mul_denominatorInverse
    {K : Type*} [Field K] [Finite K]
    (D : Polynomial K) (hD0 : D.coeff 0 ≠ 0) :
    (D : PowerSeries K) * denominatorInverse D hD0 = 1 := by
  exact Classical.choose_spec (exists_denominatorInverse D hD0)

/-- Over a finite field, the canonical denominator inverse itself has the
polynomial-times-periodic representation constructed above. -/
theorem exists_denominatorInverse_eq_polynomial_stepGeometric
    {K : Type*} [Field K] [Finite K]
    (D : Polynomial K) (hD0 : D.coeff 0 ≠ 0) :
    ∃ (m : ℕ) (E : Polynomial K), 0 < m ∧
      denominatorInverse D hD0 = (E : PowerSeries K) * stepGeometric m := by
  obtain ⟨m, E, hm, hinv⟩ := exists_polynomial_stepGeometric_inverse D hD0
  refine ⟨m, E, hm, ?_⟩
  calc
    denominatorInverse D hD0 =
        denominatorInverse D hD0 * 1 := by rw [mul_one]
    _ = denominatorInverse D hD0 *
        ((D : PowerSeries K) * ((E : PowerSeries K) * stepGeometric m)) := by
          rw [hinv]
    _ = ((D : PowerSeries K) * denominatorInverse D hD0) *
        ((E : PowerSeries K) * stepGeometric m) := by ring
    _ = (E : PowerSeries K) * stepGeometric m := by
      rw [coe_mul_denominatorInverse, one_mul]

/-- The canonical result of multiplying `T` by the rational function `P/D`. -/
noncomputable def rationalMultiplierSeries
    {K : Type*} [Field K] [Finite K]
    (P D : Polynomial K) (T : PowerSeries K) (hD0 : D.coeff 0 ≠ 0) :
    PowerSeries K :=
  (P : PowerSeries K) * T * denominatorInverse D hD0

@[simp] theorem coe_mul_rationalMultiplierSeries
    {K : Type*} [Field K] [Finite K]
    (P D : Polynomial K) (T : PowerSeries K) (hD0 : D.coeff 0 ≠ 0) :
    (D : PowerSeries K) * rationalMultiplierSeries P D T hD0 =
      (P : PowerSeries K) * T := by
  unfold rationalMultiplierSeries
  calc
    (D : PowerSeries K) *
        ((P : PowerSeries K) * T * denominatorInverse D hD0) =
      (P : PowerSeries K) * T *
        ((D : PowerSeries K) * denominatorInverse D hD0) := by ring
    _ = (P : PowerSeries K) * T := by
      rw [coe_mul_denominatorInverse, mul_one]

theorem exists_rationalMultiplierSeries_eq_polynomial_stepGeometric
    {K : Type*} [Field K] [Finite K]
    (P D : Polynomial K) (T : PowerSeries K) (hD0 : D.coeff 0 ≠ 0) :
    ∃ (m : ℕ) (E : Polynomial K), 0 < m ∧
      rationalMultiplierSeries P D T hD0 =
        ((P * E : Polynomial K) : PowerSeries K) *
          (stepGeometric m * T) := by
  obtain ⟨m, E, hm, hE⟩ :=
    exists_denominatorInverse_eq_polynomial_stepGeometric D hD0
  refine ⟨m, E, hm, ?_⟩
  unfold rationalMultiplierSeries
  rw [hE, Polynomial.coe_mul]
  ring

/-- Multiplying a power series by an arbitrary rational function `P / D`
is realized without fractions, using the step-geometric denominator above. -/
theorem exists_rational_multiplier_series
    {K : Type*} [Field K] [Finite K]
    (P D : Polynomial K) (T : PowerSeries K)
    (hD0 : D.coeff 0 ≠ 0) :
    ∃ (m : ℕ) (E : Polynomial K) (U : PowerSeries K),
      0 < m ∧ U = (P : PowerSeries K) * T *
        ((E : PowerSeries K) * stepGeometric m) ∧
      (D : PowerSeries K) * U = (P : PowerSeries K) * T := by
  obtain ⟨m, E, hm, hinv⟩ := exists_polynomial_stepGeometric_inverse D hD0
  refine ⟨m, E, (P : PowerSeries K) * T *
    ((E : PowerSeries K) * stepGeometric m), hm, rfl, ?_⟩
  calc
    (D : PowerSeries K) * ((P : PowerSeries K) * T *
        ((E : PowerSeries K) * stepGeometric m)) =
      (P : PowerSeries K) * T *
        ((D : PowerSeries K) * ((E : PowerSeries K) * stepGeometric m)) := by ring
    _ = (P : PowerSeries K) * T := by rw [hinv, mul_one]

end SierpinskiFormal

#print axioms SierpinskiFormal.exists_dvd_X_pow_sub_one
#print axioms SierpinskiFormal.exists_rational_multiplier_series
