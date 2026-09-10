import SierpinskiFormal.RationalSpan
import Mathlib.Algebra.Polynomial.Div

set_option autoImplicit false

namespace IndependentZeroBlocks

variable {K : Type*} [Field K]

/-- The first positive coefficient of a kernel occurs at degree d. -/
def KernelFirstDegree (A : Polynomial K) (d : ℕ) : Prop :=
  0 < d ∧ A.coeff d ≠ 0 ∧ ∀ j, 0 < j → j < d → A.coeff j = 0

/-- A denominator supported on the kernel: all of its factors, with any
finite multiplicities, can be absorbed by a power of the kernel. -/
def KernelSupportedDenominator (A D : Polynomial K) : Prop :=
  ∃ N : ℕ, D ∣ A ^ N

/-- Either the first positive degree is shared, or the rational denominator
is supported entirely on the kernel. -/
def KernelDenominatorCompatible (A D : Polynomial K) (d : ℕ) : Prop :=
  KernelFirstDegree A d ∨ KernelSupportedDenominator A D

theorem KernelSupportedDenominator.coeff_zero_ne_zero
    {A D : Polynomial K} (h : KernelSupportedDenominator A D)
    (hA0 : A.coeff 0 = 1) : D.coeff 0 ≠ 0 := by
  obtain ⟨N, C, hC⟩ := h
  intro hD0
  have heq := congrArg (fun P : Polynomial K => P.coeff 0) hC
  simp [Polynomial.coeff_mul, hA0, hD0] at heq
  rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_pow,
    ← Polynomial.coeff_zero_eq_eval_zero, hA0, one_pow] at heq
  exact one_ne_zero heq

theorem KernelSupportedDenominator.map_radix
    {L : Type*} [Field L] [Fintype K] [Fintype L] [Algebra K L]
    {A D : Polynomial K} (h : KernelSupportedDenominator A D) :
    KernelSupportedDenominator
      ((A.map (algebraMap K L)) ^ radixExtensionExponent K L)
      (D.map (algebraMap K L)) := by
  obtain ⟨N, hN⟩ := h
  have hr : 0 < radixExtensionExponent K L := by
    have hh := pred_card_eq_pred_mul_radixExtensionExponent K L
    have hL : 2 ≤ Fintype.card L := Fintype.one_lt_card
    by_contra hn
    have hz : radixExtensionExponent K L = 0 := by omega
    rw [hz, mul_zero] at hh
    omega
  refine ⟨N, ?_⟩
  have hm : D.map (algebraMap K L) ∣ (A.map (algebraMap K L)) ^ N := by
    simpa using Polynomial.map_dvd (algebraMap K L) hN
  apply dvd_trans hm
  rw [← pow_mul]
  exact pow_dvd_pow _ (Nat.le_mul_of_pos_left _ hr)

/-- A geometric denominator, written as a polynomial. -/
noncomputable def geometricDenominator (r : K) : Polynomial K :=
  1 - Polynomial.C r * Polynomial.X

@[simp] theorem geometricDenominator_coeff_zero (r : K) :
    (geometricDenominator r).coeff 0 = 1 := by
  simp [geometricDenominator]

theorem geometricDenominator_dvd_of_eval_zero
    (A : Polynomial K) (r : K) (hr : r ≠ 0)
    (hroot : A.eval r⁻¹ = 0) :
    geometricDenominator r ∣ A := by
  have hroot' : Polynomial.X - Polynomial.C r⁻¹ ∣ A :=
    Polynomial.dvd_iff_isRoot.mpr hroot
  obtain ⟨B, hB⟩ := hroot'
  have hscale : geometricDenominator r * Polynomial.C (-r⁻¹) =
      Polynomial.X - Polynomial.C r⁻¹ := by
    simp only [geometricDenominator, mul_sub, sub_mul, one_mul]
    rw [mul_comm (Polynomial.C r) Polynomial.X, mul_assoc, ← Polynomial.C_mul]
    simp [hr, Polynomial.C_neg, sub_eq_add_neg, add_comm]
  refine ⟨Polynomial.C (-r⁻¹) * B, ?_⟩
  rw [hB, ← hscale]
  ring

theorem kernelSupported_geometric_power_of_eval_zero
    (A : Polynomial K) (r : K) (hr : r ≠ 0)
    (hroot : A.eval r⁻¹ = 0) (m : ℕ) :
    KernelSupportedDenominator A (geometricDenominator r ^ m) := by
  exact ⟨m, pow_dvd_pow_of_dvd (geometricDenominator_dvd_of_eval_zero A r hr hroot) m⟩

end IndependentZeroBlocks
