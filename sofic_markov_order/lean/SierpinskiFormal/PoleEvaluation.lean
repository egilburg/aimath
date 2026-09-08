import Mathlib.FieldTheory.Finite.Basic
import Lean.Elab.Tactic.Omega

/-!
# The admissible pole-evaluation condition

The b-th-root hypothesis is explicit. This file proves its finite-field
consequence and does not assert the existence of a suitable extension field.
-/

namespace SierpinskiFormal

/-- At a branch pole the positive-power kernel evaluates to zero. -/
theorem kernel_eval_zero
    {K : Type*} [Field K] (D : Polynomial K) (gamma : K)
    (a s : ℕ) (ha : 0 < a) (hs : 0 < s) (hzero : D.eval gamma = 0) :
    (D ^ (a * s)).eval gamma = 0 := by
  rw [Polynomial.eval_pow, hzero, zero_pow (Nat.ne_of_gt (Nat.mul_pos ha hs))]

/-- At an off-branch pole a b-th root of the evaluation makes the kernel
evaluate to one when the field size is congruent to one modulo b. -/
theorem kernel_eval_one_of_root
    {K : Type*} [Field K] [Fintype K]
    (D : Polynomial K) (gamma r : K) (a b s : ℕ)
    (hq : Fintype.card K = b * s + 1)
    (hr : r ^ b = D.eval gamma) (hrne : r ≠ 0) :
    (D ^ (a * s)).eval gamma = 1 := by
  have hcard : Fintype.card K - 1 = b * s := by omega
  have hexp : b * (a * s) = (Fintype.card K - 1) * a := by
    rw [hcard]
    ac_rfl
  rw [Polynomial.eval_pow, ← hr, ← pow_mul, hexp, pow_mul,
    FiniteField.pow_card_sub_one_eq_one r hrne, one_pow]

/-- Splitting the finitely many polynomials `X^b-D(gamma)` supplies precisely
the evaluation condition required by the common-kernel-seed theorem. -/
theorem kernel_eval_zero_or_one_of_root
    {K : Type*} [Field K] [Fintype K]
    (D : Polynomial K) (gamma : K) (a b s : ℕ)
    (ha : 0 < a) (hs : 0 < s)
    (hq : Fintype.card K = b * s + 1)
    (hroot : ∃ r : K, r ^ b = D.eval gamma) :
    (D ^ (a * s)).eval gamma = 0 ∨ (D ^ (a * s)).eval gamma = 1 := by
  by_cases hzero : D.eval gamma = 0
  · exact Or.inl (kernel_eval_zero D gamma a s ha hs hzero)
  · right
    have hb : 0 < b := by
      by_contra hb
      have hbzero : b = 0 := by omega
      have hcard : 1 < Fintype.card K := Fintype.one_lt_card
      simp only [hbzero, zero_mul, zero_add] at hq
      omega
    obtain ⟨r, hr⟩ := hroot
    have hrne : r ≠ 0 := by
      intro hz
      rw [hz, zero_pow (Nat.ne_of_gt hb)] at hr
      exact hzero hr.symm
    exact kernel_eval_one_of_root D gamma r a b s hq hr hrne

/-- Enlarging a finite field preserves the cardinality congruence needed for
the kernel exponent. Thus later splitting-field constructions do not lose it. -/
theorem card_sub_one_dvd_of_finite_extension
    {K L : Type*} [Field K] [Field L] [Fintype K] [Fintype L] [Algebra K L]
    (b : ℕ) (hb : b ∣ Fintype.card K - 1) :
    b ∣ Fintype.card L - 1 := by
  have hK : 1 ≤ Fintype.card K := Fintype.card_pos
  have hL : 1 ≤ Fintype.card L := Fintype.card_pos
  have hbase : Nat.ModEq b 1 (Fintype.card K) := (Nat.modEq_iff_dvd' hK).mpr hb
  apply (Nat.modEq_iff_dvd' hL).mp
  simpa only [one_pow, ← Module.card_eq_pow_finrank] using
    hbase.pow (Module.finrank K L)

end SierpinskiFormal

#print axioms SierpinskiFormal.kernel_eval_zero_or_one_of_root
#print axioms SierpinskiFormal.card_sub_one_dvd_of_finite_extension
