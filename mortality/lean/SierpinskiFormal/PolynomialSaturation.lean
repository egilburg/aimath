import Mathlib.RingTheory.Polynomial.UniqueFactorization

set_option autoImplicit false

/-!
# A finite test for polynomial saturation

If a nonzero polynomial `D` divides `P * A ^ N` for some exponent, then it
already divides `P * A ^ D.natDegree`.  Factors of `D` which occur in `P` may
be cancelled; every remaining irreducible factor must occur in `A`, and one
power of `A` pays for at least one degree of `D`.
-/

namespace SierpinskiFormal

open Polynomial

private theorem polynomial_isUnit_of_natDegree_eq_zero
    {K : Type*} [Field K] {f : Polynomial K}
    (hf : f ≠ 0) (hdeg : f.natDegree = 0) : IsUnit f := by
  rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg] at hf ⊢
  exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by simpa using hf))

/-- A divisibility by some power of `A` is witnessed by the power whose
exponent is the degree of the nonzero denominator. -/
theorem dvd_mul_pow_natDegree_of_dvd_mul_pow
    {K : Type*} [Field K] {A P D : Polynomial K} {N : ℕ}
    (hD : D ≠ 0) (hdiv : D ∣ P * A ^ N) :
    D ∣ P * A ^ D.natDegree := by
  classical
  generalize hd : D.natDegree = d
  induction d using Nat.strong_induction_on generalizing D P N with
  | h d ih =>
      by_cases hd0 : d = 0
      · have hunit : IsUnit D :=
          polynomial_isUnit_of_natDegree_eq_zero hD (hd.trans hd0)
        exact hunit.dvd
      · have hdpos : 0 < D.natDegree := by omega
        obtain ⟨q, hqirr, hqD⟩ := Polynomial.exists_irreducible_of_natDegree_pos hdpos
        obtain ⟨D', rfl⟩ := hqD
        have hq0 : q ≠ 0 := hqirr.ne_zero
        have hD'0 : D' ≠ 0 := right_ne_zero_of_mul hD
        have hqdeg : 0 < q.natDegree := Nat.pos_of_ne_zero fun hqdeg0 ↦
          hqirr.not_isUnit
            (polynomial_isUnit_of_natDegree_eq_zero hq0 hqdeg0)
        have hdeg_mul : (q * D').natDegree = q.natDegree + D'.natDegree :=
          Polynomial.natDegree_mul hq0 hD'0
        have hD'deg : D'.natDegree < d := by
          rw [← hd, hdeg_mul]
          omega
        have hstep : D'.natDegree + 1 ≤ d := by
          rw [← hd, hdeg_mul]
          omega
        by_cases hqA : q ∣ A
        · have hD'div : D' ∣ P * A ^ N :=
            (dvd_mul_left D' q).trans hdiv
          have hind : D' ∣ P * A ^ D'.natDegree :=
            ih D'.natDegree hD'deg hD'0 hD'div rfl
          have hone : q * D' ∣ P * A ^ (D'.natDegree + 1) := by
            simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using
              mul_dvd_mul hqA hind
          exact hone.trans
            (mul_dvd_mul_left P (pow_dvd_pow A hstep))
        · have hqprod : q ∣ P * A ^ N :=
            (dvd_mul_right q D').trans hdiv
          have hqP : q ∣ P := by
            rcases hqirr.prime.dvd_or_dvd hqprod with hqP | hqpow
            · exact hqP
            · exact False.elim (hqA (hqirr.prime.dvd_of_dvd_pow hqpow))
          obtain ⟨P', rfl⟩ := hqP
          have hcancel : D' ∣ P' * A ^ N := by
            apply (mul_dvd_mul_iff_left hq0).mp
            simpa [mul_assoc] using hdiv
          have hind : D' ∣ P' * A ^ D'.natDegree :=
            ih D'.natDegree hD'deg hD'0 hcancel rfl
          have hsmall : q * D' ∣ (q * P') * A ^ D'.natDegree := by
            simpa [mul_assoc] using mul_dvd_mul_left q hind
          exact hsmall.trans
            (mul_dvd_mul_left (q * P') (pow_dvd_pow A (Nat.le_of_lt hD'deg)))

/-- Polynomial saturation by powers of `A` can be tested at the single
exponent `D.natDegree`. -/
theorem exists_dvd_mul_pow_iff_dvd_mul_pow_natDegree
    {K : Type*} [Field K] {A P D : Polynomial K} (hD : D ≠ 0) :
    (∃ N : ℕ, D ∣ P * A ^ N) ↔ D ∣ P * A ^ D.natDegree := by
  constructor
  · rintro ⟨N, hN⟩
    exact dvd_mul_pow_natDegree_of_dvd_mul_pow hD hN
  · exact fun h ↦ ⟨D.natDegree, h⟩

/-- A numerator coprime to the denominator has no effect on divisibility by a
fixed power. -/
theorem dvd_mul_pow_iff_dvd_pow_of_isCoprime
    {K : Type*} [Field K] {A P D : Polynomial K} {N : ℕ}
    (hPD : IsCoprime P D) :
    D ∣ P * A ^ N ↔ D ∣ A ^ N := by
  constructor
  · exact hPD.symm.dvd_of_dvd_mul_left
  · exact fun h ↦ dvd_mul_of_dvd_right h P

/-- In a reduced fraction, saturation of the denominator is independent of
the numerator. -/
theorem exists_dvd_mul_pow_iff_exists_dvd_pow_of_isCoprime
    {K : Type*} [Field K] {A P D : Polynomial K}
    (hPD : IsCoprime P D) :
    (∃ N : ℕ, D ∣ P * A ^ N) ↔ ∃ N : ℕ, D ∣ A ^ N := by
  constructor
  · rintro ⟨N, hN⟩
    exact ⟨N, (dvd_mul_pow_iff_dvd_pow_of_isCoprime hPD).mp hN⟩
  · rintro ⟨N, hN⟩
    exact ⟨N, (dvd_mul_pow_iff_dvd_pow_of_isCoprime hPD).mpr hN⟩

/-- For a reduced fraction, the existential saturation test is equivalently
the single finite divisibility test with no numerator. -/
theorem exists_dvd_mul_pow_iff_dvd_pow_natDegree_of_isCoprime
    {K : Type*} [Field K] {A P D : Polynomial K}
    (hD : D ≠ 0) (hPD : IsCoprime P D) :
    (∃ N : ℕ, D ∣ P * A ^ N) ↔ D ∣ A ^ D.natDegree := by
  rw [exists_dvd_mul_pow_iff_exists_dvd_pow_of_isCoprime hPD]
  simpa only [one_mul] using
    (exists_dvd_mul_pow_iff_dvd_mul_pow_natDegree
      (A := A) (P := (1 : Polynomial K)) hD)

end SierpinskiFormal
