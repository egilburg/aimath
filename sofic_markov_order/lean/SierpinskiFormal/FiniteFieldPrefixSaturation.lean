import SierpinskiFormal.PolynomialSaturation
import SierpinskiFormal.ProductPrefixes

set_option autoImplicit false

/-!
# Finite-field product prefixes and polynomial saturation

Over a finite field, the length-`e` product prefix of a polynomial is a
geometric-sum power of that polynomial.  Consequently divisibility by some
product prefix is exactly divisibility after saturation by arbitrary powers.
-/

namespace IndependentZeroBlocks

open SierpinskiFormal
open scoped BigOperators

/-- Divisibility by some finite-field product prefix is equivalent to
divisibility after multiplying by some ordinary power.  No nonvanishing or
degree assumption on any of the three polynomials is needed. -/
theorem exists_dvd_mul_kernelPrefix_iff_exists_dvd_mul_pow
    {K : Type*} [Field K] [Fintype K]
    {A P D : Polynomial K} :
    (∃ e : ℕ, D ∣ P * kernelPrefix (Fintype.card K) A e) ↔
      ∃ N : ℕ, D ∣ P * A ^ N := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨∑ j ∈ Finset.range e, (Fintype.card K) ^ j, ?_⟩
    rwa [kernelPrefix_card_eq_pow_geomSum] at he
  · rintro ⟨N, hN⟩
    let e := N + 1
    let M := ∑ j ∈ Finset.range e, (Fintype.card K) ^ j
    have hcard : 2 ≤ Fintype.card K := Fintype.one_lt_card
    have hNM : N ≤ M := by
      calc
        N ≤ e := by simp [e]
        _ = ∑ _j ∈ Finset.range e, 1 := by simp
        _ ≤ M := by
          dsimp [M]
          apply Finset.sum_le_sum
          intro j hj
          exact one_le_pow₀ (by omega)
    refine ⟨e, ?_⟩
    rw [kernelPrefix_card_eq_pow_geomSum]
    exact hN.trans (mul_dvd_mul_left P (pow_dvd_pow A hNM))

/-- The prefix-saturation equivalence under the usual normalized-kernel
hypotheses.  The hypotheses are recorded for convenient use by the density
endpoint; the equivalence itself is valid without them. -/
theorem exists_dvd_mul_kernelPrefix_iff_exists_dvd_mul_pow_of_admissible
    {K : Type*} [Field K] [Fintype K]
    {A P D : Polynomial K}
    (_hA0 : A.coeff 0 = 1)
    (_hAdegree : A.natDegree < Fintype.card K) :
    (∃ e : ℕ, D ∣ P * kernelPrefix (Fintype.card K) A e) ↔
      ∃ N : ℕ, D ∣ P * A ^ N :=
  exists_dvd_mul_kernelPrefix_iff_exists_dvd_mul_pow

/-- For a nonzero denominator, prefix saturation has the single finite test
at exponent `D.natDegree`. -/
theorem exists_dvd_mul_kernelPrefix_iff_dvd_mul_pow_natDegree
    {K : Type*} [Field K] [Fintype K]
    {A P D : Polynomial K} (hD : D ≠ 0) :
    (∃ e : ℕ, D ∣ P * kernelPrefix (Fintype.card K) A e) ↔
      D ∣ P * A ^ D.natDegree :=
  exists_dvd_mul_kernelPrefix_iff_exists_dvd_mul_pow.trans
    (SierpinskiFormal.exists_dvd_mul_pow_iff_dvd_mul_pow_natDegree hD)

/-- The finite prefix-saturation test stated with the standard normalized
kernel hypotheses. -/
theorem exists_dvd_mul_kernelPrefix_iff_dvd_mul_pow_natDegree_of_admissible
    {K : Type*} [Field K] [Fintype K]
    {A P D : Polynomial K}
    (_hA0 : A.coeff 0 = 1)
    (_hAdegree : A.natDegree < Fintype.card K)
    (hD : D ≠ 0) :
    (∃ e : ℕ, D ∣ P * kernelPrefix (Fintype.card K) A e) ↔
      D ∣ P * A ^ D.natDegree :=
  exists_dvd_mul_kernelPrefix_iff_dvd_mul_pow_natDegree hD

end IndependentZeroBlocks
