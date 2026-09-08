import SierpinskiFormal.SeedBlocks
import SierpinskiFormal.Lucas

set_option autoImplicit false

/-!
# Denominators supported on the branch kernel

This file proves that a rational denominator dividing a power of the branch
kernel can be absorbed into a polynomial factor after passing to a sufficiently
large finite-field Frobenius dilation.
-/

namespace IndependentZeroBlocks

open SierpinskiFormal

/-- Dilation by a power of the base preserves the same seed.  The power only
increases the required depth and rescales the left trim. -/
theorem HasSeedBlocks.dilate_pow
    {K : Type*} [CommRing K] {q seed : ℕ} {T : PowerSeries K}
    (hT : HasSeedBlocks q seed T) (hq : 2 ≤ q) (e : ℕ) :
    HasSeedBlocks q seed (dilate (q ^ e) T) := by
  obtain ⟨h, depth, hT⟩ := hT
  refine ⟨h * q ^ e, depth + e, ?_⟩
  intro F hF j hj hjq
  have heF : e ≤ F := by omega
  have hdepth : depth ≤ F - e := by omega
  have hQpos : 0 < q ^ e := pow_pos (by omega) e
  rw [coeff_dilate]
  split_ifs with hdiv
  · have hpow : q ^ F = q ^ e * q ^ (F - e) := by
      rw [← pow_add]
      congr 1
      omega
    have hleft : q ^ e ∣ seed * q ^ F := by
      rw [hpow]
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        dvd_mul_right (q ^ e) (seed * q ^ (F - e))
    have hquot :
        (seed * q ^ F + j) / q ^ e = seed * q ^ (F - e) + j / q ^ e := by
      rw [Nat.add_div_of_dvd_right hleft, hpow]
      rw [show seed * (q ^ e * q ^ (F - e)) =
          (seed * q ^ (F - e)) * q ^ e by ring]
      rw [Nat.mul_div_left _ hQpos]
    rw [hquot]
    apply hT (F - e) hdepth (j / q ^ e)
    · exact (Nat.le_div_iff_mul_le hQpos).2 hj
    · apply (Nat.div_lt_iff_lt_mul hQpos).2
      rw [Nat.pow_sub_mul_pow q heF]
      exact hjq
  · rfl

/-- Finite-field Frobenius iterated `e` times is dilation by the corresponding
power of the field cardinality. -/
theorem power_card_pow_eq_dilate
    {K : Type*} [Field K] [Fintype K] (T : PowerSeries K) (e : ℕ) :
    T ^ (Fintype.card K) ^ e = dilate ((Fintype.card K) ^ e) T := by
  apply power_eq_dilate_of_polynomial ((Fintype.card K) ^ e)
    (pow_pos Fintype.card_pos e)
  induction e with
  | zero =>
      intro P
      simp
  | succ e ih =>
      intro P
      rw [pow_succ, Polynomial.expand_mul, ih, FiniteField.expand_card,
        ← pow_mul]
      congr 1
      exact Nat.mul_comm _ _

/-- If a denominator divides a power of the branch kernel, every rational
multiple with that denominator inherits any seed blocks already known for the
branch series. -/
theorem HasSeedBlocks.rationalMultiple_of_dvd_kernel_pow
    {K : Type*} [Field K] [Fintype K]
    {seed : ℕ}
    (A P D : Polynomial K) (T : PowerSeries K)
    (hbranch : (A : PowerSeries K) * T ^ (Fintype.card K - 1) = 1)
    (hseed : HasSeedBlocks (Fintype.card K) seed T)
    (N : ℕ) (hDpow : D ∣ A ^ N) (hD0 : D.coeff 0 ≠ 0) :
    HasSeedBlocks (Fintype.card K) seed (rationalMultiple P D T) := by
  let Q := Fintype.card K
  let E := N + 1
  let M := ∑ i ∈ Finset.range E, Q ^ i
  have hQ : 2 ≤ Q := Fintype.one_lt_card
  have hgeom : (Q - 1) * M + 1 = Q ^ E := by
    have h := geom_sum_mul_add (Q - 1) E
    rw [show Q - 1 + 1 = Q by omega] at h
    simpa [M, Nat.mul_comm] using h
  have hNM : N ≤ M := by
    calc
      N ≤ E := by dsimp [E]; omega
      _ = ∑ _i ∈ Finset.range E, 1 := by simp
      _ ≤ M := by
        dsimp [M]
        apply Finset.sum_le_sum
        intro i hi
        exact one_le_pow₀ (by omega)
  have hunit :
      (((A ^ M : Polynomial K) : PowerSeries K) *
        T ^ ((Q - 1) * M)) = 1 := by
    have hb : (A : PowerSeries K) * T ^ (Q - 1) = 1 := by
      simpa [Q] using hbranch
    have h : ((A : PowerSeries K) * T ^ (Q - 1)) ^ M = 1 := by
      simpa using congrArg (fun U : PowerSeries K => U ^ M) hb
    rw [mul_pow, ← pow_mul] at h
    simpa [Polynomial.coe_pow] using h
  have hfactorPower :
      T = ((A ^ M : Polynomial K) : PowerSeries K) * T ^ (Q ^ E) := by
    calc
      T = (1 : PowerSeries K) * T := by simp
      _ = ((((A ^ M : Polynomial K) : PowerSeries K) *
          T ^ ((Q - 1) * M)) * T) := by rw [hunit]
      _ = ((A ^ M : Polynomial K) : PowerSeries K) *
          T ^ ((Q - 1) * M + 1) := by rw [pow_succ]; ring
      _ = ((A ^ M : Polynomial K) : PowerSeries K) * T ^ (Q ^ E) := by
        rw [hgeom]
  have hfactor :
      T = ((A ^ M : Polynomial K) : PowerSeries K) * dilate (Q ^ E) T := by
    rw [← power_card_pow_eq_dilate T E]
    simpa [Q] using hfactorPower
  have hDpowM : D ∣ A ^ M :=
    hDpow.trans (pow_dvd_pow A hNM)
  obtain ⟨C, hC⟩ := hDpowM
  let U := ((P * C : Polynomial K) : PowerSeries K) * dilate (Q ^ E) T
  have hU : (D : PowerSeries K) * U = (P : PowerSeries K) * T := by
    calc
      (D : PowerSeries K) * U =
          (P : PowerSeries K) *
            (((D * C : Polynomial K) : PowerSeries K) * dilate (Q ^ E) T) := by
              dsimp [U]
              simp only [Polynomial.coe_mul]
              ring
      _ = (P : PowerSeries K) *
          (((A ^ M : Polynomial K) : PowerSeries K) * dilate (Q ^ E) T) := by
            rw [hC]
      _ = (P : PowerSeries K) * T := by rw [← hfactor]
  have hrep : U = rationalMultiple P D T :=
    eq_rationalMultiple_of_denominator P D T U hD0 hU
  rw [← hrep]
  exact (hseed.dilate_pow hQ E).polynomial_mul (P * C)

end IndependentZeroBlocks

#print axioms IndependentZeroBlocks.HasSeedBlocks.dilate_pow
#print axioms IndependentZeroBlocks.power_card_pow_eq_dilate
#print axioms IndependentZeroBlocks.HasSeedBlocks.rationalMultiple_of_dvd_kernel_pow
