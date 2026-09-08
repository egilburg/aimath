import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.FieldTheory.Finite.Basic

set_option autoImplicit false

/-!
# Prime-power and prime-to-characteristic parts of a period

This file separates a positive natural-number period into its characteristic
prime-power part and its coprime part, and records the period of the associated
divisibility indicator.
-/

namespace SierpinskiFormal

/-- Split a positive period into its `p`-power part and a positive part not
divisible by `p`. -/
theorem exists_primePower_coprime_decomposition
    (p m : ℕ) (hp : p.Prime) (hm : 0 < m) :
    ∃ e s : ℕ,
      0 < s ∧ m = p ^ e * s ∧ ¬p ∣ s ∧ (p ^ e).Coprime s := by
  obtain ⟨e, s, hps, hsplit⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (Nat.ne_of_gt hm) p hp.ne_one
  have hspos : 0 < s := by
    by_contra hs
    have hs0 : s = 0 := by omega
    rw [hs0, Nat.mul_zero] at hsplit
    omega
  exact ⟨e, s, hspos, hsplit, hps,
    (hp.coprime_pow_of_not_dvd hps).symm⟩

/-- The decomposition specialized to the characteristic of a finite field. -/
theorem exists_finiteField_primePower_coprime_decomposition
    {K : Type*} [Field K] [Fintype K]
    (p m : ℕ) [CharP K p] (hm : 0 < m) :
    ∃ e s : ℕ,
      0 < s ∧ m = p ^ e * s ∧ ¬p ∣ s ∧ (p ^ e).Coprime s := by
  exact exists_primePower_coprime_decomposition p m
    (CharP.char_is_prime K p) hm

/-- A characteristic prime power divides the matching power of the finite
field cardinality. -/
theorem charPow_dvd_cardPow
    {K : Type*} [Field K] [Fintype K]
    (p e : ℕ) [CharP K p] :
    p ^ e ∣ Fintype.card K ^ e := by
  obtain ⟨f, hp, hcard⟩ := FiniteField.card K p
  have hpdvd : p ∣ Fintype.card K := by
    rw [hcard]
    exact dvd_pow_self p f.ne_zero
  exact pow_dvd_pow_of_dvd hpdvd e

/-- The literal divisibility indicator is periodic with its modulus.  This
statement is definition-independent, so downstream files can rewrite their
chosen selector to the lambda below. -/
theorem divisibility_indicator_periodic
    (K : Type*) [Zero K] [One K] (H : ℕ) :
    Function.Periodic (fun n : ℕ => if H ∣ n then (1 : K) else 0) H := by
  intro n
  simp only [Nat.dvd_add_self_right]

/-- Consequently the `p^e` divisibility indicator has period `card K ^ e`,
the block size used by the grouped weighted-series argument. -/
theorem divisibility_indicator_period_cardPow
    {K : Type*} [Field K] [Fintype K]
    (p e : ℕ) [CharP K p] :
    Function.Periodic
      (fun n : ℕ => if p ^ e ∣ n then (1 : K) else 0)
      (Fintype.card K ^ e) := by
  have hdvd : p ^ e ∣ Fintype.card K ^ e := charPow_dvd_cardPow p e
  obtain ⟨a, ha⟩ := hdvd
  rw [ha]
  simpa [Nat.mul_comm] using
    (divisibility_indicator_periodic K (p ^ e)).nsmul a

end SierpinskiFormal

#print axioms SierpinskiFormal.exists_finiteField_primePower_coprime_decomposition
#print axioms SierpinskiFormal.divisibility_indicator_period_cardPow
