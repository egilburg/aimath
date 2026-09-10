import SierpinskiFormal.MonoidDigitProduct
import SierpinskiFormal.UniformPowerClosure

set_option autoImplicit false

namespace IndependentZeroBlocks

open SierpinskiFormal
open scoped BigOperators

/-- A scalar digit polynomial which permits every digit below `B` except
`w`. -/
noncomputable def oneForbiddenDigitPolynomial
    (B w : ℕ) : Polynomial ℚ :=
  ∑ d ∈ (Finset.range B).erase w, Polynomial.monomial d 1

@[simp] theorem coeff_oneForbiddenDigitPolynomial (B w n : ℕ) :
    (oneForbiddenDigitPolynomial B w).coeff n =
      if n < B ∧ n ≠ w then 1 else 0 := by
  classical
  simp [oneForbiddenDigitPolynomial, Polynomial.coeff_monomial,
    and_comm]

/-- The scalar forbidden-digit model has exactly `B-1` supported radix
digits. -/
theorem radixDigitSupportCount_oneForbiddenDigitPolynomial
    {B w : ℕ} (hw : w < B) :
    radixDigitSupportCount B (oneForbiddenDigitPolynomial B w) = B - 1 := by
  classical
  simp [radixDigitSupportCount, coeff_oneForbiddenDigitPolynomial, hw]
  have hfin : (Finset.range B).filter (fun d => d < B ∧ d ≠ w) =
      (Finset.range B).erase w := by
    ext d
    simp
    tauto
  rw [hfin, Finset.card_erase_of_mem (Finset.mem_range.mpr hw)]
  simp

/-- A zero regrouped digit must be positive under normalization. -/
private theorem zero_regrouped_digit_pos
    {M : Type*} [MonoidWithZero M] [Nontrivial M]
    {b : ℕ} {a : ℕ → M} {w : ℕ}
    (hz : monoidDigitProduct b a w = 0) : 0 < w := by
  by_contra hw
  have : w = 0 := Nat.eq_zero_of_not_pos hw
  subst w
  simp at hz

/-- Support of a monoid digit product with a mortal regrouped digit is
contained in the corresponding scalar forbidden-digit support. -/
theorem monoidDigitProduct_support_subset_forbiddenDigit
    {M : Type*} [MonoidWithZero M] [Nontrivial M]
    (b : ℕ) (hb : 2 ≤ b) (a : ℕ → M) (ha0 : a 0 = 1)
    (ell : ℕ) (hell : 0 < ell) (w : ℕ)
    (hz : monoidDigitProduct b a w = 0)
    (n : ℕ) (hn : monoidDigitProduct b a n ≠ 0) :
    PowerSeries.coeff n
      (canonicalSeries (b ^ ell) (oneForbiddenDigitPolynomial (b ^ ell) w)) ≠ 0 := by
  have havoid := monoidDigitProduct_support_avoids_regrouped_digits
    b hb a ha0 ell hell w hz n hn
  have hB : 2 ≤ b ^ ell := by
    have hp := Nat.le_self_pow (by omega : ell ≠ 0) b
    omega
  rw [coeff_canonicalSeries]
  apply List.prod_ne_zero
  intro hzero
  obtain ⟨d, hd, hd0⟩ := List.mem_map.mp hzero
  have hdB : d < b ^ ell := Nat.digits_lt_base (by omega) hd
  have hdw : d ≠ w := by
    intro heq
    subst d
    exact havoid hd
  rw [coeff_oneForbiddenDigitPolynomial, if_pos ⟨hdB, hdw⟩] at hd0
  norm_num at hd0

/-- At regrouped radix powers, mortal-word support is bounded by the number
of words which avoid the forbidden digit. -/
theorem predicateCount_monoidDigitProduct_pow_le_forbiddenWord
    {M : Type*} [MonoidWithZero M] [Nontrivial M]
    (b : ℕ) (hb : 2 ≤ b) (a : ℕ → M) (ha0 : a 0 = 1)
    (ell : ℕ) (hell : 0 < ell) (w : ℕ) (hw : w < b ^ ell)
    (hz : monoidDigitProduct b a w = 0) (k : ℕ) :
    predicateCount (fun n => monoidDigitProduct b a n ≠ 0)
        ((b ^ ell) ^ k) ≤ ((b ^ ell) - 1) ^ k := by
  classical
  let A := oneForbiddenDigitPolynomial (b ^ ell) w
  calc
    predicateCount (fun n => monoidDigitProduct b a n ≠ 0) ((b ^ ell) ^ k) ≤
        supportCount (canonicalSeries (b ^ ell) A) ((b ^ ell) ^ k) := by
      unfold predicateCount supportCount
      apply Finset.card_le_card
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
      exact ⟨hn.1, monoidDigitProduct_support_subset_forbiddenDigit
        b hb a ha0 ell hell w hz n hn.2⟩
    _ = radixDigitSupportCount (b ^ ell) A ^ k :=
      supportCount_canonicalSeries_pow_eq_digitSupport (b ^ ell)
        (by have := Nat.le_self_pow (by omega : ell ≠ 0) b; omega)
        A (by
          have hwpos := zero_regrouped_digit_pos hz
          simp [A, coeff_oneForbiddenDigitPolynomial, hwpos, Nat.ne_of_lt hwpos,
            pow_pos (by omega : 0 < b) ell]) k
    _ = ((b ^ ell) - 1) ^ k := by
      rw [radixDigitSupportCount_oneForbiddenDigitPolynomial hw]

/-- A mortal regrouped digit gives a uniform translated support bound with
the forbidden-word exponent `log(B-1)/log(B)`, where `B=b^ell`. -/
theorem monoidDigitProduct_uniformMortalWordIntervalBound
    {M : Type*} [MonoidWithZero M] [Nontrivial M]
    (b : ℕ) (hb : 2 ≤ b) (a : ℕ → M) (ha0 : a 0 = 1)
    (ell : ℕ) (hell : 0 < ell) (w : ℕ) (hw : w < b ^ ell)
    (hz : monoidDigitProduct b a w = 0) :
    HasUniformPowerIntervalBound
      (Real.log (((b ^ ell) - 1 : ℕ) : ℝ) / Real.log ((b ^ ell : ℕ) : ℝ))
      (fun n => monoidDigitProduct b a n ≠ 0) := by
  let B := b ^ ell
  let A := oneForbiddenDigitPolynomial B w
  have hB : 2 ≤ B := by
    dsimp [B]
    have hp := Nat.le_self_pow (by omega : ell ≠ 0) b
    omega
  have hwpos := zero_regrouped_digit_pos hz
  have hA0 : A.coeff 0 = 1 := by
    simp [A, coeff_oneForbiddenDigitPolynomial, hwpos, Nat.ne_of_lt hwpos,
      B, pow_pos (by omega : 0 < b) ell]
  have hs : radixDigitSupportCount B A = B - 1 := by
    exact radixDigitSupportCount_oneForbiddenDigitPolynomial (by simpa [B] using hw)
  have hsmall : radixDigitSupportCount B A < B := by rw [hs]; omega
  have hscalar := canonicalSeries_hasUniformDigitLogIntervalBound
    B hB A hA0 hsmall
  have hmono := hscalar.mono (fun n hn => by
    simpa [B, A] using
      monoidDigitProduct_support_subset_forbiddenDigit
        b hb a ha0 ell hell w hz n hn)
  simpa [digitSupportExponent, hs, B] using hmono

/-- Explicit-constant form of the mortal-word translated interval bound. -/
theorem intervalPredicateCount_monoidDigitProduct_le_mortalWordExponent
    {M : Type*} [MonoidWithZero M] [Nontrivial M]
    (b : ℕ) (hb : 2 ≤ b) (a : ℕ → M) (ha0 : a 0 = 1)
    (ell : ℕ) (hell : 0 < ell) (w : ℕ) (hw : w < b ^ ell)
    (hz : monoidDigitProduct b a w = 0)
    (start L : ℕ) (hL : 1 ≤ L) :
    (intervalPredicateCount (fun n => monoidDigitProduct b a n ≠ 0)
      start L : ℝ) ≤
      ((2 * ((b ^ ell) - 1) : ℕ) : ℝ) *
        (L : ℝ) ^
          (Real.log (((b ^ ell) - 1 : ℕ) : ℝ) /
            Real.log ((b ^ ell : ℕ) : ℝ)) := by
  let B := b ^ ell
  let A := oneForbiddenDigitPolynomial B w
  have hB : 2 ≤ B := by
    dsimp [B]
    have hp := Nat.le_self_pow (by omega : ell ≠ 0) b
    omega
  have hwpos := zero_regrouped_digit_pos hz
  have hA0 : A.coeff 0 = 1 := by
    simp [A, coeff_oneForbiddenDigitPolynomial, hwpos, Nat.ne_of_lt hwpos,
      B, pow_pos (by omega : 0 < b) ell]
  have hs : radixDigitSupportCount B A = B - 1 :=
    radixDigitSupportCount_oneForbiddenDigitPolynomial (by simpa [B] using hw)
  have hsmall : radixDigitSupportCount B A < B := by rw [hs]; omega
  have hcount : intervalPredicateCount
      (fun n => monoidDigitProduct b a n ≠ 0) start L ≤
      intervalPredicateCount
        (fun n => PowerSeries.coeff n (canonicalSeries B A) ≠ 0) start L := by
    classical
    unfold intervalPredicateCount
    apply Finset.card_le_card
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    exact ⟨hj.1, by
      simpa [B, A] using monoidDigitProduct_support_subset_forbiddenDigit
        b hb a ha0 ell hell w hz (start + j) hj.2⟩
  have hscalar := intervalPredicateCount_canonicalSeries_le_digitLog
    B hB A hA0 hsmall start L hL
  have hαeq : digitSupportExponent B A =
      Real.log ((B - 1 : ℕ) : ℝ) / Real.log (B : ℝ) := by
    simp [digitSupportExponent, hs]
  rw [hαeq, hs] at hscalar
  have hcountR : (intervalPredicateCount
      (fun n => monoidDigitProduct b a n ≠ 0) start L : ℝ) ≤
      (intervalPredicateCount
        (fun n => PowerSeries.coeff n (canonicalSeries B A) ≠ 0) start L : ℝ) := by
    exact_mod_cast hcount
  exact hcountR.trans (by simpa only [B] using hscalar)

end IndependentZeroBlocks
