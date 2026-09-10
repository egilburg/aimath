import SierpinskiFormal.MortalWordCounting

set_option autoImplicit false
namespace IndependentZeroBlocks
open SierpinskiFormal

/-- A predicate excluded by one fixed radix digit avoids that digit in the
canonical radix expansion of every point where it holds. -/
theorem predicate_avoids_digit_of_zeroCylinder
    (bad : ℕ → Prop) (B w : ℕ) (hB : 2 ≤ B) (_hw : w < B)
    (hcylinder : ∀ k q j : ℕ, j < B ^ k →
      ¬bad (B ^ (k + 1) * q + B ^ k * w + j))
    (n : ℕ) (hn : bad n) : w ∉ Nat.digits B n := by
  intro hwdigits
  obtain ⟨low, high, hdigits⟩ := List.append_of_mem hwdigits
  let k := low.length
  let q := Nat.ofDigits B high
  let j := Nat.ofDigits B low
  have hlow : ∀ d ∈ low, d < B := by
    intro d hd
    apply Nat.digits_lt_base (by omega)
    rw [hdigits]
    simp [hd]
  have hj : j < B ^ k := by
    exact Nat.ofDigits_lt_base_pow_length (by omega) hlow
  have hnDigits := (Nat.ofDigits_digits B n).symm
  rw [hdigits] at hnDigits
  have heq : B ^ (k + 1) * q + B ^ k * w + j = n := by
    dsimp only [k, q, j]
    rw [Nat.ofDigits_append, Nat.ofDigits_cons] at hnDigits
    rw [hnDigits]
    simp only [List.length, pow_succ]
    ring
  exact (hcylinder k q j hj) (by simpa only [heq] using hn)

/-- Support of any predicate with a fixed zero digit cylinder is contained
in the canonical one-forbidden-digit scalar model. -/
theorem predicate_support_subset_forbiddenDigit_of_zeroCylinder
    (bad : ℕ → Prop) (B w : ℕ) (hB : 2 ≤ B) (hw : w < B)
    (hcylinder : ∀ k q j : ℕ, j < B ^ k →
      ¬bad (B ^ (k + 1) * q + B ^ k * w + j))
    (n : ℕ) (hn : bad n) :
    PowerSeries.coeff n
      (canonicalSeries B (oneForbiddenDigitPolynomial B w)) ≠ 0 := by
  have havoid := predicate_avoids_digit_of_zeroCylinder bad B w hB hw hcylinder n hn
  rw [coeff_canonicalSeries]
  apply List.prod_ne_zero
  intro hzero
  obtain ⟨d, hd, hd0⟩ := List.mem_map.mp hzero
  have hdB : d < B := Nat.digits_lt_base (by omega) hd
  have hdw : d ≠ w := by
    intro heq
    subst d
    exact havoid hd
  rw [coeff_oneForbiddenDigitPolynomial, if_pos ⟨hdB, hdw⟩] at hd0
  norm_num at hd0

/-- If the forbidden digit is zero, the cylinder condition forces the
predicate to be empty. -/
theorem predicate_empty_of_zeroDigitCylinder
    (bad : ℕ → Prop) (B : ℕ) (hB : 2 ≤ B)
    (hcylinder : ∀ k q j : ℕ, j < B ^ k →
      ¬bad (B ^ (k + 1) * q + B ^ k * 0 + j)) :
    ∀ n, ¬bad n := by
  intro n hn
  have hnot := hcylinder n 0 n (Nat.lt_pow_self (by omega : 1 < B))
  apply hnot
  simpa using hn

/-- At radix powers, a fixed zero digit cylinder leaves at most `(B-1)^k`
possible exceptional indices. -/
theorem predicateCount_pow_le_of_zeroCylinder
    (bad : ℕ → Prop) (B w : ℕ) (hB : 2 ≤ B) (hw : w < B)
    (hcylinder : ∀ k q j : ℕ, j < B ^ k →
      ¬bad (B ^ (k + 1) * q + B ^ k * w + j))
    (k : ℕ) :
    predicateCount bad (B ^ k) ≤ (B - 1) ^ k := by
  classical
  by_cases hw0 : w = 0
  · subst w
    have hempty := predicate_empty_of_zeroDigitCylinder bad B hB hcylinder
    have hz : predicateCount bad (B ^ k) = 0 := by
      unfold predicateCount
      rw [Finset.card_eq_zero]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hnmem
      simp only [Finset.mem_filter, Finset.mem_range] at hnmem
      exact hempty n hnmem.2
    rw [hz]
    exact Nat.zero_le _
  · let A := oneForbiddenDigitPolynomial B w
    calc
      predicateCount bad (B ^ k) ≤ supportCount (canonicalSeries B A) (B ^ k) := by
        unfold predicateCount supportCount
        apply Finset.card_le_card
        intro n hn
        simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
        exact ⟨hn.1, by
          simpa only [A] using
            predicate_support_subset_forbiddenDigit_of_zeroCylinder
              bad B w hB hw hcylinder n hn.2⟩
      _ = radixDigitSupportCount B A ^ k := by
        apply supportCount_canonicalSeries_pow_eq_digitSupport B hB A
        rw [show A.coeff 0 = if 0 < B ∧ 0 ≠ w then 1 else 0 by
          exact coeff_oneForbiddenDigitPolynomial B w 0]
        simp [show 0 < B by omega, Ne.symm hw0]
      _ = (B - 1) ^ k := by
        rw [radixDigitSupportCount_oneForbiddenDigitPolynomial hw]

/-- Explicit uniform translated-interval count for every predicate excluded
by one fixed radix digit cylinder. -/
theorem intervalPredicateCount_le_of_zeroCylinder
    (bad : ℕ → Prop) (B w : ℕ) (hB : 2 ≤ B) (hw : w < B)
    (hcylinder : ∀ k q j : ℕ, j < B ^ k →
      ¬bad (B ^ (k + 1) * q + B ^ k * w + j))
    (start L : ℕ) (hL : 1 ≤ L) :
    (intervalPredicateCount bad start L : ℝ) ≤
      ((2 * (B - 1) : ℕ) : ℝ) *
        (L : ℝ) ^ (Real.log ((B - 1 : ℕ) : ℝ) / Real.log (B : ℝ)) := by
  classical
  by_cases hw0 : w = 0
  · subst w
    have hempty := predicate_empty_of_zeroDigitCylinder bad B hB hcylinder
    simp [intervalPredicateCount, hempty]
    positivity
  · let A := oneForbiddenDigitPolynomial B w
    have hA0 : A.coeff 0 = 1 := by
      rw [show A.coeff 0 = if 0 < B ∧ 0 ≠ w then 1 else 0 by
        exact coeff_oneForbiddenDigitPolynomial B w 0]
      simp [show 0 < B by omega, Ne.symm hw0]
    have hs : radixDigitSupportCount B A = B - 1 :=
      radixDigitSupportCount_oneForbiddenDigitPolynomial hw
    have hsmall : radixDigitSupportCount B A < B := by
      rw [hs]
      omega
    have hcount : intervalPredicateCount bad start L ≤
        intervalPredicateCount
          (fun n ↦ PowerSeries.coeff n (canonicalSeries B A) ≠ 0) start L := by
      unfold intervalPredicateCount
      apply Finset.card_le_card
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
      exact ⟨hj.1, by
        simpa only [A] using
          predicate_support_subset_forbiddenDigit_of_zeroCylinder
            bad B w hB hw hcylinder (start + j) hj.2⟩
    have hscalar := intervalPredicateCount_canonicalSeries_le_digitLog
      B hB A hA0 hsmall start L hL
    have hα : digitSupportExponent B A =
        Real.log ((B - 1 : ℕ) : ℝ) / Real.log (B : ℝ) := by
      simp [digitSupportExponent, hs]
    rw [hα, hs] at hscalar
    have hcountR : (intervalPredicateCount bad start L : ℝ) ≤
        (intervalPredicateCount
          (fun n ↦ PowerSeries.coeff n (canonicalSeries B A) ≠ 0) start L : ℝ) := by
      exact_mod_cast hcount
    exact hcountR.trans hscalar

/-- The explicit forbidden-digit exponent gives a uniform power interval
bound for an arbitrary predicate satisfying the zero-cylinder condition. -/
theorem hasUniformPowerIntervalBound_of_zeroCylinder
    (bad : ℕ → Prop) (B w : ℕ) (hB : 2 ≤ B) (hw : w < B)
    (hcylinder : ∀ k q j : ℕ, j < B ^ k →
      ¬bad (B ^ (k + 1) * q + B ^ k * w + j)) :
    HasUniformPowerIntervalBound
      (Real.log ((B - 1 : ℕ) : ℝ) / Real.log (B : ℝ)) bad := by
  refine ⟨((2 * (B - 1) : ℕ) : ℝ), by positivity, ?_⟩
  intro start L hL
  exact intervalPredicateCount_le_of_zeroCylinder bad B w hB hw hcylinder start L hL

end IndependentZeroBlocks
