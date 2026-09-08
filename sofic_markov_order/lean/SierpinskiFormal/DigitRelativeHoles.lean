import SierpinskiFormal.ExactDigitSupport
import SierpinskiFormal.UniformRelativeHoles

set_option autoImplicit false

/-!
# Uniform relative holes from a missing radix digit

A missing digit in a canonical digit-product series creates a zero child
inside every aligned radix block.  At a radix scale adapted to an arbitrary
long interval, one such child occupies a fixed positive fraction of the
interval.
-/

namespace IndependentZeroBlocks

open SierpinskiFormal

/-- A missing digit makes the actual radix digit support strictly smaller than
the radix. -/
theorem radixDigitSupportCount_lt_of_missingDigit
    {K : Type*} [Field K] (b : ℕ)
    (A : Polynomial K) (d : ℕ) (hd : d < b) (hAd : A.coeff d = 0) :
    radixDigitSupportCount b A < b := by
  classical
  let D := (Finset.range b).filter fun x => A.coeff x ≠ 0
  have hproper : D ⊂ Finset.range b := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨?_, ?_⟩
    · intro x hx
      exact (Finset.mem_filter.mp hx).1
    · intro heq
      have hmem : d ∈ D := by
        rw [heq]
        exact Finset.mem_range.mpr hd
      exact (Finset.mem_filter.mp hmem).2 hAd
  have hcard := Finset.card_lt_card hproper
  simpa [D, radixDigitSupportCount] using hcard

/-- The support predicate of a canonical series has uniform relative holes as
soon as one radix digit is missing.  One may take constant `b⁻³` and cutoff
`b²`. -/
theorem canonicalSeries_support_hasUniformRelativeHoles_of_missingDigit
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (d : ℕ) (hd : d < b) (hAd : A.coeff d = 0) :
    HasUniformRelativeHoles
      (fun n => PowerSeries.coeff n (canonicalSeries b A) ≠ 0) := by
  refine ⟨1 / (b : ℝ) ^ 3, by positivity, b ^ 2, ?_⟩
  intro a L hL
  have hLpos : L ≠ 0 := by
    have : 0 < b ^ 2 := by positivity
    omega
  let t := Nat.log b L
  have ht2 : 2 ≤ t := by
    apply Nat.le_log_of_pow_le (by omega)
    simpa [t] using hL
  let k := t - 2
  have htk : t = k + 2 := by
    dsimp [k]
    omega
  let M := b ^ k
  let B := b ^ (k + 1)
  let q := a / B + 1
  let p := B * q
  let n := p + d * M
  have hMpos : 0 < M := by positivity
  have hBpos : 0 < B := by positivity
  have hpowLower : b ^ (k + 2) ≤ L := by
    rw [← htk]
    simpa [t] using Nat.pow_log_le_self b hLpos
  have htwoB : 2 * B ≤ L := by
    calc
      2 * B ≤ b * B := Nat.mul_le_mul_right B hb
      _ = b ^ (k + 2) := by
        simp [B, pow_succ, Nat.mul_comm]
      _ ≤ L := hpowLower
  have hap : a ≤ p := by
    have h := (Nat.lt_mul_div_succ a hBpos).le
    simpa [p, q] using h
  have hpaB : p ≤ a + B := by
    calc
      p = a / B * B + B := by
        simp [p, q]
        ring
      _ ≤ a + B := Nat.add_le_add_right (Nat.div_mul_le_self a B) B
  have hchild : d * M + M ≤ B := by
    calc
      d * M + M = (d + 1) * M := by ring
      _ ≤ b * M :=
        Nat.mul_le_mul_right M (Nat.succ_le_iff.mpr hd)
      _ = B := by
        simp [B, M, pow_succ, Nat.mul_comm]
  have hnstart : a ≤ n := hap.trans (Nat.le_add_right p (d * M))
  have hnend : n + M ≤ a + L := by
    calc
      n + M = p + (d * M + M) := by simp [n]; ring
      _ ≤ p + B := Nat.add_le_add_left hchild p
      _ ≤ a + B + B := Nat.add_le_add_right hpaB B
      _ = a + 2 * B := by ring
      _ ≤ a + L := Nat.add_le_add_left htwoB a
  have hpowUpper : L ≤ b ^ 3 * M := by
    have hlt := Nat.lt_pow_succ_log_self (by omega : 1 < b) L
    have htSucc : t + 1 = k + 3 := by omega
    have hlt' : L < b ^ (k + 3) := by
      simpa [t, htSucc] using hlt
    have hlt'' : L < b ^ 3 * M := by
      simpa [M, pow_add, Nat.mul_comm] using hlt'
    exact Nat.le_of_lt hlt''
  have hrelative :
      (1 / (b : ℝ) ^ 3) * (L : ℝ) ≤ (M : ℝ) := by
    rw [one_div_mul_eq_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (b : ℝ) ^ 3)).2
    have hpowUpper' : L ≤ M * b ^ 3 := by
      simpa [Nat.mul_comm] using hpowUpper
    exact_mod_cast hpowUpper'
  refine ⟨n, M, hnstart, hnend, hrelative, ?_⟩
  intro j hj
  rw [not_ne_iff]
  simpa [n, p, B, M, add_assoc] using
    coeff_canonicalSeries_eq_zero_on_missingDigit_cylinder
      b hb A hA0 d hd hAd k q j hj

/-- A strict deficit in the actual radix digit support supplies a missing digit,
and therefore uniform relative holes in the canonical support. -/
theorem canonicalSeries_support_hasUniformRelativeHoles_of_digitSupport_lt
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hsmall : radixDigitSupportCount b A < b) :
    HasUniformRelativeHoles
      (fun n => PowerSeries.coeff n (canonicalSeries b A) ≠ 0) := by
  classical
  let D := (Finset.range b).filter fun d => A.coeff d ≠ 0
  have hcard : D.card < (Finset.range b).card := by
    simpa [D, radixDigitSupportCount] using hsmall
  obtain ⟨d, hd, hnot⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hcard
  have hAd : A.coeff d = 0 := by
    by_contra hne
    exact hnot (Finset.mem_filter.mpr ⟨hd, hne⟩)
  exact canonicalSeries_support_hasUniformRelativeHoles_of_missingDigit
    b hb A hA0 d (Finset.mem_range.mp hd) hAd

/-- The traditional strict degree condition also gives uniform relative holes:
the digit at position `b - 1` is absent. -/
theorem canonicalSeries_support_hasUniformRelativeHoles_of_natDegree_lt
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b - 1) :
    HasUniformRelativeHoles
      (fun n => PowerSeries.coeff n (canonicalSeries b A) ≠ 0) := by
  apply canonicalSeries_support_hasUniformRelativeHoles_of_missingDigit
    b hb A hA0 (b - 1) (by omega)
  exact Polynomial.coeff_eq_zero_of_natDegree_lt hdegree

end IndependentZeroBlocks
