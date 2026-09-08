import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

/-!
# Ordered digit products and absorbing zero words

Digits are little-endian, so low digits multiply on the left. No commutativity
is assumed. The normalization at digit zero makes leading-zero padding inert.
-/

namespace IndependentZeroBlocks

def monoidDigitProduct {M : Type*} [Monoid M]
    (b : ℕ) (a : ℕ → M) (n : ℕ) : M :=
  ((Nat.digits b n).map a).prod

@[simp] theorem monoidDigitProduct_zero {M : Type*} [Monoid M]
    (b : ℕ) (a : ℕ → M) : monoidDigitProduct b a 0 = 1 := by
  simp [monoidDigitProduct]

/-- The low radix digit is the leftmost factor. -/
theorem monoidDigitProduct_mul_add {M : Type*} [Monoid M]
    (b : ℕ) (hb : 2 ≤ b) (a : ℕ → M) (ha0 : a 0 = 1)
    (n r : ℕ) (hr : r < b) :
    monoidDigitProduct b a (b * n + r) = a r * monoidDigitProduct b a n := by
  by_cases hz : r = 0 ∧ n = 0
  · rcases hz with ⟨rfl, rfl⟩
    simp [ha0]
  · have hnz : r ≠ 0 ∨ n ≠ 0 := by
      by_cases hr0 : r = 0
      · exact Or.inr fun hn0 => hz ⟨hr0, hn0⟩
      · exact Or.inl hr0
    unfold monoidDigitProduct
    rw [show b * n + r = r + b * n by omega]
    rw [Nat.digits_add b (by omega) r n hr hnz]
    simp

/-- A low block multiplies before the high block, including zero padding. -/
theorem monoidDigitProduct_pow_mul_add {M : Type*} [Monoid M]
    (b : ℕ) (hb : 2 ≤ b) (a : ℕ → M) (ha0 : a 0 = 1)
    (e q r : ℕ) (hr : r < b ^ e) :
    monoidDigitProduct b a (b ^ e * q + r) =
      monoidDigitProduct b a r * monoidDigitProduct b a q := by
  induction e generalizing q r with
  | zero =>
    have hr0 : r = 0 := by simpa using hr
    subst r
    simp
  | succ e ih =>
    have hbpos : 0 < b := by omega
    have hd : r % b < b := Nat.mod_lt r hbpos
    have hm : r / b < b ^ e := by
      apply (Nat.div_lt_iff_lt_mul hbpos).2
      simpa [pow_succ, Nat.mul_comm] using hr
    have hsplit : b * (r / b) + r % b = r := Nat.div_add_mod r b
    have hi : b ^ (e + 1) * q + r =
        b * (b ^ e * q + r / b) + r % b := by
      rw [pow_succ]
      nlinarith
    rw [hi, monoidDigitProduct_mul_add b hb a ha0 _ _ hd, ih q (r / b) hm]
    rw [← mul_assoc, ← monoidDigitProduct_mul_add b hb a ha0 _ _ hd, hsplit]

/-- Evaluating any bounded digit word agrees with its ordered product, even
when the word has leading zero digits in little-endian notation. -/
theorem monoidDigitProduct_ofDigits {M : Type*} [Monoid M]
    (b : ℕ) (hb : 2 ≤ b) (a : ℕ → M) (ha0 : a 0 = 1)
    (w : List ℕ) (hw : ∀ d ∈ w, d < b) :
    monoidDigitProduct b a (Nat.ofDigits b w) = (w.map a).prod := by
  induction w with
  | nil => simp
  | cons d w ih =>
    have hd : d < b := hw d (by simp)
    have htail : ∀ z ∈ w, z < b := fun z hz => hw z (by simp [hz])
    rw [Nat.ofDigits_cons, Nat.add_comm,
      monoidDigitProduct_mul_add b hb a ha0 _ d hd, ih htail]
    simp

/-- Appending leading zero digits does not change the word product. -/
theorem monoidDigitWord_append_zero_padding {M : Type*} [Monoid M]
    (a : ℕ → M) (ha0 : a 0 = 1) (w : List ℕ) (k : ℕ) :
    ((w ++ List.replicate k 0).map a).prod = (w.map a).prod := by
  simp [ha0]

/-- The normalized ordered radix recurrence determines all coefficients. -/
theorem monoidDigitProduct_eq_of_recursion {M : Type*} [Monoid M]
    (b : ℕ) (hb : 2 ≤ b) (a : ℕ → M) (ha0 : a 0 = 1)
    (f : ℕ → M) (hf0 : f 0 = 1)
    (hf : ∀ n r, r < b → f (b * n + r) = a r * f n) (n : ℕ) :
    f n = monoidDigitProduct b a n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      simp [hf0]
    · have hlt : n / b < n := Nat.div_lt_self (by omega) (by omega)
      have hr : n % b < b := Nat.mod_lt n (by omega)
      have hs : b * (n / b) + n % b = n := Nat.div_add_mod n b
      calc
        f n = f (b * (n / b) + n % b) := by rw [hs]
        _ = a (n % b) * f (n / b) := hf _ _ hr
        _ = a (n % b) * monoidDigitProduct b a (n / b) := by rw [ih _ hlt]
        _ = monoidDigitProduct b a (b * (n / b) + n % b) :=
          (monoidDigitProduct_mul_add b hb a ha0 _ _ hr).symm
        _ = monoidDigitProduct b a n := by rw [hs]

/-- Consecutive blocks of `ell` digits can be treated as single digits in
radix `b^ell`, without changing their noncommutative order. -/
theorem monoidDigitProduct_regroup_radix {M : Type*} [Monoid M]
    (b : ℕ) (hb : 2 ≤ b) (a : ℕ → M) (ha0 : a 0 = 1)
    (ell : ℕ) (hell : 0 < ell) (n : ℕ) :
    monoidDigitProduct (b ^ ell) (monoidDigitProduct b a) n =
      monoidDigitProduct b a n := by
  have hB : 2 ≤ b ^ ell := by
    have hp := Nat.le_self_pow (show ell ≠ 0 by omega) b
    omega
  symm
  apply monoidDigitProduct_eq_of_recursion (b ^ ell) hB
    (monoidDigitProduct b a) (by simp) (monoidDigitProduct b a) (by simp) _ n
  intro q r hr
  exact monoidDigitProduct_pow_mul_add b hb a ha0 ell q r hr

/-- A nonempty mortal digit word is equivalent to a zero coefficient. -/
theorem monoidDigitProduct_exists_zero_iff_zero_word
    {M : Type*} [MonoidWithZero M] [Nontrivial M]
    (b : ℕ) (hb : 2 ≤ b) (a : ℕ → M) (ha0 : a 0 = 1) :
    (∃ n : ℕ, monoidDigitProduct b a n = 0) ↔
      ∃ w : List ℕ, w ≠ [] ∧ (∀ d ∈ w, d < b) ∧ (w.map a).prod = 0 := by
  constructor
  · rintro ⟨n, hn⟩
    have hn0 : n ≠ 0 := by
      intro hz
      subst n
      simp at hn
    exact ⟨Nat.digits b n, Nat.digits_ne_nil_iff_ne_zero.mpr hn0,
      fun d hd => Nat.digits_lt_base (by omega) hd, hn⟩
  · rintro ⟨w, _, hw, hz⟩
    exact ⟨Nat.ofDigits b w, by rw [monoidDigitProduct_ofDigits b hb a ha0 w hw, hz]⟩

/-- A zero coefficient provides a positive-width, nonzero missing block
digit for radix regrouping and support geometry. -/
theorem monoidDigitProduct_exists_bounded_zero_block
    {M : Type*} [MonoidWithZero M] [Nontrivial M]
    (b : ℕ) (hb : 2 ≤ b) (a : ℕ → M)
    (hz : ∃ n, monoidDigitProduct b a n = 0) :
    ∃ ell w : ℕ, 0 < ell ∧ 0 < w ∧ w < b ^ ell ∧
      monoidDigitProduct b a w = 0 := by
  obtain ⟨n, hn⟩ := hz
  have hn0 : n ≠ 0 := by
    intro h
    subst n
    simp at hn
  have hd : Nat.digits b n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn0
  have hlen : 0 < (Nat.digits b n).length := List.length_pos_iff.mpr hd
  have hbound := Nat.ofDigits_lt_base_pow_length (by omega : 1 < b)
    (fun d (h : d ∈ Nat.digits b n) => Nat.digits_lt_base (by omega) h)
  rw [Nat.ofDigits_digits] at hbound
  exact ⟨(Nat.digits b n).length, n, hlen, Nat.pos_of_ne_zero hn0, hbound, hn⟩

/-- A mortal word annihilates any word containing it as a contiguous factor. -/
theorem monoidDigitWord_zero_of_factor
    {M : Type*} [MonoidWithZero M] (a : ℕ → M)
    (u w v : List ℕ) (hw : (w.map a).prod = 0) :
    ((u ++ w ++ v).map a).prod = 0 := by
  simp [hw]

/-- Any zero coefficient can be inserted between arbitrary low and high
blocks. This is a two-sided absorbing factor, not a commutative argument. -/
theorem monoidDigitProduct_zero_cylinder
    {M : Type*} [MonoidWithZero M]
    (b : ℕ) (hb : 2 ≤ b) (a : ℕ → M) (ha0 : a 0 = 1)
    (ell w : ℕ) (hw : w < b ^ ell) (hzero : monoidDigitProduct b a w = 0)
    (k q j : ℕ) (hj : j < b ^ k) :
    monoidDigitProduct b a (b ^ (k + ell) * q + b ^ k * w + j) = 0 := by
  have hi : b ^ (k + ell) * q + b ^ k * w + j =
      b ^ k * (b ^ ell * q + w) + j := by rw [pow_add]; ring
  rw [hi, monoidDigitProduct_pow_mul_add b hb a ha0 k _ j hj,
    monoidDigitProduct_pow_mul_add b hb a ha0 ell q w hw, hzero,
    zero_mul, mul_zero]

/-- The word formulation supplies the block width and coefficient value
needed by the cylinder theorem. -/
theorem monoidDigitProduct_zero_word_cylinder
    {M : Type*} [MonoidWithZero M]
    (b : ℕ) (hb : 2 ≤ b) (a : ℕ → M) (ha0 : a 0 = 1)
    (w : List ℕ) (hw : ∀ d ∈ w, d < b) (hz : (w.map a).prod = 0)
    (k q j : ℕ) (hj : j < b ^ k) :
    monoidDigitProduct b a
      (b ^ (k + w.length) * q + b ^ k * Nat.ofDigits b w + j) = 0 := by
  apply monoidDigitProduct_zero_cylinder b hb a ha0 w.length (Nat.ofDigits b w)
    (Nat.ofDigits_lt_base_pow_length (by omega) hw) _ k q j hj
  rw [monoidDigitProduct_ofDigits b hb a ha0 w hw, hz]

/-- A specified zero block at any digit position annihilates the product. -/
theorem monoidDigitProduct_zero_of_block_digit
    {M : Type*} [MonoidWithZero M]
    (b : ℕ) (hb : 2 ≤ b) (a : ℕ → M) (ha0 : a 0 = 1)
    (ell w : ℕ) (hw : w < b ^ ell) (hz : monoidDigitProduct b a w = 0)
    (n k : ℕ) (hn : (n / b ^ k) % b ^ ell = w) :
    monoidDigitProduct b a n = 0 := by
  have hp : 0 < b ^ k := pow_pos (by omega) k
  have hlo := Nat.div_add_mod n (b ^ k)
  have hhi := Nat.div_add_mod (n / b ^ k) (b ^ ell)
  rw [hn] at hhi
  rw [← hlo, monoidDigitProduct_pow_mul_add b hb a ha0 k
    (n / b ^ k) (n % b ^ k) (Nat.mod_lt n hp)]
  rw [← hhi, monoidDigitProduct_pow_mul_add b hb a ha0 ell _ w hw, hz,
    zero_mul, mul_zero]

/-- Every supported index avoids the mortal word at all aligned block
positions in radix `b^ell`. -/
theorem monoidDigitProduct_support_avoids_aligned_digit
    {M : Type*} [MonoidWithZero M]
    (b : ℕ) (hb : 2 ≤ b) (a : ℕ → M) (ha0 : a 0 = 1)
    (ell w : ℕ) (hw : w < b ^ ell) (hz : monoidDigitProduct b a w = 0)
    (n : ℕ) (hn : monoidDigitProduct b a n ≠ 0) (k : ℕ) :
    (n / (b ^ ell) ^ k) % b ^ ell ≠ w := by
  intro hd
  apply hn
  apply monoidDigitProduct_zero_of_block_digit b hb a ha0 ell w hw hz n (ell * k)
  simpa [pow_mul] using hd

/-- Equivalently, a supported index has no mortal block among its canonical
digits in the regrouped radix. This is a direct support-containment interface
for a scalar missing-digit model. -/
theorem monoidDigitProduct_support_avoids_regrouped_digits
    {M : Type*} [MonoidWithZero M]
    (b : ℕ) (hb : 2 ≤ b) (a : ℕ → M) (ha0 : a 0 = 1)
    (ell : ℕ) (hell : 0 < ell) (w : ℕ)
    (hz : monoidDigitProduct b a w = 0)
    (n : ℕ) (hn : monoidDigitProduct b a n ≠ 0) :
    w ∉ Nat.digits (b ^ ell) n := by
  intro hw
  have hmem : (0 : M) ∈ (Nat.digits (b ^ ell) n).map (monoidDigitProduct b a) :=
    List.mem_map.mpr ⟨w, hw, hz⟩
  have hp := List.prod_eq_zero hmem
  change monoidDigitProduct (b ^ ell) (monoidDigitProduct b a) n = 0 at hp
  rw [monoidDigitProduct_regroup_radix b hb a ha0 ell hell n] at hp
  exact hn hp

end IndependentZeroBlocks
