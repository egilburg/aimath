import SierpinskiFormal.Lucas
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

set_option autoImplicit false

/-!
# Canonical normalized solutions of polynomial dilation equations

For a normalized polynomial `A` whose support lies below a radix `q`, its
canonical power series has at `n` the product of `A`'s coefficients over the
base-`q` digits of `n`.  This gives existence of a normalized solution of
`T = A * T(X^q)` without assuming a power series in advance.
-/

namespace IndependentZeroBlocks

open SierpinskiFormal

variable {R : Type*} [CommRing R]

/-- The canonical series attached to a polynomial kernel: its coefficient at
`n` is the product of the kernel coefficients at the base-`q` digits of `n`.
Digits are little-endian, though commutativity makes their order immaterial. -/
noncomputable def canonicalSeries (q : ℕ) (A : Polynomial R) : PowerSeries R :=
  PowerSeries.mk fun n => ((Nat.digits q n).map A.coeff).prod

@[simp] theorem coeff_canonicalSeries (q n : ℕ) (A : Polynomial R) :
    PowerSeries.coeff n (canonicalSeries q A) =
      ((Nat.digits q n).map A.coeff).prod := by
  simp [canonicalSeries]

/-- The canonical series is normalized, independently of the kernel: zero has
an empty base-`q` digit expansion. -/
@[simp] theorem coeff_zero_canonicalSeries (q : ℕ) (A : Polynomial R) :
    PowerSeries.coeff 0 (canonicalSeries q A) = 1 := by
  simp [canonicalSeries]

/-- Appending a low base-`q` digit multiplies the canonical coefficient by the
corresponding kernel coefficient.  The normalization assumption handles the
single exceptional representation `0 = q * 0 + 0`. -/
theorem coeff_canonicalSeries_mul_add
    (q : ℕ) (hq : 2 ≤ q) (A : Polynomial R) (hA0 : A.coeff 0 = 1)
    (m d : ℕ) (hd : d < q) :
    PowerSeries.coeff (q * m + d) (canonicalSeries q A) =
      PowerSeries.coeff m (canonicalSeries q A) * A.coeff d := by
  by_cases hzero : d = 0 ∧ m = 0
  · rcases hzero with ⟨rfl, rfl⟩
    simp [hA0]
  · have hnz : d ≠ 0 ∨ m ≠ 0 := by
      by_cases hd0 : d = 0
      · exact Or.inr fun hm0 => hzero ⟨hd0, hm0⟩
      · exact Or.inl hd0
    rw [coeff_canonicalSeries, coeff_canonicalSeries]
    rw [show q * m + d = d + q * m by omega]
    rw [Nat.digits_add q (by omega) d m hd hnz]
    simp [mul_comm]

/-- The canonical digit-product series solves the exact dilation equation for
every normalized kernel supported strictly below the radix. -/
theorem canonicalSeries_dilation_equation
    (q : ℕ) (hq : 2 ≤ q) (A : Polynomial R) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < q) :
    canonicalSeries q A = (A : PowerSeries R) * dilate q (canonicalSeries q A) := by
  ext n
  have hqpos : 0 < q := by omega
  have hmod : n % q < q := Nat.mod_lt n hqpos
  have hsplit : q * (n / q) + n % q = n := Nat.div_add_mod n q
  rw [← hsplit]
  rw [coeff_canonicalSeries_mul_add q hq A hA0 (n / q) (n % q) hmod]
  rw [coeff_polynomial_mul_dilate q hqpos A hdegree
    (canonicalSeries q A) (n / q) (n % q) hmod]

/-- Every normalized solution of the same polynomial dilation equation is the
canonical digit-product series. -/
theorem eq_canonicalSeries_of_dilation_equation
    (q : ℕ) (hq : 2 ≤ q) (A : Polynomial R) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < q) (T : PowerSeries R)
    (hT0 : PowerSeries.coeff 0 T = 1)
    (hT : T = (A : PowerSeries R) * dilate q T) :
    T = canonicalSeries q A := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n = 0
      · subst n
        simp [hT0]
      · have hqpos : 0 < q := by omega
        have hmod : n % q < q := Nat.mod_lt n hqpos
        have hdiv : n / q < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) hq
        have hsplit : q * (n / q) + n % q = n := Nat.div_add_mod n q
        calc
          PowerSeries.coeff n T =
              PowerSeries.coeff (q * (n / q) + n % q) T := by rw [hsplit]
          _ = PowerSeries.coeff (n / q) T * A.coeff (n % q) :=
            coeff_of_dilation_equation q hqpos A hdegree T hT
              (n / q) (n % q) hmod
          _ = PowerSeries.coeff (n / q) (canonicalSeries q A) *
              A.coeff (n % q) := by rw [ih (n / q) hdiv]
          _ = PowerSeries.coeff (q * (n / q) + n % q)
              (canonicalSeries q A) :=
            (coeff_canonicalSeries_mul_add q hq A hA0
              (n / q) (n % q) hmod).symm
          _ = PowerSeries.coeff n (canonicalSeries q A) := by rw [hsplit]

/-- Existence of a normalized solution follows from the canonical
construction; no separately supplied series or existence hypothesis is needed. -/
theorem exists_normalized_dilation_series
    (q : ℕ) (hq : 2 ≤ q) (A : Polynomial R) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < q) :
    ∃ T : PowerSeries R,
      PowerSeries.coeff 0 T = 1 ∧ T = (A : PowerSeries R) * dilate q T := by
  exact ⟨canonicalSeries q A, coeff_zero_canonicalSeries q A,
    canonicalSeries_dilation_equation q hq A hA0 hdegree⟩

/-- The normalized solution exists uniquely and is given by
`canonicalSeries`. -/
theorem existsUnique_normalized_dilation_series
    (q : ℕ) (hq : 2 ≤ q) (A : Polynomial R) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < q) :
    ∃! T : PowerSeries R,
      PowerSeries.coeff 0 T = 1 ∧ T = (A : PowerSeries R) * dilate q T := by
  refine ⟨canonicalSeries q A,
    ⟨coeff_zero_canonicalSeries q A,
      canonicalSeries_dilation_equation q hq A hA0 hdegree⟩, ?_⟩
  intro T hT
  exact eq_canonicalSeries_of_dilation_equation q hq A hA0 hdegree T hT.1 hT.2

/-- Over a finite field, the canonical dilation solution also satisfies the
algebraic branch equation from which the dilation identity normally arises. -/
theorem canonicalSeries_finiteField_branch
    {K : Type*} [Field K] [Fintype K]
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < Fintype.card K) :
    (A : PowerSeries K) *
        (canonicalSeries (Fintype.card K) A) ^ (Fintype.card K - 1) = 1 := by
  let q := Fintype.card K
  let T := canonicalSeries q A
  have hq : 2 ≤ q := by
    exact Fintype.one_lt_card
  have hT : T = (A : PowerSeries K) * dilate q T :=
    canonicalSeries_dilation_equation q hq A hA0 hdegree
  have hfrob : T ^ q = dilate q T := power_eq_dilate_finiteField T
  rw [← hfrob] at hT
  have hqsplit : q = (q - 1) + 1 := by omega
  have hfactor : T = ((A : PowerSeries K) * T ^ (q - 1)) * T := by
    rw [hqsplit, pow_succ, ← mul_assoc] at hT
    exact hT
  have hTne : T ≠ 0 := by
    intro hz
    have hz0 := congrArg (PowerSeries.coeff 0) hz
    simp [T, q] at hz0
  have hcancel : (1 : PowerSeries K) * T =
      ((A : PowerSeries K) * T ^ (q - 1)) * T := by
    simpa using hfactor
  have hone : (1 : PowerSeries K) = (A : PowerSeries K) * T ^ (q - 1) :=
    mul_right_cancel₀ hTne hcancel
  simpa [T, q] using hone.symm

end IndependentZeroBlocks

#print axioms IndependentZeroBlocks.canonicalSeries_dilation_equation
#print axioms IndependentZeroBlocks.exists_normalized_dilation_series
#print axioms IndependentZeroBlocks.existsUnique_normalized_dilation_series
#print axioms IndependentZeroBlocks.canonicalSeries_finiteField_branch
