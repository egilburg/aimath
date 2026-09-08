import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.FieldTheory.Finite.Basic
import Lean.Elab.Tactic.Omega

/-! Exact scalar Lucas identities from a formal-power-series dilation equation.

`dilate q T` is the coefficientwise definition of the substitution `T(X^q)`.
The equation assumed below is an equality of whole formal power series, not a
finite-prefix test. No Frobenius or reduction theorem is assumed implicitly.
-/

namespace SierpinskiFormal

open PowerSeries

variable {F : Type*} [CommRing F]

/-- Formal substitution of `X^q` for `X`, defined for positive `q` by its
coefficients. All uses below explicitly assume `0 < q`. -/
noncomputable def dilate (q : ℕ) (T : PowerSeries F) : PowerSeries F :=
  PowerSeries.mk fun n => if q ∣ n then PowerSeries.coeff (n / q) T else 0

@[simp] theorem coeff_dilate (q n : ℕ) (T : PowerSeries F) :
    PowerSeries.coeff n (dilate q T) =
      if q ∣ n then PowerSeries.coeff (n / q) T else 0 := by
  simp [dilate]

/-- Lift a polynomial Frobenius identity to every coefficient of an infinite
formal power series by truncating beyond that coefficient. -/
theorem power_eq_dilate_of_polynomial
    (q : ℕ) (hq : 0 < q)
    (hpoly : ∀ P : Polynomial F, Polynomial.expand F q P = P ^ q)
    (T : PowerSeries F) : T ^ q = dilate q T := by
  ext n
  have ht := congrArg (fun P : Polynomial F => P.coeff n)
    (PowerSeries.trunc_trunc_pow T (n + 1) q)
  simp only [PowerSeries.coeff_trunc, if_pos (Nat.lt_succ_self n)] at ht
  rw [← ht, ← Polynomial.coe_pow, Polynomial.coeff_coe,
    ← hpoly (PowerSeries.trunc (n + 1) T), Polynomial.coeff_expand hq, coeff_dilate]
  split_ifs with hd
  · rw [PowerSeries.coeff_trunc,
      if_pos (lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.lt_succ_self _))]
  · rfl

/-- Full formal-power-series Frobenius over an arbitrary finite field. -/
theorem power_eq_dilate_finiteField
    {E : Type*} [Field E] [Fintype E] (T : PowerSeries E) :
    T ^ Fintype.card E = dilate (Fintype.card E) T := by
  exact power_eq_dilate_of_polynomial (Fintype.card E) Fintype.card_pos
    FiniteField.expand_card T

/-- Algebraic part of the Frobenius bridge. The Frobenius substitution identity
is an explicit hypothesis. The branch equation itself then suffices; uniqueness
of formal roots is not needed. -/
theorem dilation_equation_of_power_identity
    (D T : PowerSeries F) (a b s q : ℕ) (hq : q = b * s + 1)
    (hbranch : D ^ a * T ^ b = 1) (hfrob : T ^ q = dilate q T) :
    T = D ^ (a * s) * dilate q T := by
  rw [← hfrob, hq, pow_succ, pow_mul, pow_mul]
  rw [← mul_assoc, ← mul_pow, hbranch, one_pow, one_mul]

/-- Finite-field branch equation implies the exact dilation equation. Here
`q = b*s+1` expresses the divisibility of `q-1` by the branch denominator. -/
theorem finiteField_dilation_equation
    {E : Type*} [Field E] [Fintype E]
    (D : Polynomial E) (T : PowerSeries E) (a b s : ℕ)
    (hq : Fintype.card E = b * s + 1)
    (hbranch : (D : PowerSeries E) ^ a * T ^ b = 1) :
    T = ((D ^ (a * s) : Polynomial E) : PowerSeries E) *
      dilate (Fintype.card E) T := by
  rw [Polynomial.coe_pow]
  exact dilation_equation_of_power_identity (D : PowerSeries E) T a b s
    (Fintype.card E) hq hbranch (power_eq_dilate_finiteField T)

/-- Polynomial multiplication against a dilated power series has a single
contributing convolution term when the polynomial degree is below the base. -/
theorem coeff_polynomial_mul_dilate
    (q : ℕ) (hq : 0 < q) (K : Polynomial F) (hK : K.natDegree < q)
    (T : PowerSeries F) (m d : ℕ) (hd : d < q) :
    PowerSeries.coeff (q * m + d) ((K : PowerSeries F) * dilate q T) =
      PowerSeries.coeff m T * K.coeff d := by
  rw [PowerSeries.coeff_mul]
  rw [Finset.sum_eq_single (d, q * m)]
  · simp [Nat.mul_div_right, hq, mul_comm]
  · intro ij hij hne
    have hsum : ij.1 + ij.2 = q * m + d := Finset.mem_antidiagonal.mp hij
    by_cases hiq : ij.1 < q
    · by_cases hj : q ∣ ij.2
      · have hi : ij.1 = d := by
          have hm := congrArg (fun n : ℕ => n % q) hsum
          simpa [Nat.add_mod, Nat.mod_eq_of_lt hiq, Nat.mod_eq_zero_of_dvd hj,
            Nat.mod_eq_of_lt hd] using hm
        have hjval : ij.2 = q * m := by omega
        exact False.elim (hne (Prod.ext hi hjval))
      · simp [hj]
    · have hz : K.coeff ij.1 = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_lt_of_le hK (Nat.le_of_not_gt hiq))
      simp [hz]
  · intro hnot
    exact False.elim (hnot (Finset.mem_antidiagonal.mpr (Nat.add_comm _ _)))

/-- The coefficient digit rule before normalizing the constant coefficient. -/
theorem coeff_of_dilation_equation
    (q : ℕ) (hq : 0 < q) (K : Polynomial F) (hK : K.natDegree < q)
    (T : PowerSeries F) (hT : T = (K : PowerSeries F) * dilate q T)
    (m d : ℕ) (hd : d < q) :
    PowerSeries.coeff (q * m + d) T =
      PowerSeries.coeff m T * K.coeff d := by
  calc
    _ = PowerSeries.coeff (q * m + d)
        ((K : PowerSeries F) * dilate q T) := congrArg _ hT
    _ = _ := coeff_polynomial_mul_dilate q hq K hK T m d hd

/-- The low coefficients of the kernel polynomial are exactly those of the
normalized solution. -/
theorem low_coeff_of_dilation_equation
    (q : ℕ) (hq : 0 < q) (K : Polynomial F) (hK : K.natDegree < q)
    (T : PowerSeries F) (hT : T = (K : PowerSeries F) * dilate q T)
    (hT0 : PowerSeries.coeff 0 T = 1) (d : ℕ) (hd : d < q) :
    PowerSeries.coeff d T = K.coeff d := by
  simpa [hT0] using coeff_of_dilation_equation q hq K hK T hT 0 d hd

/-- Exact scalar Lucas identity at every index, obtained from a whole-series
functional equation and a degree bound. -/
theorem lucas_of_dilation_equation
    (q : ℕ) (hq : 0 < q) (K : Polynomial F) (hK : K.natDegree < q)
    (T : PowerSeries F) (hT : T = (K : PowerSeries F) * dilate q T)
    (hT0 : PowerSeries.coeff 0 T = 1) (m d : ℕ) (hd : d < q) :
    PowerSeries.coeff (q * m + d) T =
      PowerSeries.coeff m T * PowerSeries.coeff d T := by
  rw [low_coeff_of_dilation_equation q hq K hK T hT hT0 d hd]
  exact coeff_of_dilation_equation q hq K hK T hT m d hd

/-- The strict degree bound provides a vanishing high digit. -/
theorem high_digit_zero_of_dilation_equation
    (q : ℕ) (hq : 0 < q) (K : Polynomial F) (hK : K.natDegree < q)
    (T : PowerSeries F) (hT : T = (K : PowerSeries F) * dilate q T)
    (hT0 : PowerSeries.coeff 0 T = 1) (d : ℕ) (hd : d < q)
    (hdegree : K.natDegree < d) :
    PowerSeries.coeff d T = 0 := by
  rw [low_coeff_of_dilation_equation q hq K hK T hT hT0 d hd]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt hdegree

/-- From a fractional-power branch over a finite field directly to the scalar
Lucas recurrence. The degree inequality is imposed on its kernel polynomial. -/
theorem finiteField_lucas_of_branch
    {E : Type*} [Field E] [Fintype E]
    (D : Polynomial E) (T : PowerSeries E) (a b s : ℕ)
    (hq : Fintype.card E = b * s + 1)
    (hbranch : (D : PowerSeries E) ^ a * T ^ b = 1)
    (hK : (D ^ (a * s)).natDegree < Fintype.card E)
    (hT0 : PowerSeries.coeff 0 T = 1)
    (m d : ℕ) (hd : d < Fintype.card E) :
    PowerSeries.coeff (Fintype.card E * m + d) T =
      PowerSeries.coeff m T * PowerSeries.coeff d T := by
  exact lucas_of_dilation_equation (Fintype.card E) Fintype.card_pos
    (D ^ (a * s)) hK T (finiteField_dilation_equation D T a b s hq hbranch)
    hT0 m d hd

/-- The manuscript's strict rational-exponent degree condition gives a genuine
high-digit gap for the polynomial kernel. -/
theorem kernel_degree_lt_pred_base
    (D : Polynomial F) (a b s q : ℕ) (hs : 0 < s)
    (hq : q = b * s + 1) (hgap : a * D.natDegree < b) :
    (D ^ (a * s)).natDegree < q - 1 := by
  have hmul := Nat.mul_lt_mul_of_pos_right hgap hs
  calc
    (D ^ (a * s)).natDegree ≤ (a * s) * D.natDegree :=
      Polynomial.natDegree_pow_le
    _ < b * s := by simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul
    _ = q - 1 := by omega

/-- A nonconstant polynomial supported below the radix has a first nonzero
positive digit. This avoids any derivative calculation for choosing the seed. -/
theorem exists_first_nonzero_kernel_digit
    (K : Polynomial F) (q : ℕ) (hpos : 0 < K.natDegree)
    (hdegree : K.natDegree < q) :
    ∃ d, 0 < d ∧ d < q ∧ K.coeff d ≠ 0 ∧
      ∀ j, 0 < j → j < d → K.coeff j = 0 := by
  classical
  have hK : K ≠ 0 := by
    intro hz
    simp [hz] at hpos
  have hlead : K.coeff K.natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hK
  have hex : ∃ d, 0 < d ∧ K.coeff d ≠ 0 := ⟨K.natDegree, hpos, hlead⟩
  have hd := Nat.find_spec hex
  refine ⟨Nat.find hex, hd.1,
    lt_of_le_of_lt (Nat.find_min' hex ⟨hpos, hlead⟩) hdegree, hd.2, ?_⟩
  intro j hjpos hjlt
  by_contra hj
  exact Nat.find_min hex hjlt ⟨hjpos, hj⟩

end SierpinskiFormal
