import SierpinskiFormal.DigitRelativeHoles
import SierpinskiFormal.RationalSupportGrowth

set_option autoImplicit false

namespace IndependentZeroBlocks
open SierpinskiFormal

/-- Polynomial multiplication and positive dilation preserve uniform relative
holes in coefficient support. Cancellation can only remove support. -/
theorem HasUniformRelativeHoles.polynomial_mul_dilate
    {K : Type*} [Field K] {F : PowerSeries K}
    (hF : HasUniformRelativeHoles (fun n => PowerSeries.coeff n F ≠ 0))
    (H : Polynomial K) (q : ℕ) (hq : 0 < q) :
    HasUniformRelativeHoles
      (fun n => PowerSeries.coeff n ((H : PowerSeries K) * SierpinskiFormal.dilate q F) ≠ 0) := by
  classical
  let bad : ℕ → ℕ → Prop := fun h n =>
    ∃ k, PowerSeries.coeff k F ≠ 0 ∧ n = h + q * k
  have hbad : HasUniformRelativeHoles (fun n => ∃ h ∈ H.support, bad h n) :=
    HasUniformRelativeHoles.finset_union bad H.support
      (fun h _ => hF.affineImage h q hq)
  apply hbad.mono
  intro n hn
  by_contra hnone
  apply hn
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  have heq : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
  by_cases hH : H.coeff ij.1 = 0
  · simp [hH]
  by_cases hdiv : q ∣ ij.2
  · by_cases htail : PowerSeries.coeff (ij.2 / q) F = 0
    · simp [coeff_dilate, hdiv, htail]
    · exfalso
      apply hnone
      refine ⟨ij.1, Polynomial.mem_support_iff.mpr hH, ij.2 / q, htail, ?_⟩
      rw [Nat.mul_div_cancel_left' hdiv]
      exact heq.symm
  · simp [coeff_dilate, hdiv]

/-- An absorbed filter has uniform relative holes whenever the actual digit
support omits a digit. This sufficient result needs only degree below the
radix, allowing missing digits away from the highest position. -/
theorem digitProduct_rational_hasUniformRelativeHoles_of_absorbed
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b)
    (hsmall : radixDigitSupportCount b A < b)
    (P D : Polynomial K) (hD0 : D.coeff 0 ≠ 0)
    (habs : ∃ e, D ∣ P * kernelPrefix b A e) :
    HasUniformRelativeHoles (fun n => PowerSeries.coeff n
      (rationalMultiple P D (canonicalSeries b A)) ≠ 0) := by
  obtain ⟨e, he⟩ := habs
  obtain ⟨H, hform⟩ := rationalMultiple_eq_polynomial_mul_dilate_of_dvd
    b hb A hA0 hdegree e P D hD0 he
  rw [hform]
  exact (canonicalSeries_support_hasUniformRelativeHoles_of_digitSupport_lt
    b hb A hA0 hsmall).polynomial_mul_dilate H (b ^ e) (pow_pos (by omega) e)

/-- Combined algebraic and geometric classification under the strict degree
gap. Zero, digit-exponent growth with uniform relative holes, and linear
growth exhaust all rational filters. -/
theorem digitProduct_rational_growth_and_holes_classification
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b - 1) (P D : Polynomial K)
    (hD0 : D.coeff 0 ≠ 0) :
    (P = 0 ∧ rationalMultiple P D (canonicalSeries b A) = 0) ∨
    (P ≠ 0 ∧ (∃ e, D ∣ P * kernelPrefix b A e) ∧
      HasPowerSupportGrowth (rationalMultiple P D (canonicalSeries b A))
        (digitSupportExponent b A) ∧
      HasUniformRelativeHoles (fun n => PowerSeries.coeff n
        (rationalMultiple P D (canonicalSeries b A)) ≠ 0)) ∨
    ((∀ e, ¬D ∣ P * kernelPrefix b A e) ∧
      HasPowerSupportGrowth (rationalMultiple P D (canonicalSeries b A)) 1) := by
  rcases digitProduct_rational_supportGrowth_classification
    b hb A hA0 hdegree P D hD0 with hzero | ⟨hP, habs, hgrowth⟩ | hdense
  · exact Or.inl hzero
  · exact Or.inr (Or.inl ⟨hP, habs, hgrowth,
      digitProduct_rational_hasUniformRelativeHoles_of_absorbed b hb A hA0
        (by omega) (radixDigitSupportCount_lt_of_degree b A hdegree) P D hD0 habs⟩)
  · exact Or.inr (Or.inr hdense)

end IndependentZeroBlocks
