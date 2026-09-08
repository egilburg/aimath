import SierpinskiFormal.RationalDensityCriterion

set_option autoImplicit false

namespace IndependentZeroBlocks
open SierpinskiFormal

/-- Prefix absorption persists when additional digit factors are included. -/
theorem kernelPrefix_dvd_of_le
    {K : Type*} [CommRing K] (b : ℕ) (A : Polynomial K)
    {e E : ℕ} (h : e ≤ E) : kernelPrefix b A e ∣ kernelPrefix b A E := by
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.range_mono h)

/-- Normalized digit prefixes are nonzero over any field. -/
theorem kernelPrefix_ne_zero
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b) (e : ℕ) : kernelPrefix b A e ≠ 0 := by
  intro hz
  have h := canonicalSeries_eq_kernelPrefix_mul_dilate b hb A hA0 hdegree e
  rw [hz, Polynomial.coe_zero, zero_mul] at h
  have h0 := congrArg (PowerSeries.coeff 0) h
  simp at h0

/-- Every absorbed nonzero rational filter admits a block form in which the
polynomial degree is strictly below the dilation factor. The polynomial and
depth are constructed from absorption, not supplied as extra hypotheses. -/
theorem rationalMultiple_exists_disjoint_block_form
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b - 1) (P D : Polynomial K)
    (hP : P ≠ 0) (hD0 : D.coeff 0 ≠ 0)
    (habs : ∃ e, D ∣ P * kernelPrefix b A e) :
    ∃ E : ℕ, ∃ H : Polynomial K, H ≠ 0 ∧ H.natDegree < b ^ E ∧
      P * kernelPrefix b A E = D * H ∧
      rationalMultiple P D (canonicalSeries b A) =
        (H : PowerSeries K) * dilate (b ^ E) (canonicalSeries b A) := by
  obtain ⟨e, he⟩ := habs
  obtain ⟨r, hr⟩ := pow_unbounded_of_one_lt ((b - 1) * P.natDegree)
    (by omega : 1 < b)
  let E := max e r
  have heE : e ≤ E := le_max_left _ _
  have hlarge : (b - 1) * P.natDegree < b ^ E :=
    hr.trans_le (Nat.pow_le_pow_right (by omega) (le_max_right e r))
  have hdiv : D ∣ P * kernelPrefix b A E :=
    he.trans (mul_dvd_mul_left P (kernelPrefix_dvd_of_le b A heE))
  obtain ⟨H, hH⟩ := hdiv
  have hC : kernelPrefix b A E ≠ 0 := kernelPrefix_ne_zero b hb A hA0 (by omega) E
  have hHne : H ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hH
    exact mul_ne_zero hP hC hH
  have hD : D ≠ 0 := by
    intro hz
    exact hD0 (by simp [hz])
  have hHdeg : H.natDegree ≤ P.natDegree + (kernelPrefix b A E).natDegree := by
    have hd := congrArg Polynomial.natDegree hH
    rw [Polynomial.natDegree_mul hP hC, Polynomial.natDegree_mul hD hHne] at hd
    omega
  have hCdeg := kernelPrefix_natDegree_le_mul_pow b hb A E
  have hshort : H.natDegree < b ^ E := by
    have hscaled := Nat.mul_le_mul_left (b - 1) hHdeg
    have ha : A.natDegree + 1 ≤ b - 1 := by omega
    have hbound := Nat.mul_le_mul_right (b ^ E) ha
    have hstrict : (b - 1) * H.natDegree < (b - 1) * b ^ E := by nlinarith
    exact Nat.lt_of_mul_lt_mul_left hstrict
  refine ⟨E, H, hHne, hshort, hH, ?_⟩
  apply Eq.symm
  apply eq_rationalMultiple_of_denominator P D (canonicalSeries b A) _ hD0
  nth_rw 2 [canonicalSeries_eq_kernelPrefix_mul_dilate b hb A hA0 (by omega) E]
  have hHps := congrArg (fun Q : Polynomial K => (Q : PowerSeries K)) hH
  simp only [Polynomial.coe_mul] at hHps ⊢
  calc
    (D : PowerSeries K) * ((H : PowerSeries K) * dilate (b ^ E) (canonicalSeries b A)) =
      ((D : PowerSeries K) * (H : PowerSeries K)) * dilate (b ^ E) (canonicalSeries b A) := by ring
    _ = ((P : PowerSeries K) * (kernelPrefix b A E : PowerSeries K)) *
        dilate (b ^ E) (canonicalSeries b A) := by rw [← hHps]
    _ = _ := by ring

end IndependentZeroBlocks
