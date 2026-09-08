import SierpinskiFormal.ExactDigitSupport
import SierpinskiFormal.AbsorbedBlockForm

set_option autoImplicit false

namespace IndependentZeroBlocks
open SierpinskiFormal

/-- A single residue is isolated as soon as the polynomial ends before its
second occurrence. Other residues may carry between blocks. -/
theorem coeff_polynomial_mul_dilate_isolated_residue
    {K : Type*} [Field K] (q : ℕ) (hq : 0 < q)
    (G : Polynomial K) (T : PowerSeries K) (r : ℕ) (hr : r < q)
    (hG : G.natDegree < q + r) (n : ℕ) :
    PowerSeries.coeff (q * n + r) ((G : PowerSeries K) * dilate q T) =
      G.coeff r * PowerSeries.coeff n T := by
  rw [PowerSeries.coeff_mul, Finset.sum_eq_single (r, q * n)]
  · simp [Nat.mul_div_right, hq]
  · intro ij hij hne
    have hsum := Finset.mem_antidiagonal.mp hij
    by_cases hj : q ∣ ij.2
    · by_cases hi : ij.1 < q + r
      · have hmod : ij.1 % q = r := by
          have hm := congrArg (fun z : ℕ => z % q) hsum
          simpa [Nat.add_mod, Nat.mod_eq_zero_of_dvd hj,
            Nat.mod_eq_of_lt hr] using hm
        have hdiv := Nat.div_add_mod ij.1 q
        have hid : ij.1 / q = 0 := by
          by_contra hz
          have hp : 1 ≤ ij.1 / q := Nat.one_le_iff_ne_zero.mpr hz
          have hm := Nat.mul_le_mul_left q hp
          rw [hmod] at hdiv
          nlinarith
        have hir : ij.1 = r := by simpa [hid, hmod] using hdiv.symm
        have hjn : ij.2 = q * n := by omega
        exact False.elim (hne (Prod.ext hir hjn))
      · have hz : G.coeff ij.1 = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (hG.trans_le (by omega))
        simp [hz]
    · simp [hj]
  · intro hnot
    exact False.elim (hnot (Finset.mem_antidiagonal.mpr (Nat.add_comm _ _)))

/-- The degree of a no-carry prefix is below its radix block, including the
boundary case `deg A = b - 1`. -/
theorem fiber_kernelPrefix_natDegree_lt_pow
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hdegree : A.natDegree < b) (e : ℕ) :
    (kernelPrefix b A e).natDegree < b ^ e := by
  have hd := kernelPrefix_natDegree_bound b hb A e
  have hle : A.natDegree ≤ b - 1 := by omega
  have hmul := Nat.mul_le_mul_right (b ^ e - 1) hle
  have hp : 0 < b ^ e := pow_pos (by omega) e
  have hsub : b ^ e - 1 + 1 = b ^ e := by omega
  have hb1 : 0 < b - 1 := by omega
  nlinarith

theorem fiber_coeff_kernelPrefix_eq_canonical
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b) (e n : ℕ) (hn : n < b ^ e) :
    (kernelPrefix b A e).coeff n = PowerSeries.coeff n (canonicalSeries b A) := by
  rw [canonicalSeries_eq_kernelPrefix_mul_dilate b hb A hA0 hdegree e]
  symm
  simpa using coeff_mul_dilate_of_lt (b ^ e)
    (kernelPrefix b A e : PowerSeries K) (canonicalSeries b A) (by simp) n hn

theorem fiber_kernelPrefix_missing_interval
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b) (m : ℕ) (hm : m < b)
    (hAm : A.coeff m = 0) (e n : ℕ)
    (hlo : m * b ^ e ≤ n) (hhi : n < (m + 1) * b ^ e) :
    (kernelPrefix b A (e + 1)).coeff n = 0 := by
  have hn : n < b ^ (e + 1) := by
    have hmul := Nat.mul_le_mul_right (b ^ e) (show m + 1 ≤ b by omega)
    rw [pow_succ]
    nlinarith
  rw [fiber_coeff_kernelPrefix_eq_canonical b hb A hA0 hdegree (e + 1) n hn]
  have hr : n - m * b ^ e < b ^ e := by
    have hs := Nat.sub_add_cancel hlo
    nlinarith
  have hz := coeff_canonicalSeries_eq_zero_on_missingDigit_cylinder
    b hb A hA0 m hm hAm e 0 (n - m * b ^ e) hr
  simpa [Nat.add_sub_of_le hlo] using hz

/-- A finite prefix before a zero interval has a last nonzero coefficient. -/
theorem polynomial_exists_last_before_zero_interval
    {K : Type*} [Field K] (C : Polynomial K) (hC0 : C.coeff 0 ≠ 0)
    (g L : ℕ) (hg : 0 < g)
    (hgap : ∀ n, g ≤ n → n < g + L → C.coeff n = 0) :
    ∃ t, t < g ∧ C.coeff t ≠ 0 ∧
      ∀ n, t < n → n < g + L → C.coeff n = 0 := by
  classical
  let S := (Finset.range g).filter fun n => C.coeff n ≠ 0
  have hS : S.Nonempty := ⟨0, by simp [S, hg, hC0]⟩
  let t := S.max' hS
  have htS : t ∈ S := Finset.max'_mem S hS
  have ht : t < g ∧ C.coeff t ≠ 0 := by simpa [S] using htS
  refine ⟨t, ht.1, ht.2, ?_⟩
  intro n htn hn
  by_cases hgn : g ≤ n
  · exact hgap n hgn hn
  · by_contra hz
    have hnS : n ∈ S := by simp [S, show n < g by omega, hz]
    have hnt : n ≤ t := Finset.le_max' S n hnS
    omega

/-- A zero interval after the last prefix coefficient isolates the leading
term of an arbitrary polynomial multiplier. -/
theorem coeff_polynomial_mul_at_last_before_gap
    {K : Type*} [Field K] (H C : Polynomial K) (t : ℕ)
    (hgap : ∀ n, t < n → n ≤ t + H.natDegree → C.coeff n = 0) :
    (H * C).coeff (H.natDegree + t) = H.leadingCoeff * C.coeff t := by
  rw [Polynomial.coeff_mul, Finset.sum_eq_single (H.natDegree, t)]
  · rfl
  · intro ij hij hne
    have hsum := Finset.mem_antidiagonal.mp hij
    by_cases hi : H.natDegree < ij.1
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi, zero_mul]
    · have ht : t < ij.2 := by
        by_contra hz
        have hi' : ij.1 = H.natDegree := by omega
        have hj' : ij.2 = t := by omega
        exact hne (Prod.ext hi' hj')
      rw [hgap ij.2 ht (by omega), mul_zero]
  · intro hnot
    exact False.elim (hnot (Finset.mem_antidiagonal.mpr rfl))

/-- Every nonzero polynomial filter of a dilated missing-digit product has
an exact copy of the canonical coefficient sequence on one affine fiber. -/
theorem polynomial_dilate_canonical_exists_exact_fiber
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b) (hmissing : ∃ m < b, A.coeff m = 0)
    (H : Polynomial K) (hH : H ≠ 0) (q : ℕ) (hq : 0 < q) :
    ∃ e r : ℕ, ∃ c : K, r < q * b ^ e ∧ c ≠ 0 ∧
      ∀ n : ℕ,
        PowerSeries.coeff ((q * b ^ e) * n + r)
          ((H : PowerSeries K) * dilate q (canonicalSeries b A)) =
        c * PowerSeries.coeff n (canonicalSeries b A) := by
  classical
  obtain ⟨m, hm, hAm⟩ := hmissing
  have hmpos : 0 < m := by
    by_contra hz
    have hm0 : m = 0 := by omega
    rw [hm0, hA0] at hAm
    exact one_ne_zero hAm
  obtain ⟨e, he⟩ := pow_unbounded_of_one_lt H.natDegree (by omega : 1 < b)
  let Q := q * b ^ (e + 1)
  let C := Polynomial.expand K q (kernelPrefix b A (e + 1))
  let g := q * (m * b ^ e)
  let L := q * b ^ e
  have hQ : 0 < Q := Nat.mul_pos hq (pow_pos (by omega) _)
  have hg : 0 < g := Nat.mul_pos hq (Nat.mul_pos hmpos (pow_pos (by omega) _))
  have hL : H.natDegree < L := by
    have hmul := Nat.mul_le_mul_right (b ^ e) (show 1 ≤ q by omega)
    dsimp [L]
    nlinarith
  have hgL : g + L ≤ Q := by
    have hmb := Nat.mul_le_mul_right (b ^ e) (show m + 1 ≤ b by omega)
    have hqmb := Nat.mul_le_mul_left q hmb
    dsimp [g, L, Q]
    rw [pow_succ]
    nlinarith
  have hC0 : C.coeff 0 ≠ 0 := by
    have hp := fiber_coeff_kernelPrefix_eq_canonical b hb A hA0 hdegree
      (e + 1) 0 (pow_pos (by omega) _)
    have hc : C.coeff 0 = 1 := by simpa [C, Polynomial.coeff_expand hq] using hp
    rw [hc]
    exact one_ne_zero
  have hgap : ∀ n, g ≤ n → n < g + L → C.coeff n = 0 := by
    intro n hnlo hnhi
    dsimp [C]
    by_cases hqn : q ∣ n
    · obtain ⟨k, rfl⟩ := hqn
      rw [Polynomial.coeff_expand_mul' hq]
      apply fiber_kernelPrefix_missing_interval b hb A hA0 hdegree m hm hAm e k
      · dsimp [g] at hnlo
        exact Nat.le_of_mul_le_mul_left hnlo hq
      · dsimp [g, L] at hnhi
        have heq : q * (m * b ^ e) + q * b ^ e = q * ((m + 1) * b ^ e) := by ring
        rw [heq] at hnhi
        exact Nat.lt_of_mul_lt_mul_left hnhi
    · simp [Polynomial.coeff_expand hq, hqn]
  obtain ⟨t, htg, htC, htail⟩ :=
    polynomial_exists_last_before_zero_interval C hC0 g L hg hgap
  let r := H.natDegree + t
  let G := H * C
  have hr : r < Q := by dsimp [r]; omega
  have hGcoeff : G.coeff r = H.leadingCoeff * C.coeff t := by
    apply coeff_polynomial_mul_at_last_before_gap H C t
    intro n htn hn
    exact htail n htn (by omega)
  have hc : G.coeff r ≠ 0 := by
    rw [hGcoeff]
    exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hH) htC
  have hCdeg : C.natDegree < Q := by
    have hpre := fiber_kernelPrefix_natDegree_lt_pow b hb A hdegree (e + 1)
    have hmul := Nat.mul_lt_mul_of_pos_left hpre hq
    simpa [C, Q, Polynomial.natDegree_expand, Nat.mul_comm] using hmul
  have hGdeg : G.natDegree < Q + r := by
    have hd : (H * C).natDegree ≤ H.natDegree + C.natDegree :=
      Polynomial.natDegree_mul_le
    dsimp [G, r]
    omega
  have hfactor :
      (H : PowerSeries K) * dilate q (canonicalSeries b A) =
        (G : PowerSeries K) * dilate Q (canonicalSeries b A) := by
    have hd := congrArg (dilate q)
      (canonicalSeries_eq_kernelPrefix_mul_dilate b hb A hA0 hdegree (e + 1))
    rw [dilate_polynomial_mul q hq, dilate_dilate] at hd
    rw [hd]
    simp only [G, C, Q, Polynomial.coe_mul, mul_assoc]
  refine ⟨e + 1, r, G.coeff r, hr, hc, ?_⟩
  intro n
  rw [hfactor]
  exact coeff_polynomial_mul_dilate_isolated_residue Q hQ G
    (canonicalSeries b A) r hr hGdeg n

/-- For radix-power dilations, the exact fiber again has a radix-power step. -/
theorem polynomial_radix_dilate_canonical_exists_exact_fiber
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b) (hmissing : ∃ m < b, A.coeff m = 0)
    (H : Polynomial K) (hH : H ≠ 0) (a : ℕ) :
    ∃ E R : ℕ, ∃ c : K, R < b ^ E ∧ c ≠ 0 ∧
      ∀ n : ℕ,
        PowerSeries.coeff (b ^ E * n + R)
          ((H : PowerSeries K) * dilate (b ^ a) (canonicalSeries b A)) =
        c * PowerSeries.coeff n (canonicalSeries b A) := by
  obtain ⟨e, r, c, hr, hc, hf⟩ := polynomial_dilate_canonical_exists_exact_fiber
    b hb A hA0 hdegree hmissing H hH (b ^ a) (pow_pos (by omega) a)
  exact ⟨a + e, r, c, by simpa [pow_add] using hr, hc, by simpa [pow_add] using hf⟩

/-- Absorption supplies a polynomial-dilation representation; a missing digit
then supplies an exact nonzero copy of the original coefficient sequence. -/
theorem absorbed_rational_canonical_exists_exact_fiber
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b) (hmissing : ∃ m < b, A.coeff m = 0)
    (P D : Polynomial K) (hP : P ≠ 0) (hD0 : D.coeff 0 ≠ 0)
    (habs : ∃ e, D ∣ P * kernelPrefix b A e) :
    ∃ E R : ℕ, ∃ c : K, R < b ^ E ∧ c ≠ 0 ∧
      ∀ n : ℕ,
        PowerSeries.coeff (b ^ E * n + R)
          (rationalMultiple P D (canonicalSeries b A)) =
        c * PowerSeries.coeff n (canonicalSeries b A) := by
  obtain ⟨e, he⟩ := habs
  obtain ⟨H, hrep⟩ := rationalMultiple_eq_polynomial_mul_dilate_of_dvd
    b hb A hA0 hdegree e P D hD0 he
  have hH : H ≠ 0 := by
    intro hz
    have hden := rationalMultiple_denominator P D (canonicalSeries b A) hD0
    rw [hrep, hz, Polynomial.coe_zero, zero_mul, mul_zero] at hden
    have hPne : (P : PowerSeries K) ≠ 0 := by
      intro hpz
      apply hP
      ext n
      have hc := congrArg (PowerSeries.coeff n) hpz
      simpa using hc
    have hFne : canonicalSeries b A ≠ 0 := by
      intro hf
      have hc := congrArg (PowerSeries.coeff 0) hf
      simp at hc
    exact mul_ne_zero hPne hFne hden.symm
  rw [hrep]
  exact polynomial_radix_dilate_canonical_exists_exact_fiber
    b hb A hA0 hdegree hmissing H hH e

end IndependentZeroBlocks
