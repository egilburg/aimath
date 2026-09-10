import SierpinskiFormal.UniformDigitGrowth

set_option autoImplicit false

namespace IndependentZeroBlocks

open SierpinskiFormal
open scoped BigOperators

/-- A power counting bound which is uniform over all translated intervals. -/
def HasUniformPowerIntervalBound
    (α : ℝ) (bad : ℕ → Prop) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ a L : ℕ, 1 ≤ L →
    (intervalPredicateCount bad a L : ℝ) ≤ C * (L : ℝ) ^ α

/-- Passing to a smaller predicate preserves a uniform interval bound. -/
theorem HasUniformPowerIntervalBound.mono
    {α : ℝ} {bad₁ bad₂ : ℕ → Prop}
    (hbad₂ : HasUniformPowerIntervalBound α bad₂)
    (hsub : ∀ n : ℕ, bad₁ n → bad₂ n) :
    HasUniformPowerIntervalBound α bad₁ := by
  obtain ⟨C, hC, hbound⟩ := hbad₂
  refine ⟨C, hC, ?_⟩
  intro a L hL
  have hcount : intervalPredicateCount bad₁ a L ≤
      intervalPredicateCount bad₂ a L := by
    classical
    unfold intervalPredicateCount
    apply Finset.card_le_card
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    exact ⟨hj.1, hsub _ hj.2⟩
  have hcountR : (intervalPredicateCount bad₁ a L : ℝ) ≤
      (intervalPredicateCount bad₂ a L : ℝ) := by exact_mod_cast hcount
  exact hcountR.trans (hbound a L hL)

/-- A local count of a finite union is at most the sum of the local counts. -/
private theorem intervalPredicateCount_exists_le
    {ι : Type*} [Fintype ι] (bad : ι → ℕ → Prop) (a L : ℕ) :
    intervalPredicateCount (fun n => ∃ i, bad i n) a L ≤
      ∑ i, intervalPredicateCount (bad i) a L := by
  classical
  have hsubset :
      (Finset.range L).filter (fun j => ∃ i, bad i (a + j)) ⊆
        Finset.univ.biUnion (fun i : ι =>
          (Finset.range L).filter (fun j => bad i (a + j))) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨hjL, i, hi⟩ := hj
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_filter, Finset.mem_range]
    exact ⟨i, hjL, hi⟩
  have hc := (Finset.card_le_card hsubset).trans Finset.card_biUnion_le
  unfold intervalPredicateCount
  convert! hc using 1
  apply congrArg Finset.card
  ext j
  simp

/-- A finite union preserves a common uniform interval exponent. -/
theorem HasUniformPowerIntervalBound.finite_union
    {ι : Type*} [Fintype ι] {α : ℝ} (bad : ι → ℕ → Prop)
    (hbad : ∀ i, HasUniformPowerIntervalBound α (bad i)) :
    HasUniformPowerIntervalBound α (fun n => ∃ i, bad i n) := by
  classical
  choose C hC hbound using hbad
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC i), ?_⟩
  intro a L hL
  calc
    (intervalPredicateCount (fun n => ∃ i, bad i n) a L : ℝ) ≤
        ((∑ i, intervalPredicateCount (bad i) a L : ℕ) : ℝ) :=
      Nat.cast_le.mpr (intervalPredicateCount_exists_le bad a L)
    _ = ∑ i, (intervalPredicateCount (bad i) a L : ℝ) := by simp
    _ ≤ ∑ i, C i * (L : ℝ) ^ α := by
      apply Finset.sum_le_sum
      intro i _
      exact hbound i a L hL
    _ = (∑ i, C i) * (L : ℝ) ^ α := (Finset.sum_mul _ _ _).symm

/-- The local count of a positive affine image is controlled by a source
interval of length `L+1`. -/
private theorem intervalPredicateCount_affineImage_le
    (bad : ℕ → Prop) (h q : ℕ) (hq : 0 < q) (a L : ℕ) :
    intervalPredicateCount
        (fun n => ∃ k : ℕ, bad k ∧ n = h + q * k) a L ≤
      intervalPredicateCount bad ((a - h) / q) (L + 1) := by
  classical
  let t := (a - h) / q
  let S := (Finset.range L).filter
    (fun j => ∃ k : ℕ, bad k ∧ a + j = h + q * k)
  have hex (j : ℕ) (hj : j ∈ S) :
      ∃ k : ℕ, bad k ∧ a + j = h + q * k := by
    simpa [S] using (Finset.mem_filter.mp hj).2
  let kOf : ℕ → ℕ := fun j =>
    if hj : j ∈ S then Classical.choose (hex j hj) else 0
  have hkbad (j : ℕ) (hj : j ∈ S) : bad (kOf j) := by
    simp only [kOf, dif_pos hj]
    exact (Classical.choose_spec (hex j hj)).1
  have hkeq (j : ℕ) (hj : j ∈ S) :
      a + j = h + q * kOf j := by
    simp only [kOf, dif_pos hj]
    exact (Classical.choose_spec (hex j hj)).2
  have ht_le (j : ℕ) (hj : j ∈ S) : t ≤ kOf j := by
    by_cases hha : h ≤ a
    · have hdiff : a - h ≤ q * kOf j := by
        have := hkeq j hj
        omega
      exact Nat.div_le_of_le_mul (by simpa [Nat.mul_comm] using hdiff)
    · have ht0 : t = 0 := by simp [t, Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hha)]
      simp [ht0]
  have hk_lt (j : ℕ) (hj : j ∈ S) : kOf j < t + (L + 1) := by
    have hjL : j < L := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    by_cases hha : h ≤ a
    · let d := a - h
      have had : h + d = a := Nat.add_sub_of_le hha
      have hkformula : q * kOf j = d + j := by
        have := hkeq j hj
        dsimp [d]
        omega
      have hdlt : d < q * (d / q + 1) := by
        simpa [Nat.mul_comm] using Nat.lt_mul_div_succ d hq
      have hLq : L ≤ q * L := Nat.le_mul_of_pos_left L hq
      have hnum : d + j < q * (d / q + (L + 1)) := by
        calc
          d + j < q * (d / q + 1) + L := Nat.add_lt_add hdlt hjL
          _ ≤ q * (d / q + 1) + q * L := Nat.add_le_add_left hLq _
          _ = q * (d / q + (L + 1)) := by ring
      have : kOf j < d / q + (L + 1) := by
        apply (Nat.mul_lt_mul_left hq).mp
        rw [hkformula]
        exact hnum
      simpa [t, d] using this
    · have hah : a < h := Nat.lt_of_not_ge hha
      have ht0 : t = 0 := by simp [t, Nat.sub_eq_zero_of_le hah.le]
      have hkq : q * kOf j < L := by
        have := hkeq j hj
        omega
      have hkle : kOf j ≤ q * kOf j := Nat.le_mul_of_pos_left _ hq
      rw [ht0]
      omega
  let f : ℕ → ℕ := fun j => kOf j - t
  have hfmem : ∀ j ∈ S,
      f j ∈ (Finset.range (L + 1)).filter (fun r => bad (t + r)) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range]
    have htle := ht_le j hj
    have hklt := hk_lt j hj
    exact ⟨by dsimp [f]; omega, by
      rw [show t + f j = kOf j by dsimp [f]; omega]
      exact hkbad j hj⟩
  have hfinj : (S : Set ℕ).InjOn f := by
    intro i hi j hj hij
    have hki : t ≤ kOf i := ht_le i hi
    have hkj : t ≤ kOf j := ht_le j hj
    have hk : kOf i = kOf j := by dsimp [f] at hij; omega
    have hei := hkeq i hi
    have hej := hkeq j hj
    rw [hk] at hei
    omega
  have hcard := Finset.card_le_card_of_injOn f hfmem hfinj
  simpa [S, t, intervalPredicateCount] using hcard

/-- Positive affine images preserve every nonnegative uniform power
exponent. -/
theorem HasUniformPowerIntervalBound.affineImage
    {α : ℝ} {bad : ℕ → Prop} (hbad : HasUniformPowerIntervalBound α bad)
    (hα : 0 ≤ α) (h q : ℕ) (hq : 0 < q) :
    HasUniformPowerIntervalBound α
      (fun n => ∃ k : ℕ, bad k ∧ n = h + q * k) := by
  obtain ⟨C, hC, hbound⟩ := hbad
  refine ⟨C * (2 : ℝ) ^ α, mul_nonneg hC (by positivity), ?_⟩
  intro a L hL
  have hcount := intervalPredicateCount_affineImage_le bad h q hq a L
  have hsource := hbound ((a - h) / q) (L + 1) (by omega)
  have hLtwo : (L + 1 : ℕ) ≤ 2 * L := by omega
  have hrpow : ((L + 1 : ℕ) : ℝ) ^ α ≤ ((2 * L : ℕ) : ℝ) ^ α :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hLtwo) hα
  calc
    (intervalPredicateCount
        (fun n => ∃ k : ℕ, bad k ∧ n = h + q * k) a L : ℝ) ≤
        (intervalPredicateCount bad ((a - h) / q) (L + 1) : ℝ) := by
      exact_mod_cast hcount
    _ ≤ C * (((L + 1 : ℕ) : ℝ) ^ α) := hsource
    _ ≤ C * (((2 * L : ℕ) : ℝ) ^ α) :=
      mul_le_mul_of_nonneg_left hrpow hC
    _ = (C * (2 : ℝ) ^ α) * (L : ℝ) ^ α := by
      push_cast
      rw [Real.mul_rpow (by positivity) (by positivity)]
      ring

/-- Snake-case alias for affine-image closure. -/
theorem HasUniformPowerIntervalBound.affine_image
    {α : ℝ} {bad : ℕ → Prop} (hbad : HasUniformPowerIntervalBound α bad)
    (hα : 0 ≤ α) (h q : ℕ) (hq : 0 < q) :
    HasUniformPowerIntervalBound α
      (fun n => ∃ k : ℕ, bad k ∧ n = h + q * k) :=
  hbad.affineImage hα h q hq

/-- Every supported coefficient of a polynomial times a dilation lies in one
of finitely many positive affine images of the original support. -/
private theorem polynomial_mul_dilate_support_subset
    {K : Type*} [Field K] (H : Polynomial K) (F : PowerSeries K)
    (q : ℕ) (n : ℕ)
    (hn : PowerSeries.coeff n
      ((H : PowerSeries K) * dilate q F) ≠ 0) :
    ∃ i : Fin (H.natDegree + 1), ∃ k : ℕ,
      PowerSeries.coeff k F ≠ 0 ∧ n = i.1 + q * k := by
  rw [PowerSeries.coeff_mul] at hn
  obtain ⟨ij, hij, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  have hHi : H.coeff ij.1 ≠ 0 := by
    simpa only [Polynomial.coeff_coe] using left_ne_zero_of_mul hterm
  have hdil : PowerSeries.coeff ij.2 (dilate q F) ≠ 0 :=
    right_ne_zero_of_mul hterm
  have hiDegree : ij.1 ≤ H.natDegree :=
    Polynomial.le_natDegree_of_ne_zero hHi
  have hqdiv : q ∣ ij.2 := by
    by_contra hnot
    rw [coeff_dilate, if_neg hnot] at hdil
    exact hdil rfl
  let k := ij.2 / q
  have hk : PowerSeries.coeff k F ≠ 0 := by
    simpa [k, coeff_dilate, hqdiv] using hdil
  have hj : q * k = ij.2 := by
    dsimp [k]
    exact Nat.mul_div_cancel_left' hqdiv
  have hsum : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
  refine ⟨⟨ij.1, Nat.lt_succ_of_le hiDegree⟩, k, hk, ?_⟩
  calc
    n = ij.1 + ij.2 := hsum.symm
    _ = ij.1 + q * k := by rw [hj]

/-- Multiplication by a polynomial after a positive dilation preserves every
nonnegative uniform interval exponent. -/
theorem HasUniformPowerIntervalBound.polynomial_mul_dilate
    {K : Type*} [Field K] {F : PowerSeries K} {α : ℝ}
    (hF : HasUniformPowerIntervalBound α
      (fun n => PowerSeries.coeff n F ≠ 0))
    (hα : 0 ≤ α) (H : Polynomial K) (q : ℕ) (hq : 0 < q) :
    HasUniformPowerIntervalBound α
      (fun n => PowerSeries.coeff n
        ((H : PowerSeries K) * dilate q F) ≠ 0) := by
  let bad : Fin (H.natDegree + 1) → ℕ → Prop := fun i n =>
    ∃ k : ℕ, PowerSeries.coeff k F ≠ 0 ∧ n = i.1 + q * k
  have hi (i : Fin (H.natDegree + 1)) :
      HasUniformPowerIntervalBound α (bad i) := by
    dsimp [bad]
    exact hF.affineImage hα i.1 q hq
  have hunion := HasUniformPowerIntervalBound.finite_union bad hi
  apply hunion.mono
  intro n hn
  obtain ⟨i, k, hk, heq⟩ :=
    polynomial_mul_dilate_support_subset H F q n hn
  exact ⟨i, k, hk, heq⟩

/-- The canonical digit support satisfies the reusable uniform-bound
predicate at its actual digit exponent. -/
theorem canonicalSeries_hasUniformDigitLogIntervalBound
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hsmall : radixDigitSupportCount b A < b) :
    HasUniformPowerIntervalBound (digitSupportExponent b A)
      (fun n => PowerSeries.coeff n (canonicalSeries b A) ≠ 0) := by
  exact canonicalSeries_uniformDigitLog_intervalBound b hb A hA0 hsmall

/-- Every absorbed rational filter with a missing digit inherits the optimal
uniform translated-interval upper exponent of its canonical digit support. -/
theorem missingDigit_rational_uniformDigitLogIntervalBound_of_absorbed
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b) (hmissing : ∃ m < b, A.coeff m = 0)
    (P D : Polynomial K) (hD0 : D.coeff 0 ≠ 0)
    (habs : ∃ e, D ∣ P * kernelPrefix b A e) :
    HasUniformPowerIntervalBound (digitSupportExponent b A)
      (fun n => PowerSeries.coeff n
        (rationalMultiple P D (canonicalSeries b A)) ≠ 0) := by
  obtain ⟨m, hm, hAm⟩ := hmissing
  have hsmall := radixDigitSupportCount_lt_of_missingDigit b A m hm hAm
  have hcanonical := canonicalSeries_hasUniformDigitLogIntervalBound
    b hb A hA0 hsmall
  have hα : 0 ≤ digitSupportExponent b A := by
    exact (radixDigitLogExponent_mem_Ico b hb A hA0 hsmall).1
  obtain ⟨e, he⟩ := habs
  obtain ⟨H, hrep⟩ := rationalMultiple_eq_polynomial_mul_dilate_of_dvd
    b hb A hA0 hdegree e P D hD0 he
  rw [hrep]
  exact hcanonical.polynomial_mul_dilate hα H (b ^ e)
    (pow_pos (by omega) e)

end IndependentZeroBlocks
