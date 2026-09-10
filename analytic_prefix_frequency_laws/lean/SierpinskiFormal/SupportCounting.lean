import SierpinskiFormal.SupportDensityDefs
import SierpinskiFormal.CanonicalSeries
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Log

set_option autoImplicit false

/-!
# Upper bounds for power-series coefficient support

This file proves that the digit-product canonical series of a polynomial whose
degree is strictly below `b - 1` has ordinary support density zero.  It also
records that dilation by a positive integer and multiplication by a polynomial
preserve support density zero.
-/

namespace IndependentZeroBlocks

open Filter
open scoped Topology
open SierpinskiFormal

/-- The number of nonzero coefficients below a cutoff is monotone in the
cutoff. -/
theorem supportCount_mono {K : Type*} [Semiring K] (F : PowerSeries K)
    {M N : ℕ} (hMN : M ≤ N) : supportCount F M ≤ supportCount F N := by
  classical
  apply Finset.card_le_card
  intro n hn
  simp only [supportCount, Finset.mem_filter, Finset.mem_range] at hn ⊢
  exact ⟨lt_of_lt_of_le hn.1 hMN, hn.2⟩

private theorem canonical_supportCount_radix_step
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1) (e : ℕ) :
    supportCount (canonicalSeries b A) (b ^ (e + 1)) ≤
      (A.natDegree + 1) * supportCount (canonicalSeries b A) (b ^ e) := by
  classical
  let S := (Finset.range (b ^ (e + 1))).filter fun n =>
    PowerSeries.coeff n (canonicalSeries b A) ≠ 0
  let T := Finset.range (A.natDegree + 1) ×ˢ
    ((Finset.range (b ^ e)).filter fun n =>
      PowerSeries.coeff n (canonicalSeries b A) ≠ 0)
  let f : ℕ → ℕ × ℕ := fun n => (n % b, n / b)
  have hf : ∀ n ∈ S, f n ∈ T := by
    intro n hn
    have hnmem := hn
    simp only [S, Finset.mem_filter, Finset.mem_range] at hnmem
    have hrem : n % b < b := Nat.mod_lt n (by omega)
    have hsplit : b * (n / b) + n % b = n := Nat.div_add_mod n b
    have hcoeff :
        PowerSeries.coeff (n / b) (canonicalSeries b A) * A.coeff (n % b) ≠ 0 := by
      rw [← coeff_canonicalSeries_mul_add b hb A hA0 (n / b) (n % b) hrem]
      simpa [hsplit] using hnmem.2
    have hremDegree : n % b ≤ A.natDegree :=
      Polynomial.le_natDegree_of_ne_zero (right_ne_zero_of_mul hcoeff)
    have hquot : n / b < b ^ e := by
      have hnlt : n < b ^ e * b := by
        simpa [pow_succ, Nat.mul_comm] using hnmem.1
      exact (Nat.div_lt_iff_lt_mul (by omega)).2 hnlt
    simp only [f, T, Finset.mem_product, Finset.mem_range, Finset.mem_filter]
    exact ⟨Nat.lt_succ_of_le hremDegree, hquot, left_ne_zero_of_mul hcoeff⟩
  have finj : (S : Set ℕ).InjOn f := by
    intro m hm n hn hmn
    have hmod : m % b = n % b := congrArg Prod.fst hmn
    have hdiv : m / b = n / b := congrArg Prod.snd hmn
    calc
      m = m % b + b * (m / b) := (Nat.mod_add_div m b).symm
      _ = n % b + b * (n / b) := by rw [hmod, hdiv]
      _ = n := Nat.mod_add_div n b
  have hcard := Finset.card_le_card_of_injOn f hf finj
  simpa [S, T, supportCount, Finset.card_product] using hcard

/-- Below the first `e` radix digits, the support of the canonical series has
at most `(A.natDegree + 1) ^ e` elements. -/
theorem supportCount_canonicalSeries_pow_le
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1) (e : ℕ) :
    supportCount (canonicalSeries b A) (b ^ e) ≤ (A.natDegree + 1) ^ e := by
  classical
  induction e with
  | zero =>
      change ((Finset.range 1).filter fun n =>
        PowerSeries.coeff n (canonicalSeries b A) ≠ 0).card ≤ 1
      exact (Finset.card_filter_le _ _).trans_eq (by simp)
  | succ e ih =>
      calc
        supportCount (canonicalSeries b A) (b ^ (e + 1)) ≤
            (A.natDegree + 1) *
              supportCount (canonicalSeries b A) (b ^ e) :=
          canonical_supportCount_radix_step b hb A hA0 e
        _ ≤ (A.natDegree + 1) * (A.natDegree + 1) ^ e :=
          Nat.mul_le_mul_left _ ih
        _ = (A.natDegree + 1) ^ (e + 1) := by rw [pow_succ]; ac_rfl

private theorem tendsto_nat_log_atTop (b : ℕ) (hb : 1 < b) :
    Tendsto (Nat.log b) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro e
  refine ⟨b ^ e, ?_⟩
  intro N hN
  exact Nat.le_log_of_pow_le hb hN

/-- The canonical digit-product series has ordinary support density zero when
the number of potentially nonzero digits is strictly smaller than the radix. -/
theorem hasZeroSupportDensity_canonicalSeries
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b - 1) :
    HasZeroSupportDensity (canonicalSeries b A) := by
  let c := A.natDegree + 1
  have hcb : c < b := by
    dsimp [c]
    omega
  have hratio_nonneg : 0 ≤ (c : ℝ) / (b : ℝ) := by positivity
  have hratio_lt_one : (c : ℝ) / (b : ℝ) < 1 := by
    rw [div_lt_one (by positivity : (0 : ℝ) < b)]
    exact Nat.cast_lt.2 hcb
  have hgeom : Tendsto
      (fun N : ℕ => (c : ℝ) * ((c : ℝ) / (b : ℝ)) ^ Nat.log b N)
      atTop (𝓝 0) := by
    simpa using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hratio_nonneg hratio_lt_one).comp
        (tendsto_nat_log_atTop b (by omega))).const_mul (c : ℝ)
  apply squeeze_zero'
  · filter_upwards with N
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hNne : N ≠ 0 := by omega
    let l := Nat.log b N
    have hpowN : b ^ l ≤ N := Nat.pow_log_le_self b hNne
    have hNnext : N ≤ b ^ (l + 1) :=
      Nat.le_of_lt (Nat.lt_pow_succ_log_self (by omega) N)
    have hcountNat : supportCount (canonicalSeries b A) N ≤ c ^ (l + 1) :=
      (supportCount_mono _ hNnext).trans (by
        simpa [c] using supportCount_canonicalSeries_pow_le b hb A hA0 (l + 1))
    have hcountReal :
        (supportCount (canonicalSeries b A) N : ℝ) ≤ (c ^ (l + 1) : ℕ) :=
      Nat.cast_le.2 hcountNat
    have hpowReal : ((b ^ l : ℕ) : ℝ) ≤ (N : ℝ) := Nat.cast_le.2 hpowN
    calc
      (supportCount (canonicalSeries b A) N : ℝ) / (N : ℝ) ≤
          ((c ^ (l + 1) : ℕ) : ℝ) / (N : ℝ) :=
        div_le_div_of_nonneg_right hcountReal (by positivity)
      _ ≤ ((c ^ (l + 1) : ℕ) : ℝ) / ((b ^ l : ℕ) : ℝ) := by
        exact div_le_div_of_nonneg_left (by positivity) (by positivity) hpowReal
      _ = (c : ℝ) * ((c : ℝ) / (b : ℝ)) ^ Nat.log b N := by
        simp only [l, Nat.cast_pow, Nat.cast_ofNat, pow_succ, div_pow]
        field_simp
        push_cast
        ring
  · exact hgeom

private theorem supportCount_dilate_le
    {K : Type*} [CommRing K] (q : ℕ) (hq : 0 < q)
    (F : PowerSeries K) (N : ℕ) :
    supportCount (dilate q F) N ≤ supportCount F N := by
  classical
  let S := (Finset.range N).filter fun n =>
    PowerSeries.coeff n (dilate q F) ≠ 0
  let T := (Finset.range N).filter fun n => PowerSeries.coeff n F ≠ 0
  let f : ℕ → ℕ := fun n => n / q
  have hf : ∀ n ∈ S, f n ∈ T := by
    intro n hn
    have hnmem := hn
    simp only [S, Finset.mem_filter, Finset.mem_range] at hnmem
    have hdivides : q ∣ n := by
      by_contra hd
      rw [SierpinskiFormal.coeff_dilate, if_neg hd] at hnmem
      exact hnmem.2 rfl
    have hNmul : N ≤ N * q := by
      simpa using Nat.mul_le_mul_left N (Nat.succ_le_iff.2 hq)
    have hquotlt : n / q < N :=
      (Nat.div_lt_iff_lt_mul hq).2 (hnmem.1.trans_le hNmul)
    simp only [f, T, Finset.mem_filter, Finset.mem_range]
    simpa [SierpinskiFormal.coeff_dilate, hdivides] using And.intro hquotlt hnmem.2
  have finj : (S : Set ℕ).InjOn f := by
    intro m hm n hn hmn
    have hm' := hm
    have hn' := hn
    simp only [S, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hm' hn'
    have hmd : q ∣ m := by
      by_contra hd
      rw [SierpinskiFormal.coeff_dilate, if_neg hd] at hm'
      exact hm'.2 rfl
    have hnd : q ∣ n := by
      by_contra hd
      rw [SierpinskiFormal.coeff_dilate, if_neg hd] at hn'
      exact hn'.2 rfl
    change m / q = n / q at hmn
    calc
      m = q * (m / q) := (Nat.mul_div_cancel_left' hmd).symm
      _ = q * (n / q) := by rw [hmn]
      _ = n := Nat.mul_div_cancel_left' hnd
  simpa [S, T, supportCount] using Finset.card_le_card_of_injOn f hf finj

/-- Dilation by a positive integer preserves ordinary support density zero. -/
theorem HasZeroSupportDensity.dilate
    {K : Type*} [CommRing K] {F : PowerSeries K}
    (hF : HasZeroSupportDensity F) (q : ℕ) (hq : 0 < q) :
    HasZeroSupportDensity (SierpinskiFormal.dilate q F) := by
  apply squeeze_zero'
  · filter_upwards with N
    positivity
  · filter_upwards with N
    exact div_le_div_of_nonneg_right
      (Nat.cast_le.2 (supportCount_dilate_le q hq F N)) (by positivity)
  · exact hF

private theorem exists_polynomial_mul_support_decomposition
    {K : Type*} [Field K] (H : Polynomial K) (F : PowerSeries K) (n : ℕ)
    (hn : PowerSeries.coeff n ((H : PowerSeries K) * F) ≠ 0) :
    ∃ ij : ℕ × ℕ, ij ∈ Finset.antidiagonal n ∧
      ij.1 ≤ H.natDegree ∧ PowerSeries.coeff ij.2 F ≠ 0 := by
  rw [PowerSeries.coeff_mul] at hn
  by_contra hnone
  push_neg at hnone
  apply hn
  apply Finset.sum_eq_zero
  intro ij hij
  have hz := hnone ij hij
  by_cases hHi : H.coeff ij.1 = 0
  · simp [hHi]
  · have hiDegree := Polynomial.le_natDegree_of_ne_zero hHi
    have hFj := hz hiDegree
    simp [hFj]

private theorem supportCount_polynomial_mul_le
    {K : Type*} [Field K] (H : Polynomial K) (F : PowerSeries K) (N : ℕ) :
    supportCount ((H : PowerSeries K) * F) N ≤
      (H.natDegree + 1) * supportCount F N := by
  classical
  let S := (Finset.range N).filter fun n =>
    PowerSeries.coeff n ((H : PowerSeries K) * F) ≠ 0
  let T := Finset.range (H.natDegree + 1) ×ˢ
    ((Finset.range N).filter fun n => PowerSeries.coeff n F ≠ 0)
  have hex (n : ℕ) (hn : PowerSeries.coeff n ((H : PowerSeries K) * F) ≠ 0) :
      ∃ ij : ℕ × ℕ, ij ∈ Finset.antidiagonal n ∧
        ij.1 ≤ H.natDegree ∧ PowerSeries.coeff ij.2 F ≠ 0 :=
    exists_polynomial_mul_support_decomposition H F n hn
  let f : ℕ → ℕ × ℕ := fun n =>
    if hn : PowerSeries.coeff n ((H : PowerSeries K) * F) ≠ 0 then
      Classical.choose (hex n hn)
    else (0, 0)
  have f_spec (n : ℕ) (hn : PowerSeries.coeff n ((H : PowerSeries K) * F) ≠ 0) :
      f n ∈ Finset.antidiagonal n ∧ (f n).1 ≤ H.natDegree ∧
        PowerSeries.coeff (f n).2 F ≠ 0 := by
    simpa [f, hn] using Classical.choose_spec (hex n hn)
  have hf : ∀ n ∈ S, f n ∈ T := by
    intro n hn
    have hnmem := hn
    simp only [S, Finset.mem_filter, Finset.mem_range] at hnmem
    have hs := f_spec n hnmem.2
    have hsum : (f n).1 + (f n).2 = n := Finset.mem_antidiagonal.mp hs.1
    simp only [T, Finset.mem_product, Finset.mem_range, Finset.mem_filter]
    exact ⟨Nat.lt_succ_of_le hs.2.1, by omega, hs.2.2⟩
  have finj : (S : Set ℕ).InjOn f := by
    intro m hm n hn hmn
    have hm' := hm
    have hn' := hn
    simp only [S, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hm' hn'
    have hms := Finset.mem_antidiagonal.mp (f_spec m hm'.2).1
    have hns := Finset.mem_antidiagonal.mp (f_spec n hn'.2).1
    rw [hmn] at hms
    omega
  have hcard := Finset.card_le_card_of_injOn f hf finj
  simpa [S, T, supportCount, Finset.card_product] using hcard

/-- Multiplication by a polynomial preserves ordinary support density zero. -/
theorem HasZeroSupportDensity.polynomial_mul
    {K : Type*} [Field K] {F : PowerSeries K}
    (hF : HasZeroSupportDensity F) (H : Polynomial K) :
    HasZeroSupportDensity ((H : PowerSeries K) * F) := by
  have hupper : Tendsto
      (fun N : ℕ => (H.natDegree + 1 : ℝ) *
        ((supportCount F N : ℝ) / (N : ℝ))) atTop (𝓝 0) := by
    simpa using hF.const_mul (H.natDegree + 1 : ℝ)
  apply squeeze_zero'
  · filter_upwards with N
    positivity
  · filter_upwards with N
    calc
      (supportCount ((H : PowerSeries K) * F) N : ℝ) / (N : ℝ) ≤
          (((H.natDegree + 1) * supportCount F N : ℕ) : ℝ) / (N : ℝ) :=
        div_le_div_of_nonneg_right
          (Nat.cast_le.2 (supportCount_polynomial_mul_le H F N)) (by positivity)
      _ = (H.natDegree + 1 : ℝ) *
          ((supportCount F N : ℝ) / (N : ℝ)) := by
        push_cast
        ring
  · exact hupper

/-- A polynomial multiple of a positive dilation of a zero-density series
again has zero support density. -/
theorem HasZeroSupportDensity.polynomial_mul_dilate
    {K : Type*} [Field K] {F : PowerSeries K}
    (hF : HasZeroSupportDensity F) (H : Polynomial K)
    (q : ℕ) (hq : 0 < q) :
    HasZeroSupportDensity
      ((H : PowerSeries K) * SierpinskiFormal.dilate q F) :=
  (hF.dilate q hq).polynomial_mul H

/-- The requested sparse form: every polynomial multiple of every positive
power-of-the-radix dilation of the canonical series has support density zero. -/
theorem hasZeroSupportDensity_polynomial_mul_dilate_canonicalSeries
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A H : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b - 1) (e : ℕ) :
    HasZeroSupportDensity
      ((H : PowerSeries K) *
        SierpinskiFormal.dilate (b ^ e) (canonicalSeries b A)) := by
  exact (hasZeroSupportDensity_canonicalSeries b hb A hA0 hdegree).polynomial_mul_dilate
    H (b ^ e) (pow_pos (by omega) e)

end IndependentZeroBlocks
