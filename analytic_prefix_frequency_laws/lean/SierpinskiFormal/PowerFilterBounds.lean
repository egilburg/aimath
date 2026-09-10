import SierpinskiFormal.ExactPowerGrowth
import SierpinskiFormal.ProductPrefixes

set_option autoImplicit false
namespace IndependentZeroBlocks
open SierpinskiFormal

/-! Public support-count interfaces extracted from the density proof. The
original source is retained unchanged; these interfaces expose its elementary
counting arguments for power-growth consumers. -/

theorem supportCount_dilate_le_self_count
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

theorem supportCount_polynomial_mul_le_degree_count
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


/-- A polynomial multiple of a positive dilation preserves every support
power upper bound, without changing its exponent. -/
theorem HasPowerPredicateBound.polynomial_mul_dilate
    {K : Type*} [Field K] {F : PowerSeries K} {α : ℝ}
    (hF : HasPowerPredicateBound α (fun n => PowerSeries.coeff n F ≠ 0))
    (H : Polynomial K) (q : ℕ) (hq : 0 < q) :
    HasPowerPredicateBound α (fun n => PowerSeries.coeff n
      ((H : PowerSeries K) * SierpinskiFormal.dilate q F) ≠ 0) := by
  obtain ⟨C, hC, N₀, hbound⟩ := (powerPredicateBound_support_iff F α).mp hF
  apply (powerPredicateBound_support_iff _ α).mpr
  refine ⟨(H.natDegree + 1 : ℕ) * C, by positivity, N₀, ?_⟩
  intro N hN
  have hn := (supportCount_polynomial_mul_le_degree_count H (SierpinskiFormal.dilate q F) N).trans
    (Nat.mul_le_mul_left (H.natDegree + 1) (supportCount_dilate_le_self_count q hq F N))
  calc
    (supportCount ((H : PowerSeries K) * SierpinskiFormal.dilate q F) N : ℝ) ≤
        (H.natDegree + 1 : ℕ) * (supportCount F N : ℝ) := by exact_mod_cast hn
    _ ≤ (H.natDegree + 1 : ℕ) * (C * (N : ℝ) ^ α) :=
      mul_le_mul_of_nonneg_left (hbound N hN) (by positivity)
    _ = _ := by ring

/-- An exact nonzero coefficient fiber embeds support into a longer prefix. -/
theorem supportCount_le_of_coefficient_fiber
    {K : Type*} [Field K] (F U : PowerSeries K)
    (q r : ℕ) (hq : 0 < q) (hr : r < q) (c : K) (hc : c ≠ 0)
    (hfiber : ∀ n, PowerSeries.coeff (q * n + r) U = c * PowerSeries.coeff n F)
    (N : ℕ) : supportCount F N ≤ supportCount U (q * N) := by
  classical
  let S := (Finset.range N).filter (fun n => PowerSeries.coeff n F ≠ 0)
  let T := (Finset.range (q * N)).filter (fun n => PowerSeries.coeff n U ≠ 0)
  have hmap : ∀ n ∈ S, q * n + r ∈ T := by
    intro n hn
    simp only [S, Finset.mem_filter, Finset.mem_range] at hn
    simp only [T, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, ?_⟩
    · calc
        q * n + r < q * n + q := Nat.add_lt_add_left hr _
        _ = q * (n + 1) := by ring
        _ ≤ q * N := Nat.mul_le_mul_left q hn.1
    · rw [hfiber]
      exact mul_ne_zero hc hn.2
  have hinj : (S : Set ℕ).InjOn (fun n => q * n + r) := by
    intro n hn m hm heq
    exact Nat.eq_of_mul_eq_mul_left hq (Nat.add_right_cancel heq)
  simpa [S, T, supportCount] using Finset.card_le_card_of_injOn
    (fun n => q * n + r) hmap hinj

/-- A radix-scale support lower bound and an upper power bound give a
two-sided exact exponent, without an exact total-count formula. -/
theorem hasPowerSupportGrowth_of_radix_lower_bound
    {K : Type*} [Semiring K] (U : PowerSeries K)
    (b s E : ℕ) (hb : 2 ≤ b) (hs : 1 ≤ s)
    (α : ℝ) (hα : 0 ≤ α) (hscale : (b : ℝ) ^ α = (s : ℝ))
    (hupper : HasPowerPredicateBound α (fun n => PowerSeries.coeff n U ≠ 0))
    (hlower : ∀ n, s ^ n ≤ supportCount U (b ^ (E + n))) :
    HasPowerSupportGrowth U α := by
  obtain ⟨C, hC, N₀, hupper⟩ := (powerPredicateBound_support_iff U α).mp hupper
  have hspos : (0 : ℝ) < (s : ℝ) := by positivity
  have hpow (e : ℕ) : (((b ^ e : ℕ) : ℝ) ^ α) = (s : ℝ) ^ e := by
    calc
      (((b ^ e : ℕ) : ℝ) ^ α) = ((b : ℝ) ^ e) ^ α := by norm_num
      _ = ((b : ℝ) ^ α) ^ e := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        rw [mul_comm, Real.rpow_mul (by positivity), Real.rpow_natCast]
      _ = (s : ℝ) ^ e := by rw [hscale]
  refine ⟨1 / (s : ℝ) ^ (E + 1), C + 1, by positivity, by linarith,
    max N₀ (b ^ E), ?_⟩
  intro N hN
  have hN₀ : N₀ ≤ N := (le_max_left _ _).trans hN
  have hEN : b ^ E ≤ N := (le_max_right _ _).trans hN
  have hNne : N ≠ 0 := by have := pow_pos (by omega : 0 < b) E; omega
  let e := Nat.log b N
  have hEe : E ≤ e := Nat.le_log_of_pow_le (by omega) hEN
  let n := e - E
  have hEn : E + n = e := Nat.add_sub_of_le hEe
  have hbN : b ^ e ≤ N := Nat.pow_log_le_self b hNne
  have hNb : N < b ^ (e + 1) := Nat.lt_pow_succ_log_self (by omega) N
  have hcount : (s : ℝ) ^ n ≤ (supportCount U N : ℝ) := by
    exact_mod_cast (show s ^ n ≤ supportCount U N from
      (hlower n).trans (supportCount_mono U (by rw [hEn]; exact hbN)))
  have hpupper : (N : ℝ) ^ α ≤ (s : ℝ) ^ (e + 1) := by
    rw [← hpow]
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hNb.le) hα
  constructor
  · apply le_trans ?_ hcount
    calc
      (1 / (s : ℝ) ^ (E + 1)) * (N : ℝ) ^ α ≤
          (1 / (s : ℝ) ^ (E + 1)) * (s : ℝ) ^ (e + 1) :=
        mul_le_mul_of_nonneg_left hpupper (by positivity)
      _ = (s : ℝ) ^ n := by
        rw [← hEn]
        field_simp
        ring
  · exact (hupper N hN₀).trans
      (mul_le_mul_of_nonneg_right (by linarith : C ≤ C + 1) (by positivity))

end IndependentZeroBlocks
