import SierpinskiFormal.MissingDigitGrowth
import SierpinskiFormal.PorousSupportBounds

set_option autoImplicit false

namespace IndependentZeroBlocks

open SierpinskiFormal

/-- Counting on a subinterval is bounded by counting on any containing
interval. -/
private theorem intervalPredicateCount_le_of_contained
    (bad : ℕ → Prop) {p a L M : ℕ} (hpa : p ≤ a)
    (hend : a + L ≤ p + M) :
    intervalPredicateCount bad a L ≤ intervalPredicateCount bad p M := by
  classical
  let f : ℕ → ℕ := fun j => (a - p) + j
  have hrepr : p + (a - p) = a := Nat.add_sub_of_le hpa
  have hf : ∀ j ∈ (Finset.range L).filter (fun j => bad (a + j)),
      f j ∈ (Finset.range M).filter (fun j => bad (p + j)) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    constructor
    · have hpoint : p + f j < p + M := by
        calc
          p + f j = (p + (a - p)) + j := by simp [f, Nat.add_assoc]
          _ = a + j := by rw [hrepr]
          _ < a + L := Nat.add_lt_add_left hj.1 a
          _ ≤ p + M := hend
      omega
    · have heq : p + f j = a + j := by
        calc
          p + f j = (p + (a - p)) + j := by simp [f, Nat.add_assoc]
          _ = a + j := by rw [hrepr]
      rw [heq]
      exact hj.2
  have hinj : Set.InjOn f
      (↑((Finset.range L).filter (fun j => bad (a + j))) : Set ℕ) := by
    intro x _ y _ hxy
    dsimp [f] at hxy
    omega
  unfold intervalPredicateCount
  exact Finset.card_le_card_of_injOn f hf hinj

/-- Every aligned radix block has no more supported canonical coefficients
than the support in one low-digit prefix. -/
theorem intervalPredicateCount_canonicalSeries_aligned_pow_le_digitSupport
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1) (e q : ℕ) :
    intervalPredicateCount
        (fun n => PowerSeries.coeff n (canonicalSeries b A) ≠ 0)
        (b ^ e * q) (b ^ e) ≤ radixDigitSupportCount b A ^ e := by
  classical
  calc
    intervalPredicateCount
        (fun n => PowerSeries.coeff n (canonicalSeries b A) ≠ 0)
        (b ^ e * q) (b ^ e) ≤ supportCount (canonicalSeries b A) (b ^ e) := by
      unfold intervalPredicateCount supportCount
      apply Finset.card_le_card
      intro r hr
      simp only [Finset.mem_filter, Finset.mem_range] at hr ⊢
      refine ⟨hr.1, ?_⟩
      rw [coeff_canonicalSeries_pow_mul_add b hb A hA0 e q r hr.1] at hr
      exact right_ne_zero_of_mul hr.2
    _ = radixDigitSupportCount b A ^ e :=
      supportCount_canonicalSeries_pow_eq_digitSupport b hb A hA0 e

/-- Any interval no longer than `b^e` meets at most two aligned radix blocks,
and consequently contains at most `2 s^e` supported coefficients. -/
theorem intervalPredicateCount_canonicalSeries_le_two_digitSupport_pow
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (a L e : ℕ) (hL : L ≤ b ^ e) :
    intervalPredicateCount
        (fun n => PowerSeries.coeff n (canonicalSeries b A) ≠ 0) a L ≤
      2 * radixDigitSupportCount b A ^ e := by
  let Q := b ^ e
  let p := Q * (a / Q)
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hpa : p ≤ a := by
    dsimp [p]
    exact Nat.mul_div_le a Q
  have haQ : a < p + Q := by
    dsimp [p]
    have h := Nat.lt_mul_div_succ a hQ
    nlinarith
  have hend : a + L ≤ p + 2 * Q := by
    have hLQ : L ≤ Q := by simpa [Q] using hL
    omega
  have hcontain := intervalPredicateCount_le_of_contained
    (fun n => PowerSeries.coeff n (canonicalSeries b A) ≠ 0) hpa hend
  rw [show 2 * Q = Q + Q by omega,
    intervalPredicateCount_add] at hcontain
  have hblock0 : intervalPredicateCount
      (fun n => PowerSeries.coeff n (canonicalSeries b A) ≠ 0) p Q ≤
      radixDigitSupportCount b A ^ e := by
    simpa [p, Q] using
      intervalPredicateCount_canonicalSeries_aligned_pow_le_digitSupport
        b hb A hA0 e (a / Q)
  have hblock1 : intervalPredicateCount
      (fun n => PowerSeries.coeff n (canonicalSeries b A) ≠ 0) (p + Q) Q ≤
      radixDigitSupportCount b A ^ e := by
    have hp1 : p + Q = b ^ e * (a / Q + 1) := by
      dsimp [p, Q]
      ring
    rw [hp1]
    simpa [Q] using
      intervalPredicateCount_canonicalSeries_aligned_pow_le_digitSupport
        b hb A hA0 e (a / Q + 1)
  exact hcontain.trans ((Nat.add_le_add hblock0 hblock1).trans_eq (by omega))

/-- The canonical digit-product support has the optimal logarithmic power
bound uniformly on every translated interval, with explicit constant twice
the number of supported digits. -/
theorem intervalPredicateCount_canonicalSeries_le_digitLog
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hsmall : radixDigitSupportCount b A < b)
    (a L : ℕ) (hL : 1 ≤ L) :
    (intervalPredicateCount
      (fun n => PowerSeries.coeff n (canonicalSeries b A) ≠ 0) a L : ℝ) ≤
        ((2 * radixDigitSupportCount b A : ℕ) : ℝ) *
          (L : ℝ) ^ digitSupportExponent b A := by
  let s := radixDigitSupportCount b A
  let α := digitSupportExponent b A
  have hs : 1 ≤ s := by
    dsimp [s]
    exact one_le_radixDigitSupportCount b (by omega) A hA0
  have hα : 0 ≤ α := by
    dsimp [α, digitSupportExponent]
    exact (radixDigitLogExponent_mem_Ico b hb A hA0 hsmall).1
  have hscale : (b : ℝ) ^ α = (s : ℝ) := by
    dsimp [α, s, digitSupportExponent]
    exact rpow_radixLogExponent b (radixDigitSupportCount b A) hb
      (one_le_radixDigitSupportCount b (by omega) A hA0)
  let l := Nat.log b L
  let e := l + 1
  have hLne : L ≠ 0 := by omega
  have hpowL : b ^ l ≤ L := by
    simpa [l] using Nat.pow_log_le_self b hLne
  have hLnext : L ≤ b ^ e := by
    exact Nat.le_of_lt (by
      simpa [l, e, Nat.succ_eq_add_one] using
        Nat.lt_pow_succ_log_self (by omega : 1 < b) L)
  have hcountNat := intervalPredicateCount_canonicalSeries_le_two_digitSupport_pow
    b hb A hA0 a L e hLnext
  have hpow_identity : (((b ^ l : ℕ) : ℝ) ^ α) = (s : ℝ) ^ l := by
    calc
      (((b ^ l : ℕ) : ℝ) ^ α) = ((b : ℝ) ^ l) ^ α := by norm_num
      _ = ((b : ℝ) ^ α) ^ l := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        rw [mul_comm, Real.rpow_mul (by positivity), Real.rpow_natCast]
      _ = (s : ℝ) ^ l := by rw [hscale]
  have hsPow : (s : ℝ) ^ l ≤ (L : ℝ) ^ α := by
    rw [← hpow_identity]
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hpowL) hα
  calc
    (intervalPredicateCount
        (fun n => PowerSeries.coeff n (canonicalSeries b A) ≠ 0) a L : ℝ) ≤
        ((2 * s ^ e : ℕ) : ℝ) := by exact_mod_cast hcountNat
    _ = ((2 * s : ℕ) : ℝ) * (s : ℝ) ^ l := by
      dsimp [e]
      push_cast
      rw [pow_succ]
      ring
    _ ≤ ((2 * s : ℕ) : ℝ) * (L : ℝ) ^ α :=
      mul_le_mul_of_nonneg_left hsPow (by positivity)

/-- Existential-constant form of the uniform optimal digit bound. -/
theorem canonicalSeries_uniformDigitLog_intervalBound
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hsmall : radixDigitSupportCount b A < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a L : ℕ, 1 ≤ L →
      (intervalPredicateCount
        (fun n => PowerSeries.coeff n (canonicalSeries b A) ≠ 0) a L : ℝ) ≤
          C * (L : ℝ) ^ digitSupportExponent b A := by
  refine ⟨((2 * radixDigitSupportCount b A : ℕ) : ℝ), by positivity, ?_⟩
  exact intervalPredicateCount_canonicalSeries_le_digitLog b hb A hA0 hsmall

end IndependentZeroBlocks
