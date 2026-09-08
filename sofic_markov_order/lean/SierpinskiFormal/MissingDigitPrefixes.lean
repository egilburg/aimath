import SierpinskiFormal.ProductPrefixes

set_option autoImplicit false

namespace IndependentZeroBlocks

open SierpinskiFormal
open scoped BigOperators

variable {K : Type*} [Field K]

/-- The part of a radix kernel strictly below digit `m`. -/
noncomputable def missingDigitPrefix (A : Polynomial K) (m : ℕ) : Polynomial K :=
  ∑ j ∈ Finset.range m, Polynomial.monomial j (A.coeff j)

@[simp] theorem coeff_missingDigitPrefix (A : Polynomial K) (m n : ℕ) :
    (missingDigitPrefix A m).coeff n = if n < m then A.coeff n else 0 := by
  classical
  simp [missingDigitPrefix, Polynomial.coeff_monomial]

/-- Multiplication on the left preserves coefficient agreement below a
cutoff. -/
private theorem coeff_mul_eq_of_eq_below
    (U S T : PowerSeries K) (N : ℕ)
    (hST : ∀ j : ℕ, j < N →
      PowerSeries.coeff j S = PowerSeries.coeff j T) :
    ∀ n : ℕ, n < N →
      PowerSeries.coeff n (U * S) = PowerSeries.coeff n (U * T) := by
  intro n hn
  simp only [PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [hST ij.2]
  have := Finset.mem_antidiagonal.mp hij
  omega

/-- Below the radix, canonical-series coefficients are the kernel
coefficients. -/
private theorem coeff_canonicalSeries_of_lt
    (b : ℕ) (hb : 2 ≤ b) (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (n : ℕ) (hn : n < b) :
    PowerSeries.coeff n (canonicalSeries b A) = A.coeff n := by
  simpa using coeff_canonicalSeries_mul_add b hb A hA0 0 n hn

/-- At scale `b^e`, the canonical tail and the expanded missing-digit prefix
agree through the missing digit block. -/
private theorem coeff_dilate_canonical_eq_missingPrefix
    (b : ℕ) (hb : 2 ≤ b) (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (e m : ℕ) (hm : m < b) (hAm : A.coeff m = 0) :
    ∀ n : ℕ, n < (m + 1) * b ^ e →
      PowerSeries.coeff n (dilate (b ^ e) (canonicalSeries b A)) =
        PowerSeries.coeff n
          (Polynomial.expand K (b ^ e) (missingDigitPrefix A m) : Polynomial K) := by
  intro n hn
  have hQ : 0 < b ^ e := pow_pos (by omega) e
  simp only [coeff_dilate, Polynomial.coeff_coe, Polynomial.coeff_expand hQ]
  by_cases hd : b ^ e ∣ n
  · rw [if_pos hd, if_pos hd]
    have hquot : n / b ^ e < m + 1 :=
      (Nat.div_lt_iff_lt_mul hQ).mpr (by simpa [Nat.mul_comm] using hn)
    have hquotb : n / b ^ e < b := hquot.trans_le (by omega)
    rw [coeff_canonicalSeries_of_lt b hb A hA0 _ hquotb]
    by_cases hlt : n / b ^ e < m
    · simp [hlt]
    · have heq : n / b ^ e = m := by omega
      simp [heq, hAm]
  · rw [if_neg hd, if_neg hd]

/-- First polynomial numerator attached to the missing digit `m`. -/
noncomputable def missingDigitFirstNumerator
    (b : ℕ) (A P : Polynomial K) (e m : ℕ) : Polynomial K :=
  P * kernelPrefix b A e *
    Polynomial.expand K (b ^ e) (missingDigitPrefix A m)

/-- The first numerator agrees with `P * canonicalSeries b A` through the
first missing-digit gap. -/
theorem coeff_missingDigitFirstNumerator
    (b : ℕ) (hb : 2 ≤ b) (A P : Polynomial K)
    (hA0 : A.coeff 0 = 1) (hdegree : A.natDegree < b)
    (m e n : ℕ) (hm : m < b) (hAm : A.coeff m = 0)
    (hn : n < (m + 1) * b ^ e) :
    PowerSeries.coeff n ((P : PowerSeries K) * canonicalSeries b A) =
      (missingDigitFirstNumerator b A P e m).coeff n := by
  rw [canonicalSeries_eq_kernelPrefix_mul_dilate b hb A hA0 hdegree e]
  rw [← mul_assoc]
  have h := coeff_mul_eq_of_eq_below
    ((P * kernelPrefix b A e : Polynomial K) : PowerSeries K)
    (dilate (b ^ e) (canonicalSeries b A))
    (Polynomial.expand K (b ^ e) (missingDigitPrefix A m) : Polynomial K)
    ((m + 1) * b ^ e)
    (coeff_dilate_canonical_eq_missingPrefix b hb A hA0 e m hm hAm) n hn
  rw [show (missingDigitFirstNumerator b A P e m).coeff n =
      PowerSeries.coeff n
        (missingDigitFirstNumerator b A P e m : PowerSeries K) by
        simp]
  simpa [missingDigitFirstNumerator, Polynomial.coe_mul] using h

/-- The kernel terms through its first positive supported digit. -/
noncomputable def firstSupportedDigitPrefix
    (A : Polynomial K) (k : ℕ) : Polynomial K :=
  1 + Polynomial.monomial k (A.coeff k)

private theorem coeff_firstSupportedDigitPrefix
    (A : Polynomial K) {k : ℕ} (hk : 0 < k) (n : ℕ) :
    (firstSupportedDigitPrefix A k).coeff n =
      if n = 0 then 1 else if n = k then A.coeff k else 0 := by
  classical
  by_cases hn0 : n = 0
  · subst n
    simp [firstSupportedDigitPrefix, Polynomial.coeff_monomial, hk.ne']
  · by_cases hnk : n = k
    · subst n
      simp [firstSupportedDigitPrefix, Polynomial.coeff_monomial,
        Polynomial.coeff_one, hk.ne']
    · simp [firstSupportedDigitPrefix, Polynomial.coeff_monomial,
        Polynomial.coeff_one, hn0, hnk, Ne.symm hnk]

/-- Dilating the canonical tail at a radix scale agrees with the two-term
kernel prefix through the first positive supported digit. -/
private theorem coeff_dilate_canonical_eq_firstSupportedPrefix
    (b : ℕ) (hb : 2 ≤ b) (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (k Q : ℕ) (hQ : 0 < Q) (hk : 0 < k) (hkb : k < b)
    (hprior : ∀ j : ℕ, 0 < j → j < k → A.coeff j = 0) :
    ∀ n : ℕ, n < (k + 1) * Q →
      PowerSeries.coeff n (dilate Q (canonicalSeries b A)) =
        PowerSeries.coeff n
          (Polynomial.expand K Q (firstSupportedDigitPrefix A k) : Polynomial K) := by
  intro n hn
  simp only [coeff_dilate, Polynomial.coeff_coe, Polynomial.coeff_expand hQ]
  by_cases hd : Q ∣ n
  · rw [if_pos hd, if_pos hd]
    have hquot : n / Q < k + 1 :=
      (Nat.div_lt_iff_lt_mul hQ).mpr (by simpa [Nat.mul_comm] using hn)
    have hquotb : n / Q < b := hquot.trans_le (by omega)
    rw [coeff_canonicalSeries_of_lt b hb A hA0 _ hquotb]
    rw [coeff_firstSupportedDigitPrefix A hk]
    by_cases hz : n / Q = 0
    · simp [hz, hA0]
    · by_cases hkq : n / Q = k
      · simp [hz, hkq, hk.ne']
      · have hpos : 0 < n / Q := Nat.pos_of_ne_zero hz
        have hlt : n / Q < k := by omega
        simp [hz, hkq, hprior _ hpos hlt]
  · rw [if_neg hd, if_neg hd]

/-- The expanded full kernel and expanded missing-digit prefix agree through
the missing digit, since that digit has coefficient zero. -/
private theorem coeff_expand_eq_missingPrefix
    (A : Polynomial K) (Q m : ℕ) (hQ : 0 < Q) (hAm : A.coeff m = 0) :
    ∀ n : ℕ, n < (m + 1) * Q →
      (Polynomial.expand K Q A).coeff n =
        (Polynomial.expand K Q (missingDigitPrefix A m)).coeff n := by
  intro n hn
  simp only [Polynomial.coeff_expand hQ]
  by_cases hd : Q ∣ n
  · rw [if_pos hd, if_pos hd]
    have hquot : n / Q < m + 1 :=
      (Nat.div_lt_iff_lt_mul hQ).mpr (by simpa [Nat.mul_comm] using hn)
    by_cases hlt : n / Q < m
    · simp [hlt]
    · have heq : n / Q = m := by omega
      simp [heq, hAm]
  · rw [if_neg hd, if_neg hd]

/-- The next complete kernel prefix and its missing-digit truncation have the
same coefficients up to the end of the missing block. -/
private theorem coeff_kernelPrefix_succ_eq_missingPrefix
    (b : ℕ) (hb : 2 ≤ b) (A : Polynomial K)
    (e m : ℕ) (hAm : A.coeff m = 0) :
    ∀ n : ℕ, n < (m + 1) * b ^ e →
      (kernelPrefix b A (e + 1)).coeff n =
        (kernelPrefix b A e *
          Polynomial.expand K (b ^ e) (missingDigitPrefix A m)).coeff n := by
  intro n hn
  have hQ : 0 < b ^ e := pow_pos (by omega) e
  have h := coeff_mul_eq_of_eq_below
    (kernelPrefix b A e : PowerSeries K)
    (Polynomial.expand K (b ^ e) A : Polynomial K)
    (Polynomial.expand K (b ^ e) (missingDigitPrefix A m) : Polynomial K)
    ((m + 1) * b ^ e)
    (fun j hj => by
      simpa using coeff_expand_eq_missingPrefix A (b ^ e) m hQ hAm j hj)
    n hn
  have hprefix : kernelPrefix b A (e + 1) =
      kernelPrefix b A e * Polynomial.expand K (b ^ e) A := by
    simp [kernelPrefix, Finset.prod_range_succ]
  rw [hprefix, ← Polynomial.coeff_coe, ← Polynomial.coeff_coe]
  simpa only [Polynomial.coe_mul] using h

/-- Shifting two polynomials by the same monomial preserves their coefficient
agreement, with the cutoff shifted by the monomial exponent. -/
private theorem coeff_monomial_mul_eq_of_eq_below
    (a : K) (r : ℕ) (S T : Polynomial K) (N : ℕ)
    (hST : ∀ j : ℕ, j < N → S.coeff j = T.coeff j) :
    ∀ n : ℕ, n < r + N →
      (Polynomial.monomial r a * S).coeff n =
        (Polynomial.monomial r a * T).coeff n := by
  intro n hn
  by_cases hrn : r ≤ n
  · have hsub : n - r < N := by omega
    have hnrepr : n - r + r = n := by omega
    rw [← hnrepr, Polynomial.coeff_monomial_mul,
      Polynomial.coeff_monomial_mul, hST _ hsub]
  · have hnlt : n < r := Nat.lt_of_not_ge hrn
    rw [← Polynomial.coeff_coe, ← Polynomial.coeff_coe,
      Polynomial.coe_mul, Polynomial.coe_mul,
      coe_monomial_mul, coe_monomial_mul]
    simp [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', hrn]

/-- Second polynomial numerator, using the first positive supported digit
`k` and the same missing digit `m`. -/
noncomputable def missingDigitSecondNumerator
    (b : ℕ) (A P : Polynomial K) (e m k : ℕ) : Polynomial K :=
  P * kernelPrefix b A (e + 1) +
    Polynomial.monomial (k * b * b ^ e) (A.coeff k) *
      missingDigitFirstNumerator b A P e m

/-- The second numerator agrees with `P * canonicalSeries b A` through the
second missing-digit gap. -/
theorem coeff_missingDigitSecondNumerator
    (b : ℕ) (hb : 2 ≤ b) (A P : Polynomial K)
    (hA0 : A.coeff 0 = 1) (hdegree : A.natDegree < b)
    (m k e n : ℕ) (hm : m < b) (hAm : A.coeff m = 0)
    (hk : 0 < k) (hkb : k < b)
    (hprior : ∀ j : ℕ, 0 < j → j < k → A.coeff j = 0)
    (hn : n < (k * b + m + 1) * b ^ e) :
    PowerSeries.coeff n ((P : PowerSeries K) * canonicalSeries b A) =
      (missingDigitSecondNumerator b A P e m k).coeff n := by
  let Q := b ^ e
  let R := b ^ (e + 1)
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hcut_le : (k * b + m + 1) * Q ≤ (k + 1) * R := by
    have hm1 : m + 1 ≤ b := by omega
    calc
      (k * b + m + 1) * Q = k * b * Q + (m + 1) * Q := by ring
      _ ≤ k * b * Q + b * Q :=
        Nat.add_le_add_left (Nat.mul_le_mul_right Q hm1) _
      _ = (k + 1) * R := by
        dsimp [R, Q]
        rw [pow_succ]
        ring
  rw [canonicalSeries_eq_kernelPrefix_mul_dilate b hb A hA0 hdegree (e + 1)]
  rw [← mul_assoc]
  have htail := coeff_mul_eq_of_eq_below
    (((P * kernelPrefix b A (e + 1) : Polynomial K)) : PowerSeries K)
    (dilate R (canonicalSeries b A))
    (Polynomial.expand K R (firstSupportedDigitPrefix A k) : Polynomial K)
    ((k + 1) * R)
    (coeff_dilate_canonical_eq_firstSupportedPrefix b hb A hA0 k R hR hk hkb hprior)
    n (hn.trans_le hcut_le)
  have hexpand : Polynomial.expand K R (firstSupportedDigitPrefix A k) =
      1 + Polynomial.monomial (k * R) (A.coeff k) := by
    simp [firstSupportedDigitPrefix, map_add, Polynomial.expand_monomial]
  rw [hexpand] at htail
  have hcoeone : ((1 : Polynomial K) : PowerSeries K) = 1 := by
    ext j
    simp
  have hsmall : ∀ j : ℕ, j < (m + 1) * Q →
      (P * kernelPrefix b A (e + 1)).coeff j =
        (missingDigitFirstNumerator b A P e m).coeff j := by
    have hbase := coeff_mul_eq_of_eq_below (P : PowerSeries K)
      (kernelPrefix b A (e + 1) : Polynomial K)
      (kernelPrefix b A e *
        Polynomial.expand K Q (missingDigitPrefix A m) : Polynomial K)
      ((m + 1) * Q)
      (fun j hj => by
        simpa only [Polynomial.coeff_coe] using
          coeff_kernelPrefix_succ_eq_missingPrefix b hb A e m hAm j hj)
    intro j hj
    have := hbase j hj
    rw [← Polynomial.coeff_coe, ← Polynomial.coeff_coe]
    simpa only [missingDigitFirstNumerator, Polynomial.coe_mul, mul_assoc] using this
  have hshift : (k * R : ℕ) = k * b * Q := by
    dsimp [Q, R]
    rw [pow_succ]
    ring
  have hshifted := coeff_monomial_mul_eq_of_eq_below (A.coeff k) (k * R)
    (P * kernelPrefix b A (e + 1))
    (missingDigitFirstNumerator b A P e m) ((m + 1) * Q) hsmall
    n (by
      have heq : (k * b + m + 1) * Q = k * b * Q + (m + 1) * Q := by ring
      rw [heq] at hn
      simpa [hshift] using hn)
  have htail' :
      PowerSeries.coeff n
          (((P * kernelPrefix b A (e + 1) : Polynomial K) : PowerSeries K) *
            dilate R (canonicalSeries b A)) =
        PowerSeries.coeff n
          ((P * kernelPrefix b A (e + 1) +
            Polynomial.monomial (k * R) (A.coeff k) *
              (P * kernelPrefix b A (e + 1)) : Polynomial K) : PowerSeries K) := by
    calc
      _ = PowerSeries.coeff n
          (((P * kernelPrefix b A (e + 1) : Polynomial K) : PowerSeries K) *
            ((1 + Polynomial.monomial (k * R) (A.coeff k) : Polynomial K) :
              PowerSeries K)) := htail
      _ = _ := by
        congr 1
        simp only [Polynomial.coe_add, Polynomial.coe_mul, hcoeone, mul_one]
        ring
  have hshiftedPS :
      PowerSeries.coeff n
          ((Polynomial.monomial (k * R) (A.coeff k) *
            (P * kernelPrefix b A (e + 1)) : Polynomial K) : PowerSeries K) =
        PowerSeries.coeff n
          ((Polynomial.monomial (k * R) (A.coeff k) *
            missingDigitFirstNumerator b A P e m : Polynomial K) : PowerSeries K) := by
    simpa only [Polynomial.coeff_coe] using hshifted
  calc
    _ = PowerSeries.coeff n
        ((P * kernelPrefix b A (e + 1) +
          Polynomial.monomial (k * R) (A.coeff k) *
            (P * kernelPrefix b A (e + 1)) : Polynomial K) : PowerSeries K) := by
              simpa [R, Polynomial.coe_mul] using htail'
    _ = PowerSeries.coeff n
        ((P * kernelPrefix b A (e + 1) +
          Polynomial.monomial (k * R) (A.coeff k) *
            missingDigitFirstNumerator b A P e m : Polynomial K) : PowerSeries K) := by
      simp only [Polynomial.coeff_coe, Polynomial.coeff_add]
      exact congrArg (fun z => (P * kernelPrefix b A (e + 1)).coeff n + z) hshifted
    _ = (missingDigitSecondNumerator b A P e m k).coeff n := by
      simp only [Polynomial.coeff_coe]
      rw [show k * R = k * b * b ^ e by simpa [Q] using hshift]
      rfl

/-- The truncated digit polynomial has degree strictly below its cutoff. -/
theorem missingDigitPrefix_natDegree_lt
    (A : Polynomial K) {m : ℕ} (hm : 0 < m) :
    (missingDigitPrefix A m).natDegree < m := by
  have hle : (missingDigitPrefix A m).natDegree ≤ m - 1 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro n hn
    rw [coeff_missingDigitPrefix]
    simp only [ite_eq_right_iff]
    intro hnm
    omega
  omega

/-- Under the no-carry hypothesis `deg A < b`, every complete kernel prefix
has degree below its radix scale. -/
theorem kernelPrefix_natDegree_lt_pow_of_lt
    (b : ℕ) (hb : 2 ≤ b) (A : Polynomial K)
    (hdegree : A.natDegree < b) (e : ℕ) :
    (kernelPrefix b A e).natDegree < b ^ e := by
  have hbound := kernelPrefix_natDegree_bound b hb A e
  have hAle : A.natDegree ≤ b - 1 := by omega
  have hmul : (b - 1) * (kernelPrefix b A e).natDegree ≤
      (b - 1) * (b ^ e - 1) :=
    hbound.trans (Nat.mul_le_mul_right (b ^ e - 1) hAle)
  have hle : (kernelPrefix b A e).natDegree ≤ b ^ e - 1 :=
    Nat.le_of_mul_le_mul_left hmul (by omega)
  have hpow : 0 < b ^ e := pow_pos (by omega) e
  omega

/-- The first numerator ends strictly before its gap start plus `deg P`. -/
theorem missingDigitFirstNumerator_natDegree_lt
    (b : ℕ) (hb : 2 ≤ b) (A P : Polynomial K)
    (hdegree : A.natDegree < b) {m : ℕ} (hm : 0 < m) (e : ℕ) :
    (missingDigitFirstNumerator b A P e m).natDegree <
      m * b ^ e + P.natDegree := by
  let Q := b ^ e
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hC : (kernelPrefix b A e).natDegree < Q := by
    simpa [Q] using kernelPrefix_natDegree_lt_pow_of_lt b hb A hdegree e
  have hB : (missingDigitPrefix A m).natDegree < m :=
    missingDigitPrefix_natDegree_lt A hm
  have hBle : (missingDigitPrefix A m).natDegree ≤ m - 1 := by omega
  have hsum : (kernelPrefix b A e).natDegree +
      (missingDigitPrefix A m).natDegree * Q < m * Q := by
    calc
      _ ≤ (Q - 1) + (m - 1) * Q :=
        Nat.add_le_add (by omega) (Nat.mul_le_mul_right Q hBle)
      _ < Q + (m - 1) * Q := by omega
      _ = ((m - 1) + 1) * Q := by ring
      _ = m * Q := by rw [Nat.sub_add_cancel (by omega : 1 ≤ m)]
  have hdeg : (missingDigitFirstNumerator b A P e m).natDegree ≤
      P.natDegree + (kernelPrefix b A e).natDegree +
        (missingDigitPrefix A m).natDegree * Q := by
    dsimp [missingDigitFirstNumerator]
    calc
      _ ≤ (P * kernelPrefix b A e).natDegree +
          (Polynomial.expand K Q (missingDigitPrefix A m)).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ (P.natDegree + (kernelPrefix b A e).natDegree) +
          (Polynomial.expand K Q (missingDigitPrefix A m)).natDegree :=
        Nat.add_le_add_right Polynomial.natDegree_mul_le _
      _ = _ := by rw [Polynomial.natDegree_expand]
  dsimp [Q] at hdeg hsum ⊢
  omega

/-- The second numerator ends strictly before its gap start plus `deg P`. -/
theorem missingDigitSecondNumerator_natDegree_lt
    (b : ℕ) (hb : 2 ≤ b) (A P : Polynomial K)
    (hdegree : A.natDegree < b) {m k : ℕ}
    (hm : 0 < m) (hk : 0 < k) (e : ℕ) :
    (missingDigitSecondNumerator b A P e m k).natDegree <
      (k * b + m) * b ^ e + P.natDegree := by
  let Q := b ^ e
  let g := (k * b + m) * Q
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hCnext : (kernelPrefix b A (e + 1)).natDegree < b * Q := by
    have h := kernelPrefix_natDegree_lt_pow_of_lt b hb A hdegree (e + 1)
    simpa [Q, pow_succ, Nat.mul_comm] using h
  have hfirst : (missingDigitFirstNumerator b A P e m).natDegree <
      m * Q + P.natDegree := by
    simpa [Q] using missingDigitFirstNumerator_natDegree_lt b hb A P hdegree hm e
  have hterm0 : (P * kernelPrefix b A (e + 1)).natDegree <
      g + P.natDegree := by
    have hmul := Polynomial.natDegree_mul_le (p := P)
      (q := kernelPrefix b A (e + 1))
    have hbg : b * Q ≤ g := by
      dsimp [g]
      have hb_le : b ≤ k * b + m := by nlinarith
      exact Nat.mul_le_mul_right Q hb_le
    omega
  have hterm1 :
      (Polynomial.monomial (k * b * Q) (A.coeff k) *
        missingDigitFirstNumerator b A P e m).natDegree <
          g + P.natDegree := by
    have hmono := Polynomial.natDegree_monomial_le (A.coeff k)
      (m := k * b * Q)
    have hmul := Polynomial.natDegree_mul_le
      (p := Polynomial.monomial (k * b * Q) (A.coeff k))
      (q := missingDigitFirstNumerator b A P e m)
    have hshift : k * b * Q + (m * Q + P.natDegree) =
        g + P.natDegree := by dsimp [g]; ring
    omega
  have hadd := Polynomial.natDegree_add_le
    (P * kernelPrefix b A (e + 1))
    (Polynomial.monomial (k * b * Q) (A.coeff k) *
      missingDigitFirstNumerator b A P e m)
  dsimp [missingDigitSecondNumerator]
  dsimp [Q, g] at hterm0 hterm1 ⊢
  exact hadd.trans_lt (max_lt hterm0 hterm1)

/-- Both missing-digit gap endpoints lie below the common later radix
cutoff. -/
theorem missingDigit_gap_endpoints_le
    (b : ℕ) (hb : 2 ≤ b) {m k : ℕ} (hm : m < b) (hkb : k < b)
    (e : ℕ) :
    (m + 1) * b ^ e ≤ b ^ (e + 2) ∧
      (k * b + m + 1) * b ^ e ≤ b ^ (e + 2) := by
  have hm1 : m + 1 ≤ b := by omega
  have hk1 : k + 1 ≤ b := by omega
  constructor
  · calc
      (m + 1) * b ^ e ≤ b * b ^ e := Nat.mul_le_mul_right _ hm1
      _ ≤ b ^ (e + 2) := by
        rw [show e + 2 = (e + 1) + 1 by omega, pow_succ, pow_succ]
        calc
          b * b ^ e = b ^ e * b := by ring
          _ ≤ (b ^ e * b) * b := Nat.le_mul_of_pos_right _ (by omega)
  · calc
      (k * b + m + 1) * b ^ e ≤ (k * b + b) * b ^ e :=
        Nat.mul_le_mul_right _ (Nat.add_le_add_left hm1 (k * b))
      _ = (k + 1) * (b * b ^ e) := by ring
      _ ≤ b * (b * b ^ e) := Nat.mul_le_mul_right _ hk1
      _ = b ^ (e + 2) := by
        rw [show e + 2 = (e + 1) + 1 by omega, pow_succ, pow_succ]
        ring

/-- Divisibility of both two-gap numerators forces absorption at the next
complete kernel prefix. -/
theorem dvd_mul_kernelPrefix_succ_of_dvd_missingDigitNumerators
    (b : ℕ) (A P D : Polynomial K) (e m k : ℕ)
    (hD1 : D ∣ missingDigitFirstNumerator b A P e m)
    (hD2 : D ∣ missingDigitSecondNumerator b A P e m k) :
    D ∣ P * kernelPrefix b A (e + 1) := by
  have hshift : D ∣ Polynomial.monomial (k * b * b ^ e) (A.coeff k) *
      missingDigitFirstNumerator b A P e m := dvd_mul_of_dvd_right hD1 _
  have hsub := dvd_sub hD2 hshift
  convert hsub using 1
  simp [missingDigitSecondNumerator]

/-- The complete two-gap numerator package.  It records exact low-coefficient
agreement, the strict degree bounds needed to start denominator recurrences,
the common later radix cutoff, and the algebraic absorption alternative. -/
theorem missingDigit_twoGap_numerator_data
    (b : ℕ) (hb : 2 ≤ b) (A P : Polynomial K)
    (hA0 : A.coeff 0 = 1) (hdegree : A.natDegree < b)
    {m k : ℕ} (hm : m < b) (hAm : A.coeff m = 0)
    (hk : 0 < k) (hkb : k < b) (hAk : A.coeff k ≠ 0)
    (hprior : ∀ j : ℕ, 0 < j → j < k → A.coeff j = 0)
    (e : ℕ) :
    (∀ n : ℕ, n < m * b ^ e + b ^ e →
      PowerSeries.coeff n ((P : PowerSeries K) * canonicalSeries b A) =
        (missingDigitFirstNumerator b A P e m).coeff n) ∧
    (∀ n : ℕ, n < (k * b + m) * b ^ e + b ^ e →
      PowerSeries.coeff n ((P : PowerSeries K) * canonicalSeries b A) =
        (missingDigitSecondNumerator b A P e m k).coeff n) ∧
    (missingDigitFirstNumerator b A P e m).natDegree <
      m * b ^ e + P.natDegree ∧
    (missingDigitSecondNumerator b A P e m k).natDegree <
      (k * b + m) * b ^ e + P.natDegree ∧
    m * b ^ e + b ^ e ≤ b ^ (e + 2) ∧
    (k * b + m) * b ^ e + b ^ e ≤ b ^ (e + 2) ∧
    A.coeff k ≠ 0 ∧
    ∀ D : Polynomial K,
      D ∣ missingDigitFirstNumerator b A P e m →
      D ∣ missingDigitSecondNumerator b A P e m k →
      D ∣ P * kernelPrefix b A (e + 1) := by
  have hmpos : 0 < m := by
    by_contra hmzero
    have : m = 0 := Nat.eq_zero_of_not_pos hmzero
    subst m
    simp [hA0] at hAm
  have hends := missingDigit_gap_endpoints_le b hb hm hkb e
  refine ⟨?_, ?_,
    missingDigitFirstNumerator_natDegree_lt b hb A P hdegree hmpos e,
    missingDigitSecondNumerator_natDegree_lt b hb A P hdegree hmpos hk e,
    ?_, ?_, hAk, ?_⟩
  · intro n hn
    apply coeff_missingDigitFirstNumerator b hb A P hA0 hdegree m e n hm hAm
    have heq : m * b ^ e + b ^ e = (m + 1) * b ^ e := by ring
    rwa [← heq]
  · intro n hn
    apply coeff_missingDigitSecondNumerator b hb A P hA0 hdegree
      m k e n hm hAm hk hkb hprior
    have heq : (k * b + m) * b ^ e + b ^ e =
        (k * b + m + 1) * b ^ e := by ring
    rwa [← heq]
  · have heq : m * b ^ e + b ^ e = (m + 1) * b ^ e := by ring
    rw [heq]
    exact hends.1
  · have heq : (k * b + m) * b ^ e + b ^ e =
        (k * b + m + 1) * b ^ e := by ring
    rw [heq]
    exact hends.2
  · intro D hD1 hD2
    exact dvd_mul_kernelPrefix_succ_of_dvd_missingDigitNumerators
      b A P D e m k hD1 hD2

end IndependentZeroBlocks
