import SierpinskiFormal.PowerSupportFamilies

set_option autoImplicit false

namespace IndependentZeroBlocks

/-- At every sufficiently large scale and every location, a predicate has a
subinterval of uniformly positive relative length on which it does not hold. -/
def HasUniformRelativeHoles (bad : ℕ → Prop) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ L0 : ℕ, ∀ a L : ℕ, L0 ≤ L →
    ∃ n M : ℕ, a ≤ n ∧ n + M ≤ a + L ∧
      c * (L : ℝ) ≤ (M : ℝ) ∧
      ∀ j : ℕ, j < M → ¬bad (n + j)

/-- The empty predicate has uniform relative holes. -/
theorem HasUniformRelativeHoles.empty :
    HasUniformRelativeHoles (fun _ : ℕ => False) := by
  refine ⟨1, by norm_num, 0, ?_⟩
  intro a L _
  refine ⟨a, L, le_rfl, by omega, ?_, ?_⟩
  · norm_num
  · simp

/-- Passing to a smaller exceptional predicate preserves uniform relative holes. -/
theorem HasUniformRelativeHoles.mono
    {bad₁ bad₂ : ℕ → Prop} (hbad₂ : HasUniformRelativeHoles bad₂)
    (hsub : ∀ n : ℕ, bad₁ n → bad₂ n) :
    HasUniformRelativeHoles bad₁ := by
  obtain ⟨c, hc, L0, hholes⟩ := hbad₂
  refine ⟨c, hc, L0, ?_⟩
  intro a L hL
  obtain ⟨n, M, hn, hend, hsize, hclean⟩ := hholes a L hL
  exact ⟨n, M, hn, hend, hsize, fun j hj hbad => hclean j hj (hsub _ hbad)⟩

/-- A union of two predicates with uniform relative holes again has uniform
relative holes.  The second hole is chosen inside the first one. -/
theorem HasUniformRelativeHoles.union
    {bad₁ bad₂ : ℕ → Prop} (hbad₁ : HasUniformRelativeHoles bad₁)
    (hbad₂ : HasUniformRelativeHoles bad₂) :
    HasUniformRelativeHoles (fun n => bad₁ n ∨ bad₂ n) := by
  obtain ⟨c₁, hc₁, L01, hholes₁⟩ := hbad₁
  obtain ⟨c₂, hc₂, L02, hholes₂⟩ := hbad₂
  obtain ⟨K, hK⟩ : ∃ K : ℕ, (L02 : ℝ) / c₁ < K := exists_nat_gt _
  refine ⟨c₂ * c₁, mul_pos hc₂ hc₁, max L01 K, ?_⟩
  intro a L hL
  have hL01 : L01 ≤ L := (le_max_left L01 K).trans hL
  have hKL : K ≤ L := (le_max_right L01 K).trans hL
  obtain ⟨n₁, M₁, hn₁, hend₁, hsize₁, hclean₁⟩ := hholes₁ a L hL01
  have hL02M₁ : L02 ≤ M₁ := by
    have hKLreal : (K : ℝ) ≤ (L : ℝ) := by exact_mod_cast hKL
    have hdiv : (L02 : ℝ) / c₁ < (L : ℝ) := hK.trans_le hKLreal
    have hstrict : (L02 : ℝ) < c₁ * (L : ℝ) := by
      have := (div_lt_iff₀ hc₁).mp hdiv
      nlinarith
    exact_mod_cast hstrict.le.trans hsize₁
  obtain ⟨n₂, M₂, hn₂, hend₂, hsize₂, hclean₂⟩ :=
    hholes₂ n₁ M₁ hL02M₁
  refine ⟨n₂, M₂, hn₁.trans hn₂, hend₂.trans hend₁, ?_, ?_⟩
  · calc
      (c₂ * c₁) * (L : ℝ) = c₂ * (c₁ * (L : ℝ)) := by ring
      _ ≤ c₂ * (M₁ : ℝ) := mul_le_mul_of_nonneg_left hsize₁ hc₂.le
      _ ≤ (M₂ : ℝ) := hsize₂
  · intro j hj hbad
    rcases hbad with hbad₁point | hbad₂point
    · have hn₁point : n₁ ≤ n₂ + j := hn₂.trans (Nat.le_add_right n₂ j)
      have hpoint_end : n₂ + j < n₁ + M₁ := by omega
      have hoff : n₂ + j - n₁ < M₁ := by omega
      have hrepr : n₁ + (n₂ + j - n₁) = n₂ + j :=
        Nat.add_sub_of_le hn₁point
      exact hclean₁ (n₂ + j - n₁) hoff (by simpa [hrepr] using hbad₁point)
    · exact hclean₂ j hj hbad₂point

/-- A finite union indexed by a finset has uniform relative holes. -/
theorem HasUniformRelativeHoles.finset_union
    {ι : Type*} [DecidableEq ι] (bad : ι → ℕ → Prop) (t : Finset ι)
    (hbad : ∀ i ∈ t, HasUniformRelativeHoles (bad i)) :
    HasUniformRelativeHoles (fun n => ∃ i ∈ t, bad i n) := by
  induction t using Finset.induction_on with
  | empty =>
      simpa using HasUniformRelativeHoles.empty
  | @insert i t hi ih =>
      have hi_holes : HasUniformRelativeHoles (bad i) := hbad i (Finset.mem_insert_self i t)
      have ht_holes : HasUniformRelativeHoles (fun n => ∃ k ∈ t, bad k n) := by
        apply ih
        intro k hk
        exact hbad k (Finset.mem_insert_of_mem hk)
      apply (hi_holes.union ht_holes).mono
      intro n hn
      obtain ⟨k, hk, hkn⟩ := hn
      rcases Finset.mem_insert.mp hk with hki | hkt
      · exact Or.inl (by simpa [hki] using hkn)
      · exact Or.inr ⟨k, hkt, hkn⟩

/-- Uniform relative holes are closed under unions over a finite type. -/
theorem HasUniformRelativeHoles.finite_union
    {ι : Type*} [Fintype ι] (bad : ι → ℕ → Prop)
    (hbad : ∀ i, HasUniformRelativeHoles (bad i)) :
    HasUniformRelativeHoles (fun n => ∃ i, bad i n) := by
  classical
  apply (HasUniformRelativeHoles.finset_union bad Finset.univ
    (fun i _ => hbad i)).mono
  intro n hn
  obtain ⟨i, hi⟩ := hn
  exact ⟨i, Finset.mem_univ i, hi⟩

/-- Translating a predicate to the right preserves uniform relative holes. -/
theorem HasUniformRelativeHoles.shift
    {bad : ℕ → Prop} (hbad : HasUniformRelativeHoles bad) (h : ℕ) :
    HasUniformRelativeHoles (fun n => ∃ k : ℕ, bad k ∧ n = h + k) := by
  obtain ⟨c, hc, L0, hholes⟩ := hbad
  let e : ℝ := min c 1 / 2
  have he : 0 < e := by
    dsimp [e]
    exact div_pos (lt_min hc (by norm_num)) (by norm_num)
  have hec : e ≤ c := by
    have hminc : min c 1 ≤ c := min_le_left c 1
    dsimp [e]
    nlinarith [hc]
  have hehalf : e ≤ (1 : ℝ) / 2 := by
    have hminone : min c 1 ≤ 1 := min_le_right c 1
    dsimp [e]
    linarith
  refine ⟨e, he, 2 * L0, ?_⟩
  intro a L hL
  have hL0 : L0 ≤ L := by omega
  by_cases ha : h ≤ a
  · obtain ⟨n, M, hn, hend, hsize, hclean⟩ := hholes (a - h) L hL0
    refine ⟨h + n, M, by omega, by omega, ?_, ?_⟩
    · have hLnonneg : (0 : ℝ) ≤ (L : ℝ) := by positivity
      exact hsize.trans' (mul_le_mul_of_nonneg_right hec hLnonneg)
    · intro j hj himage
      obtain ⟨k, hkbad, heq⟩ := himage
      have hk : k = n + j := by omega
      exact hclean j hj (by simpa [hk] using hkbad)
  · have hah : a < h := Nat.lt_of_not_ge ha
    by_cases hbefore : a + L ≤ h
    · refine ⟨a, L, le_rfl, by omega, ?_, ?_⟩
      · have heone : e ≤ 1 := hehalf.trans (by norm_num)
        have hLnonneg : (0 : ℝ) ≤ (L : ℝ) := by positivity
        simpa using mul_le_mul_of_nonneg_right heone hLnonneg
      · intro j hj himage
        obtain ⟨k, _, heq⟩ := himage
        omega
    · have hcross : h < a + L := Nat.lt_of_not_ge hbefore
      let T := a + L - h
      have hTpos : 0 < T := by dsimp [T]; omega
      by_cases hsuffix : L ≤ 2 * T
      · have hL0T : L0 ≤ T := by omega
        obtain ⟨n, M, hn, hend, hsize, hclean⟩ := hholes 0 T hL0T
        refine ⟨h + n, M, by omega, by dsimp [T] at hend ⊢; omega, ?_, ?_⟩
        · have hecHalf : e ≤ c / 2 := by
            have hminc : min c 1 ≤ c := min_le_left c 1
            dsimp [e]
            linarith
          have hLreal : (L : ℝ) ≤ 2 * (T : ℝ) := by exact_mod_cast hsuffix
          have hTnonneg : (0 : ℝ) ≤ (T : ℝ) := by positivity
          have hcT : e * (L : ℝ) ≤ c * (T : ℝ) := by
            nlinarith [mul_nonneg (sub_nonneg.mpr hecHalf) hTnonneg]
          exact hcT.trans hsize
        · intro j hj himage
          obtain ⟨k, hkbad, heq⟩ := himage
          have hk : k = n + j := by omega
          exact hclean j hj (by simpa [hk] using hkbad)
      · have hprefix : L ≤ 2 * (h - a) := by
          dsimp [T] at hsuffix
          omega
        refine ⟨a, h - a, le_rfl, by omega, ?_, ?_⟩
        · have hprefixReal : (L : ℝ) ≤ 2 * ((h - a : ℕ) : ℝ) := by
            exact_mod_cast hprefix
          have hLnonneg : (0 : ℝ) ≤ (L : ℝ) := by positivity
          nlinarith [mul_nonneg (sub_nonneg.mpr hehalf) hLnonneg]
        · intro j hj himage
          obtain ⟨k, _, heq⟩ := himage
          omega

/-- Multiplying all indices by a positive natural number preserves uniform
relative holes. -/
theorem HasUniformRelativeHoles.dilate
    {bad : ℕ → Prop} (hbad : HasUniformRelativeHoles bad)
    {q : ℕ} (hq : 0 < q) :
    HasUniformRelativeHoles (fun n => ∃ k : ℕ, bad k ∧ n = q * k) := by
  obtain ⟨c, hc, L0, hholes⟩ := hbad
  let D := 2 * q
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨c / 4, by positivity, max (4 * q) (D * L0), ?_⟩
  intro a L hL
  have hfourq : 4 * q ≤ L := (le_max_left (4 * q) (D * L0)).trans hL
  have hDL0 : D * L0 ≤ L := (le_max_right (4 * q) (D * L0)).trans hL
  let A := a / q + 1
  let K := L / D
  have hL0K : L0 ≤ K := by
    dsimp [K]
    apply (Nat.le_div_iff_mul_le hD).mpr
    simpa [Nat.mul_comm] using hDL0
  have hKtwo : 2 ≤ K := by
    dsimp [K]
    apply (Nat.le_div_iff_mul_le hD).mpr
    calc
      2 * D = 4 * q := by dsimp [D]; ring
      _ ≤ L := hfourq
  have hL_le : L ≤ 4 * q * K := by
    have hLlt : L < D * (K + 1) := by
      have ht : L < (K + 1) * D := by
        apply (Nat.div_lt_iff_lt_mul hD).mp
        dsimp [K]
        exact Nat.lt_succ_self _
      simpa [Nat.mul_comm] using ht
    have hDone : D ≤ D * K := by
      simpa using Nat.mul_le_mul_left D (show 1 ≤ K by omega)
    have hnext : D * (K + 1) ≤ 2 * D * K := by
      rw [Nat.mul_add, Nat.mul_one]
      nlinarith
    calc
      L ≤ 2 * D * K := hLlt.le.trans hnext
      _ = 4 * q * K := by dsimp [D]; ring
  have hAstart : a ≤ q * A := by
    have ha_lt : a < q * (a / q + 1) := by
      simpa [Nat.mul_comm] using
        (Nat.div_lt_iff_lt_mul hq).mp (Nat.lt_succ_self (a / q))
    simpa [A] using ha_lt.le
  have hAKend : q * (A + K) ≤ a + L := by
    have hqA : q * A ≤ a + q := by
      have hdivmul : q * (a / q) ≤ a := by
        simpa [Nat.mul_comm] using Nat.div_mul_le_self a q
      dsimp [A]
      rw [Nat.mul_add, Nat.mul_one]
      omega
    have hDK : D * K ≤ L := by
      dsimp [K]
      simpa [Nat.mul_comm] using Nat.div_mul_le_self L D
    have hqK : q + q * K ≤ L := by
      dsimp [D] at hDK
      nlinarith [hfourq]
    rw [Nat.mul_add]
    omega
  obtain ⟨n, M, hn, hend, hsize, hclean⟩ := hholes A K hL0K
  refine ⟨q * n, q * M, hAstart.trans (Nat.mul_le_mul_left q hn), ?_, ?_, ?_⟩
  · calc
      q * n + q * M = q * (n + M) := by ring
      _ ≤ q * (A + K) := Nat.mul_le_mul_left q hend
      _ ≤ a + L := hAKend
  · have hLreal : (0 : ℝ) ≤ (L : ℝ) := by positivity
    have hL_le_real : (L : ℝ) ≤ 4 * (q : ℝ) * (K : ℝ) := by
      exact_mod_cast hL_le
    calc
      (c / 4) * (L : ℝ) ≤ (c / 4) * (4 * (q : ℝ) * (K : ℝ)) :=
        mul_le_mul_of_nonneg_left hL_le_real (by positivity)
      _ = (q : ℝ) * (c * (K : ℝ)) := by ring
      _ ≤ (q : ℝ) * (M : ℝ) :=
        mul_le_mul_of_nonneg_left hsize (by positivity)
      _ = (q * M : ℕ) := by norm_num
  · intro j hj himage
    obtain ⟨k, hkbad, heq⟩ := himage
    have hnk : n ≤ k := by
      have hmul : q * n ≤ q * k := by omega
      exact Nat.le_of_mul_le_mul_left hmul hq
    have hk_end : k < n + M := by
      have hmul : q * k < q * (n + M) := by
        rw [← heq, Nat.mul_add]
        omega
      exact (Nat.mul_lt_mul_left hq).mp hmul
    have hoff : k - n < M := by omega
    have hrepr : n + (k - n) = k := Nat.add_sub_of_le hnk
    exact hclean (k - n) hoff (by simpa [hrepr] using hkbad)

/-- Positive affine images of a predicate preserve uniform relative holes. -/
theorem HasUniformRelativeHoles.affineImage
    {bad : ℕ → Prop} (hbad : HasUniformRelativeHoles bad)
    (h q : ℕ) (hq : 0 < q) :
    HasUniformRelativeHoles
      (fun n => ∃ k : ℕ, bad k ∧ n = h + q * k) := by
  apply ((hbad.dilate hq).shift h).mono
  intro n hn
  obtain ⟨k, hkbad, heq⟩ := hn
  exact ⟨q * k, ⟨k, hkbad, rfl⟩, heq⟩

/-- Snake-case alias for positive affine-image closure. -/
theorem HasUniformRelativeHoles.affine_image
    {bad : ℕ → Prop} (hbad : HasUniformRelativeHoles bad)
    (h q : ℕ) (hq : 0 < q) :
    HasUniformRelativeHoles
      (fun n => ∃ k : ℕ, bad k ∧ n = h + q * k) :=
  hbad.affineImage h q hq

/-- Removing a predicate with uniform relative holes preserves every positive
power-interval exponent. -/
theorem HasPowerIntervals.avoid_uniformRelativeHoles
    {ρ : ℝ} {Z bad : ℕ → Prop} (hZ : HasPowerIntervals ρ Z)
    (hρ : 0 < ρ) (hbad : HasUniformRelativeHoles bad) :
    HasPowerIntervals ρ (fun n => Z n ∧ ¬bad n) := by
  obtain ⟨d, hd, hinterval⟩ := hZ
  obtain ⟨c, hc, L0, hholes⟩ := hbad
  obtain ⟨R, hR⟩ := exists_nat_rpow_gt ((L0 : ℝ) / d) ρ hρ
  refine ⟨c * d, mul_pos hc hd, ?_⟩
  intro start
  obtain ⟨a, L, ha, hLpos, hpower, hgood⟩ := hinterval (max start R)
  have hstarta : start ≤ a := (le_max_left start R).trans ha
  have hRa : R ≤ a := (le_max_right start R).trans ha
  have hRend : R ≤ a + L := hRa.trans (Nat.le_add_right a L)
  have hL0L : L0 ≤ L := by
    have hRendReal : (R : ℝ) ≤ ((a + L : ℕ) : ℝ) := by exact_mod_cast hRend
    have hlarge : (L0 : ℝ) / d < ((a + L : ℕ) : ℝ) ^ ρ :=
      hR.trans_le (Real.rpow_le_rpow (by positivity) hRendReal hρ.le)
    have hstrict : (L0 : ℝ) < d * ((a + L : ℕ) : ℝ) ^ ρ := by
      have := (div_lt_iff₀ hd).mp hlarge
      nlinarith
    exact_mod_cast hstrict.le.trans hpower
  obtain ⟨n, M, hn, hend, hrelative, hclean⟩ := hholes a L hL0L
  have hMpos : 0 < M := by
    have hLreal : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hLpos
    have hMreal : (0 : ℝ) < (M : ℝ) :=
      (mul_pos hc hLreal).trans_le hrelative
    exact_mod_cast hMreal
  have hendpointReal : ((n + M : ℕ) : ℝ) ≤ ((a + L : ℕ) : ℝ) := by
    exact_mod_cast hend
  have hrpow : ((n + M : ℕ) : ℝ) ^ ρ ≤ ((a + L : ℕ) : ℝ) ^ ρ :=
    Real.rpow_le_rpow (by positivity) hendpointReal hρ.le
  refine ⟨n, M, hstarta.trans hn, hMpos, ?_, ?_⟩
  · calc
      (c * d) * ((n + M : ℕ) : ℝ) ^ ρ ≤
          (c * d) * ((a + L : ℕ) : ℝ) ^ ρ :=
        mul_le_mul_of_nonneg_left hrpow (mul_pos hc hd).le
      _ = c * (d * ((a + L : ℕ) : ℝ) ^ ρ) := by ring
      _ ≤ c * (L : ℝ) := mul_le_mul_of_nonneg_left hpower hc.le
      _ ≤ (M : ℝ) := hrelative
  · intro j hj
    have hapoint : a ≤ n + j := hn.trans (Nat.le_add_right n j)
    have hpointEnd : n + j < a + L := by omega
    have hoff : n + j - a < L := by omega
    have hrepr : a + (n + j - a) = n + j := Nat.add_sub_of_le hapoint
    constructor
    · simpa [hrepr] using hgood (n + j - a) hoff
    · exact hclean j hj

/-- Removing a predicate with uniform relative holes preserves proportional
intervals. -/
theorem HasProportionalIntervals.avoid_uniformRelativeHoles
    {Z bad : ℕ → Prop} (hZ : HasProportionalIntervals Z)
    (hbad : HasUniformRelativeHoles bad) :
    HasProportionalIntervals (fun n => Z n ∧ ¬bad n) := by
  rw [← hasPowerIntervals_one_iff] at hZ ⊢
  exact hZ.avoid_uniformRelativeHoles (by norm_num) hbad

end IndependentZeroBlocks
