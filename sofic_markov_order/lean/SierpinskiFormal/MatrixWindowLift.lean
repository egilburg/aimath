import SierpinskiFormal.DilationWindowThreshold

set_option autoImplicit false

/-!
# Backward-window digit lift for polynomial matrix dilation systems
-/

namespace IndependentZeroBlocks

open scoped BigOperators
open SierpinskiFormal

/-- The trailing coefficient window, padded by zero before index zero. -/
noncomputable def matrixWindowState
    {K ι : Type*} [CommRing K]
    (U : ι → PowerSeries K) (m n : ℕ) : ι × Fin m → K :=
  fun p => if p.2.1 ≤ n then PowerSeries.coeff (n - p.2.1) (U p.1) else 0

@[simp] theorem matrixWindowState_apply_of_le
    {K ι : Type*} [CommRing K]
    (U : ι → PowerSeries K) (m n : ℕ) (p : ι × Fin m)
    (h : p.2.1 ≤ n) :
    matrixWindowState U m n p = PowerSeries.coeff (n - p.2.1) (U p.1) := by
  simp [matrixWindowState, h]

@[simp] theorem matrixWindowState_apply_of_lt
    {K ι : Type*} [CommRing K]
    (U : ι → PowerSeries K) (m n : ℕ) (p : ι × Fin m)
    (h : n < p.2.1) :
    matrixWindowState U m n p = 0 := by
  simp [matrixWindowState, Nat.not_le.mpr h]

/-- One polynomial-times-dilation coefficient, expressed through a bounded
trailing window.  This is the scalar reindexing at the heart of the lift. -/
theorem coeff_polynomial_mul_dilate_eq_window
    {K : Type*} [CommRing K]
    (P : Polynomial K) (V : PowerSeries K)
    (b m n r t : ℕ) (hb : 2 ≤ b) (ht : t < m)
    (hdegree : P.natDegree ≤ (b - 1) * m) (hr : r < b) :
    (if t ≤ b * n + r then
        PowerSeries.coeff (b * n + r - t) ((P : PowerSeries K) * dilate b V)
      else 0) =
      ∑ s : Fin m,
        (if t ≤ r + b * s.1 then P.coeff (r + b * s.1 - t) else 0) *
          (if s.1 ≤ n then PowerSeries.coeff (n - s.1) V else 0) := by
  classical
  by_cases htarget : t ≤ b * n + r
  · rw [if_pos htarget, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    let N := b * n + r - t
    let A : Finset ℕ := (Finset.range (N + 1)).filter fun a =>
      b ∣ N - a ∧ a ≤ P.natDegree
    let S : Finset (Fin m) := Finset.univ.filter fun s =>
      s.1 ≤ n ∧ t ≤ r + b * s.1 ∧ r + b * s.1 - t ≤ P.natDegree
    have hleft :
        (∑ a ∈ Finset.range (N + 1),
          P.coeff a * PowerSeries.coeff (N - a) (dilate b V)) =
        ∑ a ∈ A, P.coeff a * PowerSeries.coeff ((N - a) / b) V := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hd : b ∣ N - a
      · by_cases haD : a ≤ P.natDegree
        · simp [hd, haD, coeff_dilate]
        · have hcoeff : P.coeff a = 0 :=
            Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
          simp [hd, haD, hcoeff, coeff_dilate]
      · simp [hd, coeff_dilate]
    simp only [Prod.fst, Prod.snd, Polynomial.coeff_coe]
    rw [show b * n + r - t = N by rfl, hleft]
    have hright :
        (∑ s : Fin m,
          (if t ≤ r + b * s.1 then P.coeff (r + b * s.1 - t) else 0) *
            (if s.1 ≤ n then PowerSeries.coeff (n - s.1) V else 0)) =
        ∑ s ∈ S, P.coeff (r + b * s.1 - t) *
          PowerSeries.coeff (n - s.1) V := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro s hs
      by_cases hsn : s.1 ≤ n
      · by_cases hts : t ≤ r + b * s.1
        · by_cases hsD : r + b * s.1 - t ≤ P.natDegree
          · simp [hsn, hts, hsD]
          · have hcoeff : P.coeff (r + b * s.1 - t) = 0 :=
              Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
            simp [hsn, hts, hsD, hcoeff]
        · simp [hts]
      · simp [hsn]
    rw [hright]
    have hNadd : N + t = b * n + r := by
      dsimp [N]
      exact Nat.sub_add_cancel htarget
    have hq_props (a : ℕ) (ha : a ∈ A) :
        let q := (N - a) / b
        q ≤ n ∧ n < q + m ∧ a + t = r + b * (n - q) := by
      have haA := Finset.mem_filter.mp ha
      have haN : a ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp haA.1)
      have hdiv : b ∣ N - a := haA.2.1
      have haD : a ≤ (b - 1) * m := le_trans haA.2.2 hdegree
      let q := (N - a) / b
      have habEq : b * q = N - a := Nat.mul_div_cancel' hdiv
      have hNa : (N - a) + a = N := Nat.sub_add_cancel haN
      have hbalance : b * q + a + t = b * n + r := by omega
      have htm : t + a < b * m := by
        have hbm : (b - 1) * m + m = b * m := by
          calc
            (b - 1) * m + m = ((b - 1) + 1) * m := by
              rw [Nat.add_mul, one_mul]
            _ = b * m := by rw [Nat.sub_add_cancel (by omega)]
        omega
      have hqle : q ≤ n := by
        by_contra hnot
        have hmul := Nat.mul_le_mul_left b (show n + 1 ≤ q by omega)
        have hchildlt : b * n + r < b * (n + 1) := by
          rw [Nat.mul_add, mul_one]
          omega
        omega
      have hqlow : n < q + m := by
        by_contra hnot
        have hmul := Nat.mul_le_mul_left b (show q + m ≤ n by omega)
        rw [Nat.mul_add] at hmul
        omega
      have hbn : b * q + b * (n - q) = b * n := by
        rw [← Nat.mul_add, Nat.add_sub_of_le hqle]
      have hindex : a + t = r + b * (n - q) := by omega
      exact ⟨hqle, hqlow, hindex⟩
    apply Finset.sum_bij
        (fun a ha =>
          let q := (N - a) / b
          ⟨n - q, by
            have hp := hq_props a ha
            dsimp [q] at hp
            omega⟩)
    · intro a ha
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      have haA := Finset.mem_filter.mp ha
      let q := (N - a) / b
      have hp := hq_props a ha
      dsimp [q] at hp ⊢
      have hindex : r + b * (n - (N - a) / b) - t = a := by omega
      exact ⟨by simp [q, hp.1], by omega,
        by simpa [q, hindex] using haA.2.2⟩
    · intro a₁ ha₁ a₂ ha₂ heq
      have hval := congrArg Fin.val heq
      have haA₁ := Finset.mem_filter.mp ha₁
      have haA₂ := Finset.mem_filter.mp ha₂
      have haN₁ : a₁ ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp haA₁.1)
      have haN₂ : a₂ ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp haA₂.1)
      have hd₁ : b ∣ N - a₁ := haA₁.2.1
      have hd₂ : b ∣ N - a₂ := haA₂.2.1
      have hq₁ := (hq_props a₁ ha₁).1
      have hq₂ := (hq_props a₂ ha₂).1
      change n - (N - a₁) / b = n - (N - a₂) / b at hval
      have hqeq : (N - a₁) / b = (N - a₂) / b := by omega
      have he₁ := Nat.mul_div_cancel' hd₁
      have he₂ := Nat.mul_div_cancel' hd₂
      rw [hqeq] at he₁
      omega
    · intro s hs
      have hsS := Finset.mem_filter.mp hs
      let a := r + b * s.1 - t
      have haadd : a + t = r + b * s.1 := by
        dsimp [a]
        exact Nat.sub_add_cancel hsS.2.2.1
      have hbn : b * s.1 + b * (n - s.1) = b * n := by
        rw [← Nat.mul_add, Nat.add_sub_of_le hsS.2.1]
      have haN : a ≤ N := by omega
      have hdiff : N - a = b * (n - s.1) := by omega
      have haA : a ∈ A := by
        simp only [A, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, by rw [hdiff]; exact dvd_mul_right b _, hsS.2.2.2⟩
      refine ⟨a, haA, ?_⟩
      apply Fin.ext
      change n - (N - a) / b = s.1
      have hquot : (N - a) / b = n - s.1 := by
        rw [hdiff]
        exact Nat.mul_div_cancel_left _ (by omega)
      rw [hquot]
      exact Nat.sub_sub_self hsS.2.1
    · intro a ha
      let q := (N - a) / b
      have hp := hq_props a ha
      dsimp [q] at hp ⊢
      have hindex : r + b * (n - (N - a) / b) - t = a := by omega
      simp [q, hp.1, hindex, Nat.sub_sub_self hp.1]
  · rw [if_neg htarget]
    symm
    apply Finset.sum_eq_zero
    intro s hs
    by_cases hts : t ≤ r + b * s.1
    · have hsn : n < s.1 := lt_of_not_ge fun hsle => by
        have hmul := Nat.mul_le_mul_left b hsle
        have hle : r + b * s.1 ≤ b * n + r := by
          simpa [Nat.add_comm] using Nat.add_le_add_left hmul r
        have hchildlt : b * n + r < t := Nat.lt_of_not_ge htarget
        exact (not_lt_of_ge (le_trans hts hle)) hchildlt
      simp [hts, matrixWindowState, Nat.not_le.mpr hsn]
    · simp [hts]

/-- The explicit digit transition on trailing coefficient windows. -/
noncomputable def matrixWindowTransition
    {K ι : Type*} [CommRing K]
    (B : ι → ι → Polynomial K) (b m r : ℕ) :
    (ι × Fin m) → (ι × Fin m) → K :=
  fun p q =>
    if p.2.1 ≤ r + b * q.2.1 then
      (B p.1 q.1).coeff (r + b * q.2.1 - p.2.1)
    else 0

/-- A polynomial matrix dilation system of degree at most `(b-1)*m`
induces the explicit radix-digit recurrence on its trailing windows. -/
theorem matrixWindowState_digit_recurrence
    {K ι : Type*} [CommRing K] [Fintype ι]
    (B : ι → ι → Polynomial K) (U : ι → PowerSeries K)
    (b m : ℕ) (hb : 2 ≤ b) (_hm : 1 ≤ m)
    (hdegree : ∀ i j, (B i j).natDegree ≤ (b - 1) * m)
    (hEq : ∀ i, U i = ∑ j,
      (B i j : PowerSeries K) * dilate b (U j)) :
    ∀ n r, r < b → ∀ p,
      matrixWindowState U m (b * n + r) p =
        ∑ q, matrixWindowTransition B b m r p q * matrixWindowState U m n q := by
  classical
  intro n r hr p
  rcases p with ⟨i, t⟩
  have ht : t.1 < m := t.2
  change (if t.1 ≤ b * n + r then
      PowerSeries.coeff (b * n + r - t.1) (U i) else 0) = _
  calc
    (if t.1 ≤ b * n + r then
        PowerSeries.coeff (b * n + r - t.1) (U i) else 0) =
        ∑ j, (if t.1 ≤ b * n + r then
          PowerSeries.coeff (b * n + r - t.1)
            ((B i j : PowerSeries K) * dilate b (U j)) else 0) := by
      by_cases htarget : t.1 ≤ b * n + r
      · simp only [if_pos htarget]
        rw [hEq i, map_sum]
      · simp [htarget]
    _ = ∑ j, ∑ s : Fin m,
        (if t.1 ≤ r + b * s.1 then
            (B i j).coeff (r + b * s.1 - t.1) else 0) *
          (if s.1 ≤ n then PowerSeries.coeff (n - s.1) (U j) else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact coeff_polynomial_mul_dilate_eq_window
        (B i j) (U j) b m n r t.1 hb ht (hdegree i j) hr
    _ = ∑ q : ι × Fin m,
        matrixWindowTransition B b m r (i, t) q * matrixWindowState U m n q := by
      rw [Fintype.sum_prod_type]
      rfl

/-- Every finite polynomial matrix dilation system admits a digit recurrence
at its automatic (least degree-controlled positive) window threshold. -/
theorem polynomialDilationMatrix_exists_windowDigitRecurrence
    {K ι : Type*} [CommRing K] [Fintype ι]
    (B : ι → ι → Polynomial K) (U : ι → PowerSeries K)
    (b : ℕ) (hb : 2 ≤ b)
    (hEq : ∀ i, U i = ∑ j,
      (B i j : PowerSeries K) * dilate b (U j)) :
    let m := polynomialDilationWindowThreshold B b
    ∃ M : ℕ → (ι × Fin m) → (ι × Fin m) → K,
      ∀ n r, r < b → ∀ p,
        matrixWindowState U m (b * n + r) p =
          ∑ q, M r p q * matrixWindowState U m n q := by
  classical
  dsimp only
  refine ⟨matrixWindowTransition B b
    (polynomialDilationWindowThreshold B b), ?_⟩
  apply matrixWindowState_digit_recurrence B U b
    (polynomialDilationWindowThreshold B b) hb
    (polynomialDilationWindowThreshold_pos B b)
  · intro i j
    exact le_trans (entry_natDegree_le_polynomialDilationMatrixDegree B i j)
      (polynomialDilationMatrixDegree_le_threshold_mul B b hb)
  · exact hEq

end IndependentZeroBlocks

#print axioms IndependentZeroBlocks.coeff_polynomial_mul_dilate_eq_window
#print axioms IndependentZeroBlocks.matrixWindowState_digit_recurrence
#print axioms IndependentZeroBlocks.polynomialDilationMatrix_exists_windowDigitRecurrence
