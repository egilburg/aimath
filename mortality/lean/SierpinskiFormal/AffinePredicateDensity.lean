import SierpinskiFormal.FiniteWindowSupport

set_option autoImplicit false
namespace IndependentZeroBlocks
open Filter
open scoped Topology BigOperators

/-- Injecting an affine preimage into its ambient prefix bounds its count. -/
theorem predicateCount_affine_preimage_le
    (bad : ℕ → Prop) (q r N : ℕ) (hq : 0 < q) :
    predicateCount (fun n => bad (q * n + r)) N ≤ predicateCount bad (q * N + r) := by
  classical
  unfold predicateCount
  apply Finset.card_le_card_of_injOn (fun n => q * n + r)
  · intro n hn
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hn ⊢
    exact ⟨Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_left hn.1 hq) r, hn.2⟩
  · intro n hn m hm heq
    exact Nat.eq_of_mul_eq_mul_left hq (Nat.add_right_cancel heq)

/-- A fixed affine enlargement and finite multiplicity preserve density zero. -/
theorem zeroPredicateDensity_of_affine_count_bound
    (small big : ℕ → Prop) (c q r : ℕ) (hq : 0 < q)
    (hcount : ∀ N, predicateCount small N ≤ c * predicateCount big (q * N + r))
    (hz : HasZeroPredicateDensity big) : HasZeroPredicateDensity small := by
  have hcofinal : Tendsto (fun N : ℕ => q * N + r) atTop atTop := by
    apply tendsto_atTop_mono (fun N => ?_) tendsto_id
    calc
      N ≤ q * N := by nlinarith
      _ ≤ q * N + r := Nat.le_add_right _ _
  have hupper : Tendsto (fun N : ℕ =>
      (c * (q + r + 1) : ℕ) *
        ((predicateCount big (q * N + r) : ℝ) / (q * N + r : ℕ))) atTop (𝓝 0) := by
    simpa using (hz.comp hcofinal).const_mul ((c * (q + r + 1) : ℕ) : ℝ)
  apply squeeze_zero'
  · filter_upwards with N
    positivity
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hNp : (0 : ℝ) < N := by positivity
    have hMp : (0 : ℝ) < (q * N + r : ℕ) := by positivity
    have hc : (predicateCount small N : ℝ) ≤
        (c : ℝ) * predicateCount big (q * N + r) := by exact_mod_cast hcount N
    have hM : ((q * N + r : ℕ) : ℝ) ≤ (q + r + 1 : ℕ) * (N : ℝ) := by
      exact_mod_cast (show q * N + r ≤ (q + r + 1) * N by nlinarith)
    rw [div_le_iff₀ hNp]
    calc
      (predicateCount small N : ℝ) ≤ (c : ℝ) * predicateCount big (q * N + r) := hc
      _ ≤ ((c * (q + r + 1) : ℕ) : ℝ) *
          ((predicateCount big (q * N + r) : ℝ) / (q * N + r : ℕ)) * N := by
        rw [show ((c * (q + r + 1) : ℕ) : ℝ) *
            ((predicateCount big (q * N + r) : ℝ) / (q * N + r : ℕ)) * N =
            (((c * (q + r + 1) : ℕ) : ℝ) *
              predicateCount big (q * N + r) * N) / (q * N + r : ℕ) by ring]
        apply (le_div_iff₀ hMp).mpr
        have hh := mul_le_mul_of_nonneg_left hM
          (show 0 ≤ (c : ℝ) * predicateCount big (q * N + r) by positivity)
        push_cast at hh ⊢
        nlinarith [hh]
  · exact hupper

/-- Positive lower density also transfers backwards through a fixed affine
count comparison. -/
theorem positiveLowerPredicateDensity_of_affine_count_bound
    (small big : ℕ → Prop) (c q r : ℕ) (hq : 0 < q)
    (hcount : ∀ N, predicateCount small N ≤ c * predicateCount big (q * N + r))
    (hs : HasPositiveLowerPredicateDensity small) :
    HasPositiveLowerPredicateDensity big := by
  obtain ⟨a, ha, N0, hlow⟩ := hs
  let L := q + r + 1
  have hL : 0 < L := by dsimp [L]; omega
  have hden : (0 : ℝ) < ((c + 1) * (2 * L) : ℕ) := by positivity
  refine ⟨a / ((c + 1) * (2 * L) : ℕ), div_pos ha hden,
    L * (N0 + 1), ?_⟩
  intro N hN
  let n := N / L
  have hn0 : N0 + 1 ≤ n := (Nat.le_div_iff_mul_le hL).mpr (by nlinarith [hN])
  have hn : 1 ≤ n := by omega
  have hLn : L * n ≤ N := by
    simpa [n, Nat.mul_comm] using Nat.div_mul_le_self N L
  have hM : q * n + r ≤ N := by
    have : q * n + r ≤ L * n := by dsimp [L]; nlinarith
    omega
  have hNupper : N ≤ 2 * L * n := by
    have hh : N < (n + 1) * L :=
      (Nat.div_lt_iff_lt_mul hL).mp (by dsimp [n]; omega)
    nlinarith
  have haN : a * (n : ℝ) ≤ (c : ℝ) * predicateCount big N := by
    calc
      a * (n : ℝ) ≤ (predicateCount small n : ℝ) := hlow n (by omega)
      _ ≤ ((c * predicateCount big (q * n + r) : ℕ) : ℝ) := by exact_mod_cast hcount n
      _ ≤ (c : ℝ) * predicateCount big N := by
        exact_mod_cast Nat.mul_le_mul_left c (predicateCount_mono big hM)
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).mpr
  have hh : (N : ℝ) ≤ (2 * L : ℕ) * (n : ℝ) := by exact_mod_cast hNupper
  have hha := mul_le_mul_of_nonneg_left hh ha.le
  have hhb := mul_le_mul_of_nonneg_left haN
    (show (0 : ℝ) ≤ (2 * L : ℕ) by positivity)
  have hp : (0 : ℝ) ≤ predicateCount big N := by positivity
  push_cast at hha hhb ⊢
  nlinarith

/-- A finite family of affine observations has one uniform affine count bound. -/
theorem predicateCount_finite_affine_preimages_le
    {ι : Type*} [Fintype ι] (bad : ℕ → Prop) (q r : ι → ℕ)
    (hq : ∀ i, 0 < q i) (N : ℕ) :
    predicateCount (fun n => ∃ i, bad (q i * n + r i)) N ≤
      Fintype.card ι * predicateCount bad
        ((1 + Finset.univ.sup q) * N + Finset.univ.sup r) := by
  classical
  calc
    predicateCount (fun n => ∃ i, bad (q i * n + r i)) N ≤
        ∑ i, predicateCount (fun n => bad (q i * n + r i)) N :=
      predicateCount_exists_le _ N
    _ ≤ ∑ _i : ι, predicateCount bad
        ((1 + Finset.univ.sup q) * N + Finset.univ.sup r) := by
      apply Finset.sum_le_sum
      intro i hi
      apply (predicateCount_affine_preimage_le bad (q i) (r i) N (hq i)).trans
      apply predicateCount_mono
      have hqi : q i ≤ Finset.univ.sup q := Finset.le_sup (Finset.mem_univ i)
      have hri : r i ≤ Finset.univ.sup r := Finset.le_sup (Finset.mem_univ i)
      nlinarith
    _ = _ := by simp

/-- Density zero survives every finite family of fixed affine preimages. -/
theorem HasZeroPredicateDensity.finite_affine_preimages
    {ι : Type*} [Fintype ι] {bad : ℕ → Prop}
    (hz : HasZeroPredicateDensity bad) (q r : ι → ℕ) (hq : ∀ i, 0 < q i) :
    HasZeroPredicateDensity (fun n => ∃ i, bad (q i * n + r i)) := by
  classical
  exact zeroPredicateDensity_of_affine_count_bound _ bad (Fintype.card ι)
    (1 + Finset.univ.sup q) (Finset.univ.sup r) (by omega)
    (predicateCount_finite_affine_preimages_le bad q r hq) hz

/-- Positive lower density in finitely many affine observations forces
positive lower density in the original predicate. -/
theorem positiveLowerPredicateDensity_of_finite_affine_preimages
    {ι : Type*} [Fintype ι] (bad : ℕ → Prop)
    (q r : ι → ℕ) (hq : ∀ i, 0 < q i)
    (hs : HasPositiveLowerPredicateDensity (fun n => ∃ i, bad (q i * n + r i))) :
    HasPositiveLowerPredicateDensity bad := by
  classical
  exact positiveLowerPredicateDensity_of_affine_count_bound _ bad (Fintype.card ι)
    (1 + Finset.univ.sup q) (Finset.univ.sup r) (by omega)
    (predicateCount_finite_affine_preimages_le bad q r hq) hs

end IndependentZeroBlocks
