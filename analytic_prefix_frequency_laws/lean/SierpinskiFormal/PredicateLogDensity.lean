import SierpinskiFormal.ImmortalConeDensity
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.PSeries

set_option autoImplicit false

/-!
# Logarithmic density for predicates on the natural numbers

We use the shifted harmonic convention.  The mass below `N` is
`sum_{n<N, S n} 1/(n+1)`, and its normalizer is
`sum_{n<N} 1/(n+1)`.  The shift includes the index zero and avoids a special
case there.  The normalizer is asymptotic to `log N`.  Comparing the shifted
weights with `1/n` also involves a summable error (rather than merely a finite
change), which is recorded separately from the unconditional zero-density
results below.
-/

namespace IndependentZeroBlocks

open Filter
open scoped Topology BigOperators

/-- The real indicator of a predicate on the natural numbers. -/
noncomputable def predicateIndicator (S : ℕ → Prop) (n : ℕ) : ℝ :=
  by
    classical
    exact if S n then 1 else 0

/-- Shifted harmonic mass of the indices below `N` satisfying `S`. -/
noncomputable def predicateLogWeight (S : ℕ → Prop) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, predicateIndicator S n / ((n : ℝ) + 1)

/-- Shifted harmonic normalizer below `N`. -/
noncomputable def logarithmicNormalizer (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) + 1)

/-- The shifted-harmonic logarithmic-density ratio. -/
noncomputable def predicateLogDensityRatio (S : ℕ → Prop) (N : ℕ) : ℝ :=
  predicateLogWeight S N / logarithmicNormalizer N

/-- A predicate has logarithmic density `delta` in the shifted-harmonic convention. -/
def HasPredicateLogDensity (S : ℕ → Prop) (delta : ℝ) : Prop :=
  Tendsto (predicateLogDensityRatio S) atTop (𝓝 delta)

/-- A predicate has logarithmic density zero. -/
def HasZeroPredicateLogDensity (S : ℕ → Prop) : Prop :=
  HasPredicateLogDensity S 0

/-- The lower logarithmic density of `S` is at least `c`, expressed without
choosing an extended-real liminf. -/
def HasLowerPredicateLogDensityAtLeast (S : ℕ → Prop) (c : ℝ) : Prop :=
  ∀ c' : ℝ, c' < c → ∀ᶠ N : ℕ in atTop, c' ≤ predicateLogDensityRatio S N

@[simp] theorem predicateIndicator_nonneg (S : ℕ → Prop) (n : ℕ) :
    0 ≤ predicateIndicator S n := by
  classical
  unfold predicateIndicator
  split <;> norm_num

@[simp] theorem predicateIndicator_le_one (S : ℕ → Prop) (n : ℕ) :
    predicateIndicator S n ≤ 1 := by
  classical
  unfold predicateIndicator
  split <;> norm_num

theorem predicateCount_cast_eq_sum_indicator (S : ℕ → Prop) (N : ℕ) :
    (predicateCount S N : ℝ) = ∑ n ∈ Finset.range N, predicateIndicator S n := by
  classical
  unfold predicateCount predicateIndicator
  simp

theorem logarithmicNormalizer_tendsto_atTop :
    Tendsto logarithmicNormalizer atTop atTop := by
  change Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (1 : ℝ) / ((n : ℝ) + 1)) atTop atTop
  exact Real.tendsto_sum_range_one_div_nat_succ_atTop

/-- The positive first difference of the shifted harmonic weights. -/
noncomputable def harmonicDifference (i : ℕ) : ℝ :=
  1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2)

theorem harmonicDifference_nonneg (i : ℕ) : 0 ≤ harmonicDifference i := by
  unfold harmonicDifference
  apply sub_nonneg.mpr
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

theorem harmonicDifference_mul_succ (i : ℕ) :
    harmonicDifference i * (i + 1 : ℕ) = 1 / ((i : ℝ) + 2) := by
  unfold harmonicDifference
  have hi1 : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  have hi2 : (0 : ℝ) < (i : ℝ) + 2 := by positivity
  field_simp [ne_of_gt hi1, ne_of_gt hi2]
  push_cast
  ring

theorem sum_harmonicDifference (n : ℕ) :
    ∑ i ∈ Finset.range n, harmonicDifference i =
      1 - 1 / ((n : ℝ) + 1) := by
  induction n with
  | zero => simp [harmonicDifference]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      unfold harmonicDifference
      push_cast
      ring

theorem sum_harmonicDifference_le_one (n : ℕ) :
    ∑ i ∈ Finset.range n, harmonicDifference i ≤ 1 := by
  rw [sum_harmonicDifference]
  exact sub_le_self 1 (by positivity)

theorem sum_harmonicDifference_mul_succ (n : ℕ) :
    ∑ i ∈ Finset.range n, harmonicDifference i * (i + 1 : ℕ) =
      logarithmicNormalizer (n + 1) - 1 := by
  induction n with
  | zero => simp [logarithmicNormalizer]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, harmonicDifference_mul_succ]
      simp only [logarithmicNormalizer, Finset.sum_range_succ, Nat.cast_add,
        Nat.cast_one]
      ring

theorem predicateCount_le_self (S : ℕ → Prop) (N : ℕ) :
    predicateCount S N ≤ N := by
  classical
  unfold predicateCount
  simpa using Finset.card_filter_le (Finset.range N) S

/-- Abel summation for the shifted harmonic predicate mass. -/
theorem predicateLogWeight_eq_by_parts (S : ℕ → Prop) {N : ℕ} (hN : 0 < N) :
    predicateLogWeight S N =
      (predicateCount S N : ℝ) / N +
        ∑ i ∈ Finset.Ico 0 (N - 1),
          ((1 : ℝ) / (i + 1 : ℕ) - 1 / (i + 2 : ℕ)) *
            (predicateCount S (i + 1) : ℝ) := by
  classical
  have hparts := Finset.sum_Ico_by_parts
    (f := fun i : ℕ ↦ (1 : ℝ) / ((i : ℝ) + 1))
    (g := predicateIndicator S) hN
  rw [show Finset.Ico 0 N = Finset.range N by ext i; simp] at hparts
  simp only [smul_eq_mul] at hparts
  have hparts' :
      ∑ n ∈ Finset.range N, predicateIndicator S n / ((n : ℝ) + 1) =
        (1 / (((N - 1 : ℕ) : ℝ) + 1)) *
            ∑ i ∈ Finset.range N, predicateIndicator S i -
          (1 / (((0 : ℕ) : ℝ) + 1)) *
            ∑ i ∈ Finset.range 0, predicateIndicator S i -
          ∑ i ∈ Finset.Ico 0 (N - 1),
            (1 / (((i + 1 : ℕ) : ℝ) + 1) - 1 / ((i : ℝ) + 1)) *
              ∑ j ∈ Finset.range (i + 1), predicateIndicator S j := by
    simpa [div_eq_mul_inv, mul_comm] using hparts
  rw [predicateLogWeight, hparts']
  simp only [Finset.sum_range_zero, mul_zero, sub_zero,
    predicateCount_cast_eq_sum_indicator]
  have hcastN : (((N - 1 : ℕ) : ℝ) + 1) = (N : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ N)]
    norm_num
  rw [hcastN, sub_eq_add_neg]
  congr 1
  · ring
  · rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    push_cast
    ring

theorem logarithmicNormalizer_nonneg (N : ℕ) :
    0 ≤ logarithmicNormalizer N := by
  unfold logarithmicNormalizer
  exact Finset.sum_nonneg (fun i _ => by positivity)

theorem logarithmicNormalizer_pos {N : ℕ} (hN : 0 < N) :
    0 < logarithmicNormalizer N := by
  unfold logarithmicNormalizer
  apply Finset.sum_pos (fun i _ => by positivity)
  exact ⟨0, by simp [hN]⟩

theorem predicateLogWeight_nonneg (S : ℕ → Prop) (N : ℕ) :
    0 ≤ predicateLogWeight S N := by
  unfold predicateLogWeight
  apply Finset.sum_nonneg
  intro i hi
  exact div_nonneg (predicateIndicator_nonneg S i) (by positivity)

theorem predicateLogDensityRatio_nonneg (S : ℕ → Prop) (N : ℕ) :
    0 ≤ predicateLogDensityRatio S N := by
  exact div_nonneg (predicateLogWeight_nonneg S N) (logarithmicNormalizer_nonneg N)

/-- An eventual upper bound for ordinary prefix densities gives an Abel-type
upper bound for the shifted harmonic mass.  The additive constant absorbs the
finitely many prefixes before `M`. -/
theorem predicateLogWeight_le_of_eventually_density_le
    (S : ℕ → Prop) {ε : ℝ} (hε : 0 ≤ ε) {M N : ℕ} (hM : 1 ≤ M) (hN : 0 < N)
    (hdensity : ∀ k : ℕ, M ≤ k → (predicateCount S k : ℝ) / (k : ℝ) ≤ ε) :
    predicateLogWeight S N ≤ ε * logarithmicNormalizer N + 2 * M := by
  have hcount (k : ℕ) :
      (predicateCount S k : ℝ) ≤ ε * (k : ℝ) + M := by
    by_cases hk : M ≤ k
    · have hkpos : (0 : ℝ) < k := by exact_mod_cast hM.trans hk
      have := (div_le_iff₀ hkpos).mp (hdensity k hk)
      exact this.trans (le_add_of_nonneg_right (Nat.cast_nonneg M))
    · have hc : (predicateCount S k : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast predicateCount_le_self S k
      have hk' : (k : ℝ) ≤ (M : ℝ) := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hk))
      exact hc.trans
        (hk'.trans (le_add_of_nonneg_left (mul_nonneg hε (Nat.cast_nonneg k))))
  rw [predicateLogWeight_eq_by_parts S hN]
  have hboundary : (predicateCount S N : ℝ) / (N : ℝ) ≤ ε + M := by
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    calc
      (predicateCount S N : ℝ) / (N : ℝ) ≤
          (ε * (N : ℝ) + M) / (N : ℝ) :=
        div_le_div_of_nonneg_right (hcount N) hNr.le
      _ = ε + M / (N : ℝ) := by
        rw [add_div, mul_comm ε, mul_div_cancel_left₀ ε (ne_of_gt hNr)]
      _ ≤ ε + M := by
        gcongr
        exact (div_le_iff₀ hNr).mpr (by nlinarith [show (1 : ℝ) ≤ N by exact_mod_cast hN])
  have hsum :
      (∑ i ∈ Finset.Ico 0 (N - 1),
          ((1 : ℝ) / (i + 1 : ℕ) - 1 / (i + 2 : ℕ)) *
            (predicateCount S (i + 1) : ℝ)) ≤
        ε * (logarithmicNormalizer N - 1) + M := by
    calc
      _ ≤ ∑ i ∈ Finset.Ico 0 (N - 1),
          harmonicDifference i * (ε * ((i + 1 : ℕ) : ℝ) + M) := by
        apply Finset.sum_le_sum
        intro i hi
        simp only [Finset.mem_Ico] at hi
        have hd := harmonicDifference_nonneg i
        have hc := hcount (i + 1)
        simpa only [harmonicDifference, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using
          mul_le_mul_of_nonneg_left hc hd
      _ = ε * (∑ i ∈ Finset.Ico 0 (N - 1),
              harmonicDifference i * (i + 1 : ℕ)) +
            M * (∑ i ∈ Finset.Ico 0 (N - 1), harmonicDifference i) := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib]
        simp only [Finset.mul_sum]
        congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring
      _ ≤ ε * (logarithmicNormalizer N - 1) + M := by
        have hNm1 : N - 1 + 1 = N := by omega
        rw [show Finset.Ico 0 (N - 1) = Finset.range (N - 1) by ext i; simp]
        have hd1 := sum_harmonicDifference_le_one (N - 1)
        have hd2 := sum_harmonicDifference_mul_succ (N - 1)
        rw [hNm1] at hd2
        rw [hd2]
        simpa only [mul_one, add_comm] using add_le_add_left
          (mul_le_mul_of_nonneg_left hd1 (Nat.cast_nonneg M))
          (ε * (logarithmicNormalizer N - 1))
  calc
    (predicateCount S N : ℝ) / (N : ℝ) +
        ∑ i ∈ Finset.Ico 0 (N - 1),
          ((1 : ℝ) / (i + 1 : ℕ) - 1 / (i + 2 : ℕ)) *
            (predicateCount S (i + 1) : ℝ)
      ≤ (ε + M) + (ε * (logarithmicNormalizer N - 1) + M) :=
        add_le_add hboundary hsum
    _ = ε * logarithmicNormalizer N + 2 * M := by ring

/-- Ordinary natural density zero implies shifted-harmonic logarithmic
density zero. -/
theorem HasZeroPredicateDensity.hasZeroPredicateLogDensity
    {S : ℕ → Prop} (hzero : HasZeroPredicateDensity S) :
    HasZeroPredicateLogDensity S := by
  rw [HasZeroPredicateLogDensity, HasPredicateLogDensity, Metric.tendsto_atTop]
  intro η hη
  have hdensity : ∀ᶠ N : ℕ in atTop,
      (predicateCount S N : ℝ) / (N : ℝ) < η / 2 :=
    hzero.eventually (Iio_mem_nhds (by linarith))
  obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.1 hdensity
  let M := max M₀ 1
  have hM : 1 ≤ M := by simp [M]
  have htail : ∀ N : ℕ, M ≤ N →
      (predicateCount S N : ℝ) / (N : ℝ) ≤ η / 2 := by
    intro N hN
    exact (hM₀ N ((show M₀ ≤ M by simp [M]).trans hN)).le
  have herr : Tendsto (fun N : ℕ => (2 * (M : ℝ)) / logarithmicNormalizer N)
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop logarithmicNormalizer_tendsto_atTop
  have hevent : ∀ᶠ N : ℕ in atTop,
      (2 * (M : ℝ)) / logarithmicNormalizer N < η / 2 :=
    herr.eventually (Iio_mem_nhds (by linarith))
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hevent
  refine ⟨max (max N₀ M) 1, fun N hN => ?_⟩
  have hNpos : 0 < N := by omega
  have hnormalizer := logarithmicNormalizer_pos hNpos
  have hweight := predicateLogWeight_le_of_eventually_density_le S
    (show 0 ≤ η / 2 by linarith) hM hNpos htail
  have hratio : predicateLogDensityRatio S N < η := by
    rw [predicateLogDensityRatio]
    calc
      predicateLogWeight S N / logarithmicNormalizer N ≤
          ((η / 2) * logarithmicNormalizer N + 2 * M) /
            logarithmicNormalizer N :=
        div_le_div_of_nonneg_right hweight hnormalizer.le
      _ = η / 2 + (2 * (M : ℝ)) / logarithmicNormalizer N := by
        rw [add_div, mul_comm (η / 2),
          mul_div_cancel_left₀ (η / 2) hnormalizer.ne']
      _ < η := by
        have := hN₀ N (by omega)
        linarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (predicateLogDensityRatio_nonneg S N)]
  exact hratio

theorem predicateCount_cast_add_compl (S : ℕ → Prop) (N : ℕ) :
    (predicateCount S N : ℝ) + predicateCount (fun n => ¬S n) N = N := by
  classical
  rw [predicateCount_cast_eq_sum_indicator,
    predicateCount_cast_eq_sum_indicator, ← Finset.sum_add_distrib]
  calc
    _ = ∑ n ∈ Finset.range N, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro n hn
      unfold predicateIndicator
      by_cases h : S n <;> simp [h]
    _ = N := by simp

theorem predicateLogWeight_add_compl (S : ℕ → Prop) (N : ℕ) :
    predicateLogWeight S N + predicateLogWeight (fun n => ¬S n) N =
      logarithmicNormalizer N := by
  classical
  unfold predicateLogWeight logarithmicNormalizer predicateIndicator
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases h : S n <;> simp [h]

theorem predicateLogDensityRatio_add_compl
    (S : ℕ → Prop) {N : ℕ} (hN : 0 < N) :
    predicateLogDensityRatio S N +
        predicateLogDensityRatio (fun n => ¬S n) N = 1 := by
  rw [predicateLogDensityRatio, predicateLogDensityRatio, ← add_div,
    predicateLogWeight_add_compl]
  exact div_self (logarithmicNormalizer_pos hN).ne'

/-- An eventual linear lower bound for prefix counts passes to the lower
shifted-harmonic logarithmic density. -/
theorem hasLowerPredicateLogDensityAtLeast_of_eventually_count_ge
    (S : ℕ → Prop) (c : ℝ)
    (hcount : ∀ᶠ N : ℕ in atTop,
      c * (N : ℝ) ≤ (predicateCount S N : ℝ)) :
    HasLowerPredicateLogDensityAtLeast S c := by
  intro c' hc'
  by_cases hc : 0 < c
  · obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.1 hcount
    let M := max M₀ 1
    have hM : 1 ≤ M := by simp [M]
    have hcountM : c * (M : ℝ) ≤ (predicateCount S M : ℝ) :=
      hM₀ M (by simp [M])
    have hcountM' : (predicateCount S M : ℝ) ≤ M := by
      exact_mod_cast predicateCount_le_self S M
    have hc_one : c ≤ 1 := by
      have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
      nlinarith
    have hcompl : ∀ k : ℕ, M ≤ k →
        (predicateCount (fun n => ¬S n) k : ℝ) / (k : ℝ) ≤ 1 - c := by
      intro k hk
      have hkr : (0 : ℝ) < k := by exact_mod_cast hM.trans hk
      apply (div_le_iff₀ hkr).2
      have hs := hM₀ k ((show M₀ ≤ M by simp [M]).trans hk)
      have hpartition := predicateCount_cast_add_compl S k
      linarith
    have herr : Tendsto (fun N : ℕ => (2 * (M : ℝ)) / logarithmicNormalizer N)
        atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop logarithmicNormalizer_tendsto_atTop
    have hevent : ∀ᶠ N : ℕ in atTop,
        (2 * (M : ℝ)) / logarithmicNormalizer N < c - c' :=
      herr.eventually (Iio_mem_nhds (sub_pos.mpr hc'))
    filter_upwards [hevent, eventually_ge_atTop M, eventually_ge_atTop 1] with N herrN hNM hN
    have hNpos : 0 < N := by omega
    have hnormalizer := logarithmicNormalizer_pos hNpos
    have hweight := predicateLogWeight_le_of_eventually_density_le
      (fun n => ¬S n) (sub_nonneg.mpr hc_one) hM hNpos hcompl
    have hcomplRatio :
        predicateLogDensityRatio (fun n => ¬S n) N ≤
          (1 - c) + (2 * (M : ℝ)) / logarithmicNormalizer N := by
      rw [predicateLogDensityRatio]
      calc
        predicateLogWeight (fun n => ¬S n) N / logarithmicNormalizer N ≤
            ((1 - c) * logarithmicNormalizer N + 2 * M) /
              logarithmicNormalizer N :=
          div_le_div_of_nonneg_right hweight hnormalizer.le
        _ = (1 - c) + (2 * (M : ℝ)) / logarithmicNormalizer N := by
          rw [add_div, mul_comm (1 - c),
            mul_div_cancel_left₀ (1 - c) hnormalizer.ne']
    have hpartition := predicateLogDensityRatio_add_compl S hNpos
    linarith
  · have hc_nonpos : c ≤ 0 := le_of_not_gt hc
    filter_upwards with N
    exact (le_trans (le_trans hc'.le hc_nonpos) (predicateLogDensityRatio_nonneg S N))

theorem HasPositiveLowerPredicateDensity.hasLowerPredicateLogDensityAtLeast
    {S : ℕ → Prop} (h : HasPositiveLowerPredicateDensity S) :
    ∃ c : ℝ, 0 < c ∧ HasLowerPredicateLogDensityAtLeast S c := by
  obtain ⟨c, hc, N₀, hN₀⟩ := h
  refine ⟨c, hc, hasLowerPredicateLogDensityAtLeast_of_eventually_count_ge S c ?_⟩
  exact Filter.eventually_atTop.2 ⟨N₀, hN₀⟩

/-- Positive eventual lower natural density is incompatible with logarithmic
density zero. -/
theorem HasPositiveLowerPredicateDensity.not_zeroLogDensity
    {S : ℕ → Prop} (h : HasPositiveLowerPredicateDensity S) :
    ¬HasZeroPredicateLogDensity S := by
  obtain ⟨c, hc, hlower⟩ := h.hasLowerPredicateLogDensityAtLeast
  intro hzero
  have hu : ∀ᶠ N : ℕ in atTop, predicateLogDensityRatio S N < c / 2 :=
    hzero.eventually (Iio_mem_nhds (by linarith))
  have hl : ∀ᶠ N : ℕ in atTop, c / 2 ≤ predicateLogDensityRatio S N :=
    hlower (c / 2) (by linarith)
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 hu
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1 hl
  let N := max N₁ N₂
  exact (not_lt_of_ge (hN₂ N (by simp [N]))) (hN₁ N (by simp [N]))

end IndependentZeroBlocks
