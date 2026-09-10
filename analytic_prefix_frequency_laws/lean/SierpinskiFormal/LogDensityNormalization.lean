import SierpinskiFormal.PredicateLogDensity
import SierpinskiFormal.LogDensityClassification
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

set_option autoImplicit false

/-!
# Comparison with the standard logarithmic-density convention

The standard numerator uses `1/n` on `1 ≤ n < N` and is divided by `log N`.
The shifted convention includes zero with weight `1` and uses `1/(n+1)`.
Their numerator difference is uniformly bounded (the majorant telescopes),
while the shifted harmonic normalizer is asymptotic to `log N`.
-/

namespace IndependentZeroBlocks

open Filter
open scoped Topology BigOperators

/-- Standard harmonic mass on the positive indices below `N`. -/
noncomputable def predicateStandardLogWeight (S : ℕ → Prop) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico 1 N, predicateIndicator S n / (n : ℝ)

/-- Standard logarithmic-density ratio, with denominator `log N`. -/
noncomputable def predicateStandardLogDensityRatio (S : ℕ → Prop) (N : ℕ) : ℝ :=
  predicateStandardLogWeight S N / Real.log (N : ℝ)

/-- Standard logarithmic density using `1/n` and `log N`. -/
def HasPredicateStandardLogDensity (S : ℕ → Prop) (delta : ℝ) : Prop :=
  Tendsto (predicateStandardLogDensityRatio S) atTop (𝓝 delta)

/-- The shifted harmonic normalizer is the real coercion of the `N`th
harmonic number. -/
theorem logarithmicNormalizer_eq_harmonic (N : ℕ) :
    logarithmicNormalizer N = (harmonic N : ℝ) := by
  simp [logarithmicNormalizer, harmonic, one_div]

theorem real_log_nat_tendsto_atTop :
    Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

/-- The shifted harmonic normalizer is asymptotic to `log N`. -/
theorem logarithmicNormalizer_div_log_tendsto_one :
    Tendsto (fun N : ℕ => logarithmicNormalizer N / Real.log (N : ℝ))
      atTop (𝓝 1) := by
  have hdiff : Tendsto
      (fun N : ℕ => logarithmicNormalizer N - Real.log (N : ℝ))
      atTop (𝓝 Real.eulerMascheroniConstant) := by
    simpa only [logarithmicNormalizer_eq_harmonic] using
      Real.tendsto_harmonic_sub_log
  have hzero := hdiff.div_atTop real_log_nat_tendsto_atTop
  have heq : ∀ᶠ N : ℕ in atTop,
      logarithmicNormalizer N / Real.log (N : ℝ) =
        (logarithmicNormalizer N - Real.log (N : ℝ)) /
            Real.log (N : ℝ) + 1 := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hlog : Real.log (N : ℝ) ≠ 0 := by
      exact ne_of_gt (Real.log_pos (by exact_mod_cast hN))
    field_simp [hlog]
    ring
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  simpa using (hzero.add hone).congr' (Filter.EventuallyEq.symm heq)

/-- Conversely, `log N` divided by the shifted harmonic normalizer tends to
one. -/
theorem log_div_logarithmicNormalizer_tendsto_one :
    Tendsto (fun N : ℕ => Real.log (N : ℝ) / logarithmicNormalizer N)
      atTop (𝓝 1) := by
  have hinv := logarithmicNormalizer_div_log_tendsto_one.inv₀ (by norm_num)
  simpa only [inv_div, inv_one] using hinv

/-- The telescoping positive difference between the standard and shifted
weights at a positive index. -/
noncomputable def standardLogWeightDifference (n : ℕ) : ℝ :=
  1 / (n : ℝ) - 1 / ((n : ℝ) + 1)

theorem standardLogWeightDifference_nonneg {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ standardLogWeightDifference n := by
  unfold standardLogWeightDifference
  apply sub_nonneg.mpr
  exact one_div_le_one_div_of_le (by exact_mod_cast hn) (by linarith)

theorem sum_standardLogWeightDifference (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Ico 1 N, standardLogWeightDifference n =
      1 - 1 / (N : ℝ) := by
  induction N with
  | zero => omega
  | succ N ih =>
      by_cases hN0 : N = 0
      · subst N
        simp
      · have hNpos : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
        rw [Finset.sum_Ico_succ_top hNpos, ih hNpos]
        unfold standardLogWeightDifference
        push_cast
        ring

theorem sum_standardLogWeightDifference_le_one (N : ℕ) :
    ∑ n ∈ Finset.Ico 1 N, standardLogWeightDifference n ≤ 1 := by
  by_cases hN : 1 ≤ N
  · rw [sum_standardLogWeightDifference N hN]
    exact sub_le_self 1 (by positivity)
  · have : N = 0 := by omega
    subst N
    simp

theorem predicateLogWeight_sub_standard_eq (S : ℕ → Prop)
    {N : ℕ} (hN : 0 < N) :
    predicateLogWeight S N - predicateStandardLogWeight S N =
      predicateIndicator S 0 -
        ∑ n ∈ Finset.Ico 1 N,
          predicateIndicator S n * standardLogWeightDifference n := by
  classical
  have hrange : Finset.range N = insert 0 (Finset.Ico 1 N) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
    omega
  rw [predicateLogWeight, predicateStandardLogWeight, hrange,
    Finset.sum_insert (by simp)]
  simp only [Nat.cast_zero, zero_add, div_one]
  have htail :
      (∑ n ∈ Finset.Ico 1 N, predicateIndicator S n / ((n : ℝ) + 1)) -
          ∑ n ∈ Finset.Ico 1 N, predicateIndicator S n / (n : ℝ) =
        -(∑ n ∈ Finset.Ico 1 N,
          predicateIndicator S n * standardLogWeightDifference n) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    unfold standardLogWeightDifference
    ring
  rw [add_sub_assoc, htail]
  ring

/-- The shifted and standard logarithmic numerators differ by at most one.
This is the finite-partial-sum form of the summable-error comparison. -/
theorem abs_predicateLogWeight_sub_standard_le_one
    (S : ℕ → Prop) (N : ℕ) :
    |predicateLogWeight S N - predicateStandardLogWeight S N| ≤ 1 := by
  by_cases hN : 0 < N
  · rw [predicateLogWeight_sub_standard_eq S hN, abs_le]
    have hsum_nonneg : 0 ≤ ∑ n ∈ Finset.Ico 1 N,
        predicateIndicator S n * standardLogWeightDifference n := by
      apply Finset.sum_nonneg
      intro n hn
      exact mul_nonneg (predicateIndicator_nonneg S n)
        (standardLogWeightDifference_nonneg (Finset.mem_Ico.mp hn).1)
    have hsum_le : ∑ n ∈ Finset.Ico 1 N,
        predicateIndicator S n * standardLogWeightDifference n ≤ 1 := by
      refine (Finset.sum_le_sum (fun n hn => ?_)).trans
        (sum_standardLogWeightDifference_le_one N)
      exact mul_le_of_le_one_left
        (standardLogWeightDifference_nonneg (Finset.mem_Ico.mp hn).1)
        (predicateIndicator_le_one S n)
    constructor
    · linarith [predicateIndicator_nonneg S 0]
    · linarith [predicateIndicator_le_one S 0]
  · have : N = 0 := by omega
    subst N
    simp [predicateLogWeight, predicateStandardLogWeight]

theorem predicateLogWeight_sub_standard_div_log_tendsto_zero
    (S : ℕ → Prop) :
    Tendsto (fun N : ℕ =>
      (predicateLogWeight S N - predicateStandardLogWeight S N) /
        Real.log (N : ℝ)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hone : Tendsto (fun N : ℕ => (1 : ℝ) / Real.log (N : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop real_log_nat_tendsto_atTop
  have hevent : ∀ᶠ N : ℕ in atTop, (1 : ℝ) / Real.log (N : ℝ) < ε :=
    hone.eventually (Iio_mem_nhds hε)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hevent
  refine ⟨max N₀ 2, fun N hN => ?_⟩
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 2 ≤ N by omega))
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hlog]
  calc
    |predicateLogWeight S N - predicateStandardLogWeight S N| /
        Real.log (N : ℝ) ≤ 1 / Real.log (N : ℝ) :=
      div_le_div_of_nonneg_right
        (abs_predicateLogWeight_sub_standard_le_one S N) hlog.le
    _ < ε := hN₀ N (by omega)

theorem predicateLogWeight_sub_standard_div_normalizer_tendsto_zero
    (S : ℕ → Prop) :
    Tendsto (fun N : ℕ =>
      (predicateLogWeight S N - predicateStandardLogWeight S N) /
        logarithmicNormalizer N) atTop (𝓝 0) := by
  have hprod := (predicateLogWeight_sub_standard_div_log_tendsto_zero S).mul
    log_div_logarithmicNormalizer_tendsto_one
  have heq : ∀ᶠ N : ℕ in atTop,
      ((predicateLogWeight S N - predicateStandardLogWeight S N) /
          Real.log (N : ℝ)) *
          (Real.log (N : ℝ) / logarithmicNormalizer N) =
        (predicateLogWeight S N - predicateStandardLogWeight S N) /
          logarithmicNormalizer N := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hlog : Real.log (N : ℝ) ≠ 0 :=
      ne_of_gt (Real.log_pos (by exact_mod_cast hN))
    field_simp [hlog]
  simpa using hprod.congr' heq

/-- The shifted-harmonic and standard `1/n` over `log N` definitions give
the same logarithmic density, at every value `delta`. -/
theorem hasPredicateLogDensity_iff_standard
    (S : ℕ → Prop) (delta : ℝ) :
    HasPredicateLogDensity S delta ↔ HasPredicateStandardLogDensity S delta := by
  constructor
  · intro hshift
    have hmain := hshift.mul logarithmicNormalizer_div_log_tendsto_one
    have hlimit := hmain.sub (predicateLogWeight_sub_standard_div_log_tendsto_zero S)
    have heq : ∀ᶠ N : ℕ in atTop,
        predicateLogDensityRatio S N *
              (logarithmicNormalizer N / Real.log (N : ℝ)) -
            (predicateLogWeight S N - predicateStandardLogWeight S N) /
              Real.log (N : ℝ) =
          predicateStandardLogDensityRatio S N := by
      filter_upwards [eventually_ge_atTop 2] with N hN
      have hlog : Real.log (N : ℝ) ≠ 0 :=
        ne_of_gt (Real.log_pos (by exact_mod_cast hN))
      have hnormalizer : logarithmicNormalizer N ≠ 0 :=
        (logarithmicNormalizer_pos (by omega)).ne'
      unfold predicateLogDensityRatio predicateStandardLogDensityRatio
      field_simp [hlog, hnormalizer]
      ring
    unfold HasPredicateStandardLogDensity
    simpa using hlimit.congr' heq
  · intro hstandard
    have hmain := hstandard.mul log_div_logarithmicNormalizer_tendsto_one
    have hlimit := hmain.add
      (predicateLogWeight_sub_standard_div_normalizer_tendsto_zero S)
    have heq : ∀ᶠ N : ℕ in atTop,
        predicateStandardLogDensityRatio S N *
              (Real.log (N : ℝ) / logarithmicNormalizer N) +
            (predicateLogWeight S N - predicateStandardLogWeight S N) /
              logarithmicNormalizer N =
          predicateLogDensityRatio S N := by
      filter_upwards [eventually_ge_atTop 2] with N hN
      have hlog : Real.log (N : ℝ) ≠ 0 :=
        ne_of_gt (Real.log_pos (by exact_mod_cast hN))
      have hnormalizer : logarithmicNormalizer N ≠ 0 :=
        (logarithmicNormalizer_pos (by omega)).ne'
      unfold predicateLogDensityRatio predicateStandardLogDensityRatio
      field_simp [hlog, hnormalizer]
      ring
    unfold HasPredicateLogDensity
    simpa using hlimit.congr' heq

theorem hasZeroPredicateLogDensity_iff_standard (S : ℕ → Prop) :
    HasZeroPredicateLogDensity S ↔ HasPredicateStandardLogDensity S 0 := by
  exact hasPredicateLogDensity_iff_standard S 0

/-- Standard logarithmic density zero has the intrinsic forbidden-word
classification for scalar radix-regular supports. -/
theorem radixRegular_support_standardLogDensity_iff_forbiddenDigitWord
    {K : Type*} [CommRing K] (b : ℕ) (hb : 2 ≤ b)
    (f : ℕ → K) (hregular : IsRadixRegular b f) :
    HasPredicateStandardLogDensity (fun n => f n ≠ 0) 0 ↔
      HasForbiddenDigitWord b (fun n => f n ≠ 0) := by
  have h := radixRegular_support_five_way_classification b hb f hregular
  exact (hasZeroPredicateLogDensity_iff_standard _).symm.trans h.2.2.2.2

/-- Standard logarithmic density zero has the intrinsic forbidden-word
classification for finite families of radix-regular supports. -/
theorem radixRegular_family_support_standardLogDensity_iff_forbiddenDigitWord
    {K J : Type*} [CommRing K] [Fintype J] (b : ℕ) (hb : 2 ≤ b)
    (f : J → ℕ → K) (hregular : ∀ i, IsRadixRegular b (f i)) :
    HasPredicateStandardLogDensity (fun n => ∃ i, f i n ≠ 0) 0 ↔
      HasForbiddenDigitWord b (fun n => ∃ i, f i n ≠ 0) := by
  have h := radixRegular_family_support_five_way_classification b hb f hregular
  exact (hasZeroPredicateLogDensity_iff_standard _).symm.trans h.2.2.2.2

/-- Standard logarithmic density zero has the intrinsic forbidden-word
classification for finite polynomial observations. -/
theorem polynomial_observed_regular_support_standardLogDensity_iff
    {K I J : Type*} [CommRing K] [Fintype J] (b : ℕ) (hb : 2 ≤ b)
    (f : I → ℕ → K) (hregular : ∀ i, IsRadixRegular b (f i))
    (P : J → MvPolynomial I K) :
    let bad := fun n => ∃ j, MvPolynomial.eval (fun i => f i n) (P j) ≠ 0
    HasPredicateStandardLogDensity bad 0 ↔ HasForbiddenDigitWord b bad := by
  have h := polynomial_observed_regular_support_five_way_classification
    b hb f hregular P
  exact (hasZeroPredicateLogDensity_iff_standard _).symm.trans h.2.2.2.2

end IndependentZeroBlocks
