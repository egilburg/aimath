import SierpinskiFormal.UniformPowerClosure
import SierpinskiFormal.MissingDigitClassification

set_option autoImplicit false
namespace IndependentZeroBlocks
open SierpinskiFormal

/-- Uniform translated bounds include the prefix bound. -/
theorem HasUniformPowerIntervalBound.toPowerPredicateBound
    {α : ℝ} {bad : ℕ → Prop} (h : HasUniformPowerIntervalBound α bad) :
    HasPowerPredicateBound α bad := by
  obtain ⟨C, hC, hcount⟩ := h
  refine ⟨C, hC, 1, ?_⟩
  intro N hN
  have heq : predicateCount bad N = intervalPredicateCount bad 0 N := by
    classical
    unfold predicateCount intervalPredicateCount
    congr 1
    ext n
    simp
  rw [heq]
  exact hcount 0 N hN

theorem HasUniformPowerIntervalBound.exponent_mono
    {α β : ℝ} {bad : ℕ → Prop}
    (h : HasUniformPowerIntervalBound α bad) (hαβ : α ≤ β) :
    HasUniformPowerIntervalBound β bad := by
  obtain ⟨C, hC, hcount⟩ := h
  refine ⟨C, hC, ?_⟩
  intro a L hL
  exact (hcount a L hL).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hL) hαβ) hC)

/-- A positive lower power law forbids any smaller upper exponent. -/
theorem HasPowerSupportGrowth.le_exponent_of_upper_bound
    {K : Type*} [Semiring K] {F : PowerSeries K} {α β : ℝ}
    (h : HasPowerSupportGrowth F α)
    (hupper : HasPowerPredicateBound β (fun n => PowerSeries.coeff n F ≠ 0)) :
    α ≤ β := by
  by_contra hnot
  have hβα : β < α := lt_of_not_ge hnot
  obtain ⟨c, C, hc, hC, N₀, hcount⟩ := h
  obtain ⟨D, hD, N₁, hu⟩ := (powerPredicateBound_support_iff F β).mp hupper
  have hβgrowth : HasPowerSupportGrowth F β := by
    refine ⟨c, D + 1, hc, by linarith, max N₀ (max N₁ 1), ?_⟩
    intro N hN
    have hN₀ : N₀ ≤ N := by omega
    have hN₁ : N₁ ≤ N := by omega
    have hNpos : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    constructor
    · exact (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hNpos hβα.le) hc.le).trans (hcount N hN₀).1
    · exact (hu N hN₁).trans
        (mul_le_mul_of_nonneg_right (by linarith : D ≤ D + 1) (by positivity))
  have heq := (show HasPowerSupportGrowth F α from ⟨c, C, hc, hC, N₀, hcount⟩).exponent_eq hβgrowth
  linarith

/-- Every predicate has the universal translated linear count bound. -/
theorem hasUniformPowerIntervalBound_one (bad : ℕ → Prop) :
    HasUniformPowerIntervalBound 1 bad := by
  refine ⟨1, by norm_num, ?_⟩
  intro a L _
  have h : intervalPredicateCount bad a L ≤ L := by
    classical
    unfold intervalPredicateCount
    exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range L)
  simpa using (show (intervalPredicateCount bad a L : ℝ) ≤ L by exact_mod_cast h)

/-- In the nonzero absorbed case the actual digit exponent is the least
possible exponent even for bounds uniform over all translated intervals. -/
theorem missingDigit_rational_uniformGrowth_iff_exponent_ge
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b) (hmissing : ∃ m < b, A.coeff m = 0)
    (P D : Polynomial K) (hP : P ≠ 0) (hD0 : D.coeff 0 ≠ 0)
    (habs : ∃ e, D ∣ P * kernelPrefix b A e) (β : ℝ) :
    HasUniformPowerIntervalBound β (fun n => PowerSeries.coeff n
      (rationalMultiple P D (canonicalSeries b A)) ≠ 0) ↔
      digitSupportExponent b A ≤ β := by
  constructor
  · intro hu
    exact (missingDigit_rational_powerSupportGrowth_of_absorbed
      b hb A hA0 hdegree hmissing P D hP hD0 habs).le_exponent_of_upper_bound
        hu.toPowerPredicateBound
  · intro hβ
    exact (missingDigit_rational_uniformDigitLogIntervalBound_of_absorbed
      b hb A hA0 hdegree hmissing P D hD0 habs).exponent_mono hβ

/-- Complete classification of every admissible translated upper exponent.
The zero case allows every real exponent; other thresholds are sharp. -/
theorem missingDigit_rational_all_uniform_exponents
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b) (hmissing : ∃ m < b, A.coeff m = 0)
    (P D : Polynomial K) (hD0 : D.coeff 0 ≠ 0) (β : ℝ) :
    HasUniformPowerIntervalBound β (fun n => PowerSeries.coeff n
      (rationalMultiple P D (canonicalSeries b A)) ≠ 0) ↔
    P = 0 ∨
    ((∃ e, D ∣ P * kernelPrefix b A e) ∧ digitSupportExponent b A ≤ β) ∨
    ((∀ e, ¬D ∣ P * kernelPrefix b A e) ∧ 1 ≤ β) := by
  constructor
  · intro hu
    by_cases hP : P = 0
    · exact Or.inl hP
    · by_cases habs : ∃ e, D ∣ P * kernelPrefix b A e
      · exact Or.inr (Or.inl ⟨habs,
          (missingDigit_rational_uniformGrowth_iff_exponent_ge b hb A hA0 hdegree
            hmissing P D hP hD0 habs β).mp hu⟩)
      · have hnot : ∀ e, ¬D ∣ P * kernelPrefix b A e := by simpa using habs
        exact Or.inr (Or.inr ⟨hnot,
          ((missingDigit_rational_linearGrowth_iff b hb A hA0 hdegree hmissing P D hD0).mpr
            hnot).le_exponent_of_upper_bound hu.toPowerPredicateBound⟩)
  · rintro (hP | ⟨habs, hβ⟩ | ⟨_, hβ⟩)
    · subst P
      refine ⟨0, le_rfl, ?_⟩
      intro a L hL
      simp [rationalMultiple, intervalPredicateCount]
    · exact (missingDigit_rational_uniformDigitLogIntervalBound_of_absorbed
        b hb A hA0 hdegree hmissing P D hD0 habs).exponent_mono hβ
    · exact (hasUniformPowerIntervalBound_one _).exponent_mono hβ

end IndependentZeroBlocks
