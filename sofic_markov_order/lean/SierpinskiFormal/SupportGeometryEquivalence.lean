import SierpinskiFormal.PorousSupportBounds
import SierpinskiFormal.SublinearAbsorption
import SierpinskiFormal.RationalRelativeHoles
import SierpinskiFormal.ExactGrowthGapExamples

set_option autoImplicit false

namespace IndependentZeroBlocks
open SierpinskiFormal

/-- Local holes in a coefficient support imply ordinary support density zero. -/
theorem HasUniformRelativeHoles.toZeroSupportDensity
    {K : Type*} [Semiring K] {F : PowerSeries K}
    (h : HasUniformRelativeHoles (fun n => PowerSeries.coeff n F ≠ 0)) :
    HasZeroSupportDensity F :=
  (zeroPredicateDensity_support_iff F).mp h.toZeroPredicateDensity

/-- Positive lower density obstructs uniform local relative holes, even when
there are large zero gaps at some locations. -/
theorem HasPositiveLowerSupportDensity.not_uniformRelativeHoles
    {K : Type*} [Semiring K] {F : PowerSeries K}
    (h : HasPositiveLowerSupportDensity F) :
    ¬HasUniformRelativeHoles (fun n => PowerSeries.coeff n F ≠ 0) := by
  intro hholes
  exact h.not_zero hholes.toZeroSupportDensity

/-- For rational digit-product filters, uniform local holes are exactly
finite-prefix absorption. This includes a zero numerator. -/
theorem digitProduct_rational_uniformRelativeHoles_iff
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b - 1) (P D : Polynomial K)
    (hD0 : D.coeff 0 ≠ 0) :
    HasUniformRelativeHoles (fun n => PowerSeries.coeff n
        (rationalMultiple P D (canonicalSeries b A)) ≠ 0) ↔
      ∃ e, D ∣ P * kernelPrefix b A e := by
  constructor
  · intro hholes
    exact (digitProduct_rational_density_zero_iff b hb A hA0 hdegree P D hD0).mp
      hholes.toZeroSupportDensity
  · intro habs
    exact digitProduct_rational_hasUniformRelativeHoles_of_absorbed b hb A hA0
      (by omega) (radixDigitSupportCount_lt_of_degree b A hdegree) P D hD0 habs

/-- Uniform translated-interval sublinear counting is another equivalent
description of the absorbed filters. The constant is uniform in the location. -/
theorem digitProduct_rational_uniformSublinearGrowth_iff
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b - 1) (P D : Polynomial K)
    (hD0 : D.coeff 0 ≠ 0) :
    (∃ α : ℝ, α < 1 ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ a N : ℕ, 1 ≤ N →
      (intervalPredicateCount (fun n => PowerSeries.coeff n
        (rationalMultiple P D (canonicalSeries b A)) ≠ 0) a N : ℝ) ≤
          C * (N : ℝ) ^ α) ↔
      ∃ e, D ∣ P * kernelPrefix b A e := by
  constructor
  · rintro ⟨α, hα, C, hC, hlocal⟩
    apply (digitProduct_rational_sublinearGrowth_iff b hb A hA0 hdegree P D hD0).mp
    refine ⟨α, hα, C, hC, 1, ?_⟩
    intro N hN
    have heq : predicateCount (fun n => PowerSeries.coeff n
        (rationalMultiple P D (canonicalSeries b A)) ≠ 0) N =
      intervalPredicateCount (fun n => PowerSeries.coeff n
        (rationalMultiple P D (canonicalSeries b A)) ≠ 0) 0 N := by
      classical
      unfold predicateCount intervalPredicateCount
      congr 1
      ext n
      simp
    rw [heq]
    exact hlocal 0 N hN
  · intro habs
    obtain ⟨α, _, hα, C, hC, hlocal⟩ :=
      ((digitProduct_rational_uniformRelativeHoles_iff b hb A hA0 hdegree P D hD0).mpr
        habs).exists_uniform_interval_power_bound
    exact ⟨α, hα, C, hC, hlocal⟩

/-- Density, sharp digit upper growth, any sublinear upper growth, and uniform
relative holes coincide on the rational digit-product family. -/
theorem digitProduct_rational_sparse_geometry_equivalences
    {K : Type*} [Field K] (b : ℕ) (hb : 2 ≤ b)
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b - 1) (P D : Polynomial K)
    (hD0 : D.coeff 0 ≠ 0) :
    (HasZeroSupportDensity (rationalMultiple P D (canonicalSeries b A)) ↔
      HasUniformRelativeHoles (fun n => PowerSeries.coeff n
        (rationalMultiple P D (canonicalSeries b A)) ≠ 0)) ∧
    (HasUniformRelativeHoles (fun n => PowerSeries.coeff n
        (rationalMultiple P D (canonicalSeries b A)) ≠ 0) ↔
      HasPowerPredicateBound (digitSupportExponent b A)
        (fun n => PowerSeries.coeff n
          (rationalMultiple P D (canonicalSeries b A)) ≠ 0)) ∧
    ((∃ α : ℝ, α < 1 ∧ HasPowerPredicateBound α
        (fun n => PowerSeries.coeff n
          (rationalMultiple P D (canonicalSeries b A)) ≠ 0)) ↔
      ∃ e, D ∣ P * kernelPrefix b A e) := by
  have hh := digitProduct_rational_uniformRelativeHoles_iff b hb A hA0 hdegree P D hD0
  exact ⟨(digitProduct_rational_density_zero_iff b hb A hA0 hdegree P D hD0).trans hh.symm,
    hh.trans (digitProduct_rational_digitUpperGrowth_iff b hb A hA0 hdegree P D hD0).symm,
    digitProduct_rational_sublinearGrowth_iff b hb A hA0 hdegree P D hD0⟩

/-- The finite-field test now detects uniform local holes as well as density
and exact support growth. -/
theorem finiteField_rational_uniformRelativeHoles_iff_finite_test
    {K : Type*} [Field K] [Fintype K]
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < Fintype.card K - 1)
    (P D : Polynomial K) (hD0 : D.coeff 0 ≠ 0) :
    HasUniformRelativeHoles (fun n => PowerSeries.coeff n
        (rationalMultiple P D (canonicalSeries (Fintype.card K) A)) ≠ 0) ↔
      D ∣ P * A ^ D.natDegree := by
  exact (digitProduct_rational_uniformRelativeHoles_iff (Fintype.card K)
    Fintype.one_lt_card A hA0 hdegree P D hD0).trans
      (exists_dvd_mul_kernelPrefix_iff_dvd_mul_pow_natDegree
        (show D ≠ 0 by intro hz; apply hD0; simp [hz]))

local instance geometryEquivalencePrimeSeven : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- A concrete boundary: proportional common zero gaps do not imply uniform
relative holes in the individual supports. -/
theorem separatedPrefixSeries_proportional_but_not_uniformRelativeHoles :
    HasProportionalIntervals (fun n => ∀ i : Bool,
      PowerSeries.coeff n (separatedPrefixSeries (K := ZMod 7) i) = 0) ∧
    ∀ i : Bool, ¬HasUniformRelativeHoles (fun n =>
      PowerSeries.coeff n (separatedPrefixSeries (K := ZMod 7) i) ≠ 0) := by
  have hp := separatedPrefixSeries_proportional_sparse_adjunct (K := ZMod 7)
  have hhost : HasProportionalIntervals (fun n => ∀ i : Bool,
      PowerSeries.coeff n (separatedPrefixSeries (K := ZMod 7) i) = 0) := by
    rw [← hasPowerIntervals_one_iff] at hp ⊢
    exact hp.mono (fun _ h => h.1)
  exact ⟨hhost, fun i =>
    (separatedPrefixSeries_seven_positive_lower_density i).not_uniformRelativeHoles⟩

end IndependentZeroBlocks
