import SierpinskiFormal.PredicateLogDensity
import SierpinskiFormal.PolynomialObservedSupport

set_option autoImplicit false

/-!
# Logarithmic-density classification for radix-regular supports

The shifted-harmonic logarithmic-density-zero condition joins the existing
four-way support classification.  The analytic input is unconditional:
ordinary density zero implies logarithmic density zero, while an eventual
positive lower natural density excludes logarithmic density zero.
-/

namespace IndependentZeroBlocks

open SierpinskiFormal
open scoped BigOperators

/-- Whenever a support dichotomy gives either ordinary density zero or a
positive eventual lower density, logarithmic density zero has the same sparse
certificate. -/
theorem hasZeroPredicateLogDensity_iff_of_density_dichotomy
    (S : ℕ → Prop) (cert : Prop)
    (hzero : HasZeroPredicateDensity S ↔ cert)
    (hpositive : HasPositiveLowerPredicateDensity S ↔ ¬cert) :
    HasZeroPredicateLogDensity S ↔ cert := by
  constructor
  · intro hlog
    by_contra hcert
    exact (hpositive.mpr hcert).not_zeroLogDensity hlog
  · intro hcert
    exact (hzero.mpr hcert).hasZeroPredicateLogDensity

/-- The five support conditions for a scalar radix-regular sequence. -/
theorem radixRegular_support_five_way_classification
    {K : Type*} [CommRing K] (b : ℕ) (hb : 2 ≤ b)
    (f : ℕ → K) (hregular : IsRadixRegular b f) :
    (HasZeroPredicateDensity (fun n => f n ≠ 0) ↔
      HasForbiddenDigitWord b (fun n => f n ≠ 0)) ∧
    (HasUniformRelativeHoles (fun n => f n ≠ 0) ↔
      HasForbiddenDigitWord b (fun n => f n ≠ 0)) ∧
    ((∃ α : ℝ, α < 1 ∧ HasUniformPowerIntervalBound α (fun n => f n ≠ 0)) ↔
      HasForbiddenDigitWord b (fun n => f n ≠ 0)) ∧
    (HasPositiveLowerPredicateDensity (fun n => f n ≠ 0) ↔
      ¬HasForbiddenDigitWord b (fun n => f n ≠ 0)) ∧
    (HasZeroPredicateLogDensity (fun n => f n ≠ 0) ↔
      HasForbiddenDigitWord b (fun n => f n ≠ 0)) := by
  have h := radixRegular_support_classification b hb f hregular
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2,
    hasZeroPredicateLogDensity_iff_of_density_dichotomy _ _ h.1 h.2.2.2⟩

/-- The five support conditions for a finite family of radix-regular
sequences over the same radix. -/
theorem radixRegular_family_support_five_way_classification
    {K J : Type*} [CommRing K] [Fintype J] (b : ℕ) (hb : 2 ≤ b)
    (f : J → ℕ → K) (hregular : ∀ i, IsRadixRegular b (f i)) :
    (HasZeroPredicateDensity (fun n => ∃ i, f i n ≠ 0) ↔
      HasForbiddenDigitWord b (fun n => ∃ i, f i n ≠ 0)) ∧
    (HasUniformRelativeHoles (fun n => ∃ i, f i n ≠ 0) ↔
      HasForbiddenDigitWord b (fun n => ∃ i, f i n ≠ 0)) ∧
    ((∃ α : ℝ, α < 1 ∧ HasUniformPowerIntervalBound α
        (fun n => ∃ i, f i n ≠ 0)) ↔
      HasForbiddenDigitWord b (fun n => ∃ i, f i n ≠ 0)) ∧
    (HasPositiveLowerPredicateDensity (fun n => ∃ i, f i n ≠ 0) ↔
      ¬HasForbiddenDigitWord b (fun n => ∃ i, f i n ≠ 0)) ∧
    (HasZeroPredicateLogDensity (fun n => ∃ i, f i n ≠ 0) ↔
      HasForbiddenDigitWord b (fun n => ∃ i, f i n ≠ 0)) := by
  have h := radixRegular_family_support_classification b hb f hregular
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2,
    hasZeroPredicateLogDensity_iff_of_density_dichotomy _ _ h.1 h.2.2.2⟩

/-- The five support conditions for failure of a finite family of polynomial
identities among radix-regular sequences. -/
theorem polynomial_observed_regular_support_five_way_classification
    {K I J : Type*} [CommRing K] [Fintype J] (b : ℕ) (hb : 2 ≤ b)
    (f : I → ℕ → K) (hregular : ∀ i, IsRadixRegular b (f i))
    (P : J → MvPolynomial I K) :
    let bad := fun n => ∃ j, MvPolynomial.eval (fun i => f i n) (P j) ≠ 0
    (HasZeroPredicateDensity bad ↔ HasForbiddenDigitWord b bad) ∧
    (HasUniformRelativeHoles bad ↔ HasForbiddenDigitWord b bad) ∧
    ((∃ α : ℝ, α < 1 ∧ HasUniformPowerIntervalBound α bad) ↔
      HasForbiddenDigitWord b bad) ∧
    (HasPositiveLowerPredicateDensity bad ↔ ¬HasForbiddenDigitWord b bad) ∧
    (HasZeroPredicateLogDensity bad ↔ HasForbiddenDigitWord b bad) := by
  exact radixRegular_family_support_five_way_classification b hb
    (fun j n => MvPolynomial.eval (fun i => f i n) (P j))
    (fun j => IsRadixRegular.polynomial b hb f hregular (P j))

/-- Polynomial observations of current coefficient vectors in a finite
polynomial matrix dilation system satisfy the five-way classification. -/
theorem polynomialMatrix_polynomialObservation_support_five_way_classification
    {K I J : Type*} [CommRing K] [Fintype I] [Fintype J]
    (B : I → I → Polynomial K) (U : I → PowerSeries K)
    (b : ℕ) (hb : 2 ≤ b)
    (hEq : ∀ i, U i = ∑ j, (B i j : PowerSeries K) * dilate b (U j))
    (P : J → MvPolynomial I K) :
    let bad := fun n => ∃ j,
      MvPolynomial.eval (fun i => PowerSeries.coeff n (U i)) (P j) ≠ 0
    (HasZeroPredicateDensity bad ↔ HasForbiddenDigitWord b bad) ∧
    (HasUniformRelativeHoles bad ↔ HasForbiddenDigitWord b bad) ∧
    ((∃ α : ℝ, α < 1 ∧ HasUniformPowerIntervalBound α bad) ↔
      HasForbiddenDigitWord b bad) ∧
    (HasPositiveLowerPredicateDensity bad ↔ ¬HasForbiddenDigitWord b bad) ∧
    (HasZeroPredicateLogDensity bad ↔ HasForbiddenDigitWord b bad) := by
  apply polynomial_observed_regular_support_five_way_classification b hb
    (fun i n => PowerSeries.coeff n (U i)) _ P
  intro i
  exact polynomialMatrix_currentObservation_isRadixRegular B U b hb hEq
    (LinearMap.proj i)

end IndependentZeroBlocks
