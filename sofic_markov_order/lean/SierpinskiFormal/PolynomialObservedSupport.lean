import SierpinskiFormal.RegularSequenceRing
import SierpinskiFormal.RegularSupportApplications
import Mathlib.Algebra.MvPolynomial.Eval

set_option autoImplicit false
namespace IndependentZeroBlocks
open SierpinskiFormal
open scoped BigOperators

/-- Polynomial combinations of regular sequences are regular. The variable
index type need not be finite: each polynomial uses only finitely many. -/
theorem IsRadixRegular.polynomial
    {K I : Type*} [CommRing K] (b : ℕ) (hb : 2 ≤ b)
    (f : I → ℕ → K) (hregular : ∀ i, IsRadixRegular b (f i))
    (P : MvPolynomial I K) :
    IsRadixRegular b (fun n => MvPolynomial.eval (fun i => f i n) P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simpa using IsRadixRegular.const b hb c
  | add P Q hP hQ =>
    simpa only [MvPolynomial.eval_add] using hP.add b hb hQ
  | mul_X P i hP =>
    simpa only [MvPolynomial.eval_mul, MvPolynomial.eval_X] using hP.mul b hb (hregular i)

/-- The same forbidden-factor theorem controls failure of any finite
family of polynomial identities among regular sequences. -/
theorem polynomial_observed_regular_support_classification
    {K I J : Type*} [CommRing K] [Fintype J] (b : ℕ) (hb : 2 ≤ b)
    (f : I → ℕ → K) (hregular : ∀ i, IsRadixRegular b (f i))
    (P : J → MvPolynomial I K) :
    let bad := fun n => ∃ j, MvPolynomial.eval (fun i => f i n) (P j) ≠ 0
    (HasZeroPredicateDensity bad ↔ HasForbiddenDigitWord b bad) ∧
    (HasUniformRelativeHoles bad ↔ HasForbiddenDigitWord b bad) ∧
    ((∃ α : ℝ, α < 1 ∧ HasUniformPowerIntervalBound α bad) ↔ HasForbiddenDigitWord b bad) ∧
    (HasPositiveLowerPredicateDensity bad ↔ ¬HasForbiddenDigitWord b bad) := by
  exact radixRegular_family_support_classification b hb
    (fun j n => MvPolynomial.eval (fun i => f i n) (P j))
    (fun j => IsRadixRegular.polynomial b hb f hregular (P j))

/-- Polynomial observations of current coefficient vectors in every finite
polynomial matrix dilation system obey the unified sparse/dense theorem. -/
theorem polynomialMatrix_polynomialObservation_support_classification
    {K I J : Type*} [CommRing K] [Fintype I] [Fintype J]
    (B : I → I → Polynomial K) (U : I → PowerSeries K)
    (b : ℕ) (hb : 2 ≤ b)
    (hEq : ∀ i, U i = ∑ j, (B i j : PowerSeries K) * dilate b (U j))
    (P : J → MvPolynomial I K) :
    let bad := fun n => ∃ j, MvPolynomial.eval (fun i => PowerSeries.coeff n (U i)) (P j) ≠ 0
    (HasZeroPredicateDensity bad ↔ HasForbiddenDigitWord b bad) ∧
    (HasUniformRelativeHoles bad ↔ HasForbiddenDigitWord b bad) ∧
    ((∃ α : ℝ, α < 1 ∧ HasUniformPowerIntervalBound α bad) ↔ HasForbiddenDigitWord b bad) ∧
    (HasPositiveLowerPredicateDensity bad ↔ ¬HasForbiddenDigitWord b bad) := by
  apply polynomial_observed_regular_support_classification b hb
    (fun i n => PowerSeries.coeff n (U i)) _ P
  intro i
  exact polynomialMatrix_currentObservation_isRadixRegular B U b hb hEq (LinearMap.proj i)

end IndependentZeroBlocks
