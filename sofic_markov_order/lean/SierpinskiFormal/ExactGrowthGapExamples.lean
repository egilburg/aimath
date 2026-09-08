import SierpinskiFormal.RelativeHoleSynchronization
import SierpinskiFormal.DigitRelativeHoles
import SierpinskiFormal.QuantitativeGapExamples

set_option autoImplicit false

/-!
# Proportional mixed-radix gap examples

The radix-four quarter-digit series has uniform relative holes, so adjoining it
to the radix-seven separated-prefix family preserves proportional gaps.  This
strengthens the earlier square-root interval statements.
-/

namespace IndependentZeroBlocks

open SierpinskiFormal

variable {K : Type*} [Field K]

private theorem separatedPrefixSeries_relativeHole_seed (i : Bool) :
    HasSeedBlocks 7 3 (separatedPrefixSeries (K := K) i) := by
  refine ⟨0, 0, ?_⟩
  intro E _ j _ hj
  exact separatedPrefixSeries_descendants E j hj i

private theorem quarterDigitSparseSeries_uniformRelativeHoles :
    HasUniformRelativeHoles
      (fun n =>
        PowerSeries.coeff n (quarterDigitSparseSeries (K := K)) ≠ 0) := by
  change HasUniformRelativeHoles
    (fun n => PowerSeries.coeff n
      (canonicalSeries 4 (1 + Polynomial.X : Polynomial K)) ≠ 0)
  exact canonicalSeries_support_hasUniformRelativeHoles_of_missingDigit
    (K := K) 4 (by omega)
    (1 + Polynomial.X : Polynomial K) (by simp)
    2 (by omega)
    (by simp [Polynomial.coeff_add, Polynomial.coeff_one,
      Polynomial.coeff_X])

/-- The radix-seven separated-prefix pair and the radix-four quarter-digit
series have common proportional zero intervals. -/
theorem separatedPrefixSeries_proportional_sparse_adjunct :
    HasProportionalIntervals (fun n =>
      (∀ i : Bool,
        PowerSeries.coeff n (separatedPrefixSeries (K := K) i) = 0) ∧
      PowerSeries.coeff n
        (quarterDigitSparseSeries (K := K)) = 0) := by
  have hF := proportionalIntervals_of_seed_family
    (separatedPrefixSeries (K := K))
    separatedPrefixSeries_relativeHole_seed
    (by omega : 2 ≤ 7) (by omega : 1 ≤ 3)
  have hG : ∀ _i : Unit, HasUniformRelativeHoles
      (fun n =>
        PowerSeries.coeff n (quarterDigitSparseSeries (K := K)) ≠ 0) := by
    intro _i
    exact quarterDigitSparseSeries_uniformRelativeHoles
  have h := proportional_family_adjoin_uniformRelativeHoles
    (separatedPrefixSeries (K := K))
    (fun _ : Unit => quarterDigitSparseSeries (K := K)) hF hG
  simpa using h

/-- Adding the same radix-four quarter-digit series to both members of the
radix-seven separated-prefix pair retains common proportional zero
intervals. -/
theorem separatedPrefixSeries_proportional_perturbations :
    HasProportionalIntervals (fun n => ∀ i : Bool,
      PowerSeries.coeff n
        (separatedPrefixSeries (K := K) i +
          quarterDigitSparseSeries (K := K)) = 0) := by
  have hF := proportionalIntervals_of_seed_family
    (separatedPrefixSeries (K := K))
    separatedPrefixSeries_relativeHole_seed
    (by omega : 2 ≤ 7) (by omega : 1 ≤ 3)
  have hG : ∀ _i : Bool, HasUniformRelativeHoles
      (fun n =>
        PowerSeries.coeff n (quarterDigitSparseSeries (K := K)) ≠ 0) := by
    intro _i
    exact quarterDigitSparseSeries_uniformRelativeHoles
  exact proportional_family_uniformRelativeHole_perturbations
    (separatedPrefixSeries (K := K))
    (fun _ : Bool => quarterDigitSparseSeries (K := K)) hF hG

end IndependentZeroBlocks
