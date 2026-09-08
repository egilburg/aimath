import SierpinskiFormal.QuantitativeSynchronization
import SierpinskiFormal.DigitSupportGrowth
import SierpinskiFormal.SynchronizationBeyondCompatibility

set_option autoImplicit false

namespace IndependentZeroBlocks

open SierpinskiFormal

variable {K : Type*} [Field K]

/-- The series supported on radix-four integers with digits zero or one. -/
noncomputable def quarterDigitSparseSeries : PowerSeries K :=
  canonicalSeries 4 (1 + Polynomial.X)

private theorem separatedPrefixSeries_quantitative_seed (i : Bool) :
    HasSeedBlocks 7 3 (separatedPrefixSeries (K := K) i) := by
  refine ⟨0, 0, ?_⟩
  intro E _ j _ hj
  exact separatedPrefixSeries_descendants E j hj i

/-- A concrete quantitative mixed-radix application over every field: the
radix-seven prefix pair shares square-root-sized late zero intervals with
the radix-four digit-product series. -/
theorem separatedPrefixSeries_sqrt_sparse_adjunct :
    HasPowerIntervals (1 / 2 : ℝ) (fun n =>
      (∀ i : Bool, PowerSeries.coeff n (separatedPrefixSeries (K := K) i) = 0) ∧
      PowerSeries.coeff n (quarterDigitSparseSeries (K := K)) = 0) := by
  have hF := proportionalIntervals_of_seed_family
    (separatedPrefixSeries (K := K)) separatedPrefixSeries_quantitative_seed
    (by omega : 2 ≤ 7) (by omega : 1 ≤ 3)
  have hG : ∀ _i : Unit, HasPowerPredicateBound (1 / 2 : ℝ)
      (fun n => PowerSeries.coeff n (quarterDigitSparseSeries (K := K)) ≠ 0) := by
    intro i
    exact canonicalSeries_four_one_add_X_powerSupportBound
  have h := proportional_family_adjoin_powerBound
    (separatedPrefixSeries (K := K))
    (fun _ : Unit => quarterDigitSparseSeries (K := K))
    (1 / 2 : ℝ) hF hG (by norm_num) (by norm_num)
  norm_num at h
  simpa using h

/-- Adding the same infinite sparse radix-four series to each member of the
radix-seven prefix pair retains square-root-sized common late zero intervals. -/
theorem separatedPrefixSeries_sqrt_perturbations :
    HasPowerIntervals (1 / 2 : ℝ) (fun n => ∀ i : Bool,
      PowerSeries.coeff n
        (separatedPrefixSeries (K := K) i + quarterDigitSparseSeries (K := K)) = 0) := by
  apply (separatedPrefixSeries_sqrt_sparse_adjunct (K := K)).mono
  intro n hn i
  rw [map_add, hn.1 i, hn.2, add_zero]

/-- The quantitative example includes the earlier qualitative notion of
arbitrarily long common zero blocks arbitrarily far out. -/
theorem separatedPrefixSeries_sparse_perturbations_zeroBlocks :
    HasArbitrarilyLongZeroBlocks (fun n i => PowerSeries.coeff n
      (separatedPrefixSeries (K := K) i + quarterDigitSparseSeries (K := K))) := by
  intro length start
  obtain ⟨N, hN, hzero⟩ :=
    (separatedPrefixSeries_sqrt_perturbations (K := K)).arbitrarilyLongIntervals
      (by norm_num) length start
  refine ⟨N, hN, ?_⟩
  intro j hj
  funext i
  exact hzero j hj i

end IndependentZeroBlocks
