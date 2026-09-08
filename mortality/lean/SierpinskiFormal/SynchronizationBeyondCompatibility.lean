import SierpinskiFormal.FiniteFieldDensity
import SierpinskiFormal.PoleCompatibility
import SierpinskiFormal.PrefixGapCriterion
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false

/-!
# Synchronization beyond common first degree and absorption

The radix-seven kernels `1 - X + X^4` and `1 - X^2 + X^4` have
different first positive degrees and neither absorbs the denominator `1-X`.
Their prefix filters nevertheless have a common absorbing zero window.
The elementary data below work over every field.
-/

namespace IndependentZeroBlocks

open SierpinskiFormal
open scoped BigOperators

variable {K : Type*} [Field K]

/-- Two kernels indexed by their distinct first positive degrees. -/
noncomputable def separatedPrefixKernel (i : Bool) : Polynomial K :=
  1 - Polynomial.X ^ (if i then 2 else 1) + Polynomial.X ^ 4

noncomputable def separatedPrefixSeries (i : Bool) : PowerSeries K :=
  rationalMultiple 1 (1 - Polynomial.X)
    (canonicalSeries 7 (separatedPrefixKernel i))

@[simp] theorem separatedPrefixKernel_coeff_zero (i : Bool) :
    (separatedPrefixKernel (K := K) i).coeff 0 = 1 := by
  cases i <;> simp [separatedPrefixKernel]

theorem separatedPrefixKernel_natDegree_le (i : Bool) :
    (separatedPrefixKernel (K := K) i).natDegree ≤ 4 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  cases i <;> simp [separatedPrefixKernel, Polynomial.coeff_X_pow,
    show n ≠ 0 by omega, Polynomial.coeff_one, Polynomial.coeff_X, show n ≠ 1 by omega, show 1 ≠ n by omega,
    show n ≠ 2 by omega, show n ≠ 4 by omega]

@[simp] theorem separatedPrefixKernel_eval_one (i : Bool) :
    (separatedPrefixKernel (K := K) i).eval 1 = 1 := by
  cases i <;> simp [separatedPrefixKernel]

/-- The prefix denominator cannot be absorbed, at any exponent. -/
theorem separatedPrefixKernel_not_absorbed (i : Bool) (N : ℕ) :
    ¬ ((1 - Polynomial.X : Polynomial K) ∣
      1 * separatedPrefixKernel i ^ N) := by
  intro h
  have he := Polynomial.eval_dvd (x := (1 : K)) h
  simp at he

theorem separatedPrefixKernel_firstDegree_iff (i : Bool) (d : ℕ) :
    KernelFirstDegree (separatedPrefixKernel (K := K) i) d ↔
      d = if i then 2 else 1 := by
  classical
  have hc : (separatedPrefixKernel (K := K) i).coeff
      (if i then 2 else 1) ≠ 0 := by
    cases i <;> simp [separatedPrefixKernel, Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_X]
  have hl : ∀ j, 0 < j → j < (if i then 2 else 1) →
      (separatedPrefixKernel (K := K) i).coeff j = 0 := by
    intro j hj hjlt
    cases i
    · simp only [Bool.false_eq_true, ↓reduceIte] at hjlt
      omega
    · simp only [↓reduceIte] at hjlt
      have hj1 : j = 1 := by omega
      simp [hj1, separatedPrefixKernel, Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_X]
  constructor
  · intro h
    rcases h with ⟨hd, hcoeff, hsmall⟩
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hcoeff (hl d hd hlt)
    · exact hc (hsmall _ (by cases i <;> decide) hgt)
  · intro hd
    subst d
    exact ⟨by cases i <;> decide, hc, hl⟩

/-- Even the cancellation-aware sufficient condition fails for this pair. -/
theorem separatedPrefixKernel_no_common_compatibility :
    ¬ ∃ d : ℕ, 0 < d ∧ ∀ i : Bool,
      KernelFirstDegree (separatedPrefixKernel (K := K) i) d ∨
        (1 - Polynomial.X : Polynomial K) ∣
          1 * separatedPrefixKernel i ^ (1 - Polynomial.X : Polynomial K).natDegree := by
  rintro ⟨d, _, h⟩
  have hf : d = 1 := by
    rcases h false with hf | hf
    · simpa using (separatedPrefixKernel_firstDegree_iff false d).mp hf
    · exact (separatedPrefixKernel_not_absorbed false _ hf).elim
  have ht : d = 2 := by
    rcases h true with ht | ht
    · simpa using (separatedPrefixKernel_firstDegree_iff true d).mp ht
    · exact (separatedPrefixKernel_not_absorbed true _ ht).elim
  omega

/-- Coefficients of division by `1-X` are inclusive prefix sums. -/
theorem coeff_prefix_rationalMultiple (T : PowerSeries K) (n : ℕ) :
    PowerSeries.coeff n (rationalMultiple 1 (1 - Polynomial.X) T) =
      ∑ j ∈ Finset.range (n + 1), PowerSeries.coeff j T := by
  let V : PowerSeries K := PowerSeries.mk fun n =>
    ∑ j ∈ Finset.range (n + 1), PowerSeries.coeff j T
  have hv : V = rationalMultiple 1 (1 - Polynomial.X) T := by
    apply eq_rationalMultiple_of_denominator
    · simp
    · have hcoe : ((1 - Polynomial.X : Polynomial K) : PowerSeries K) =
          1 - PowerSeries.X := by simp
      rw [hcoe]
      ext k
      cases k with
      | zero => simp [V]
      | succ k =>
        rw [sub_mul]
        simp only [map_sub, one_mul, PowerSeries.coeff_succ_X_mul]
        simp [V, Finset.sum_range_succ]
  rw [← hv]
  simp [V]

/-- Both filters vanish at coefficients two and three in any field. -/
theorem separatedPrefixSeries_seed (i : Bool) :
    PowerSeries.coeff 2 (separatedPrefixSeries (K := K) i) = 0 ∧
      PowerSeries.coeff 3 (separatedPrefixSeries (K := K) i) = 0 := by
  have hdigit (n : ℕ) (hn : n < 7) :
      PowerSeries.coeff n (canonicalSeries 7 (separatedPrefixKernel (K := K) i)) =
        (separatedPrefixKernel (K := K) i).coeff n := by
    simpa using coeff_canonicalSeries_mul_add 7 (by omega)
      (separatedPrefixKernel (K := K) i)
      (separatedPrefixKernel_coeff_zero i) 0 n hn
  simp only [separatedPrefixSeries, coeff_prefix_rationalMultiple]
  have h0 := hdigit 0 (by omega)
  have h1 := hdigit 1 (by omega)
  have h2 := hdigit 2 (by omega)
  have h3 := hdigit 3 (by omega)
  cases i <;>
    simp [Finset.sum_range_succ, h0, h1, h2, h3,
      separatedPrefixKernel, Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_X]

/-- The initial two-zero window propagates to the same geometric intervals
over every field, including characteristic zero. -/
theorem separatedPrefixSeries_descendants
    (E j : ℕ) (hj : j < 7 ^ E) (i : Bool) :
    PowerSeries.coeff (3 * 7 ^ E + j) (separatedPrefixSeries (K := K) i) = 0 := by
  have hdegree : ∀ i : Bool, (separatedPrefixKernel (K := K) i).natDegree < 7 := by
    intro i
    have h := separatedPrefixKernel_natDegree_le (K := K) i
    omega
  have hF : ∀ i : Bool, canonicalSeries 7 (separatedPrefixKernel (K := K) i) =
      (separatedPrefixKernel (K := K) i : PowerSeries K) *
        dilate 7 (canonicalSeries 7 (separatedPrefixKernel (K := K) i)) := by
    intro i
    exact canonicalSeries_dilation_equation 7 (by omega) _
      (separatedPrefixKernel_coeff_zero i) (hdegree i)
  have hz : ∀ i : Bool, ∀ t, t < 1 + 1 → PowerSeries.coeff (3 - t)
      (rationalMultiple 1 ((1 - Polynomial.X) ^ (1 : ℕ))
        (canonicalSeries 7 (separatedPrefixKernel (K := K) i))) = 0 := by
    intro i t ht
    have ht' : t = 0 ∨ t = 1 := by omega
    rcases ht' with rfl | rfl
    · simpa [separatedPrefixSeries] using (separatedPrefixSeries_seed (K := K) i).2
    · simpa [separatedPrefixSeries] using (separatedPrefixSeries_seed (K := K) i).1
  simpa [separatedPrefixSeries] using prefixFilter_family_descendants
    (separatedPrefixKernel (K := K))
    (fun i => canonicalSeries 7 (separatedPrefixKernel (K := K) i)) (fun _ => 1)
    7 1 3 (by omega) (by omega) (fun _ => le_rfl) hdegree hF hz E j hj i

/-- Common arbitrarily long late zero blocks, despite incompatible first
degrees and failure of every denominator-absorption test. -/
theorem separatedPrefixSeries_simultaneous_zeroBlocks :
    HasArbitrarilyLongZeroBlocks
      (fun n i => PowerSeries.coeff n (separatedPrefixSeries (K := K) i)) := by
  apply hasArbitrarilyLongZeroBlocks_of_descendants (q := 7) (seed := 3)
    (by omega) (by omega)
  intro E j hj
  funext i
  exact separatedPrefixSeries_descendants E j hj i

local instance sevenPrimeForSynchronizationBeyond : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- The counterexample satisfies the normalized finite-field branch equations. -/
theorem separatedPrefixSeries_seven_branch (i : Bool) :
    PowerSeries.coeff 0
        (canonicalSeries 7 (separatedPrefixKernel (K := ZMod 7) i)) = 1 ∧
      (separatedPrefixKernel (K := ZMod 7) i : PowerSeries (ZMod 7)) *
        (canonicalSeries 7 (separatedPrefixKernel (K := ZMod 7) i)) ^ 6 = 1 := by
  constructor
  · exact coeff_zero_canonicalSeries _ _
  · simpa [ZMod.card] using canonicalSeries_finiteField_branch
      (separatedPrefixKernel (K := ZMod 7) i) (separatedPrefixKernel_coeff_zero i)
      (by have h := separatedPrefixKernel_natDegree_le (K := ZMod 7) i
          simp only [ZMod.card]; omega)

/-- Both finite-field filters have positive lower support density, so neither
is covered by the sparse alternative in the previous theorem. -/
theorem separatedPrefixSeries_seven_positive_lower_density (i : Bool) :
    HasPositiveLowerSupportDensity (separatedPrefixSeries (K := ZMod 7) i) := by
  have hdegree : (separatedPrefixKernel (K := ZMod 7) i).natDegree <
      Fintype.card (ZMod 7) - 1 := by
    have h := separatedPrefixKernel_natDegree_le (K := ZMod 7) i
    simp only [ZMod.card]
    omega
  have hp := (finiteField_rational_positive_lower_density_iff
    (separatedPrefixKernel (K := ZMod 7) i) (separatedPrefixKernel_coeff_zero i)
    hdegree 1 (1 - Polynomial.X) (by simp)).mpr
      (separatedPrefixKernel_not_absorbed i _)
  simpa only [ZMod.card, separatedPrefixSeries] using hp

/-- A concrete refutation of necessity of the previous sufficient condition,
with both terms outside the density-zero alternative. -/
theorem separatedPrefixSeries_seven_counterexample :
    (∀ i : Bool, (separatedPrefixKernel (K := ZMod 7) i).coeff 0 = 1 ∧
      (separatedPrefixKernel (K := ZMod 7) i).natDegree <
        Fintype.card (ZMod 7) - 1) ∧
    (∀ i : Bool, HasPositiveLowerSupportDensity (separatedPrefixSeries (K := ZMod 7) i)) ∧
    HasArbitrarilyLongZeroBlocks
      (fun n i => PowerSeries.coeff n (separatedPrefixSeries (K := ZMod 7) i)) ∧
    ¬ (∃ d : ℕ, 0 < d ∧ ∀ i : Bool,
      KernelFirstDegree (separatedPrefixKernel (K := ZMod 7) i) d ∨
        (1 - Polynomial.X : Polynomial (ZMod 7)) ∣
          1 * separatedPrefixKernel i ^
            (1 - Polynomial.X : Polynomial (ZMod 7)).natDegree) := by
  refine ⟨?_, separatedPrefixSeries_seven_positive_lower_density,
    separatedPrefixSeries_simultaneous_zeroBlocks,
    separatedPrefixKernel_no_common_compatibility⟩
  intro i
  refine ⟨separatedPrefixKernel_coeff_zero i, ?_⟩
  have h := separatedPrefixKernel_natDegree_le (K := ZMod 7) i
  simp only [ZMod.card]
  omega

end IndependentZeroBlocks
