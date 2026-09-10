import SierpinskiFormal.ProductPrefixes
import SierpinskiFormal.SupportCounting

set_option autoImplicit false

namespace IndependentZeroBlocks
open SierpinskiFormal
open scoped BigOperators

private theorem sum_range_blocks_nat (f : ℕ → ℕ) (q M : ℕ) :
    (∑ n ∈ Finset.range (q * M), f n) =
      ∑ m ∈ Finset.range M, ∑ d ∈ Finset.range q, f (q * m + d) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- A polynomial occupying distinct residues modulo the dilation factor
has an exact support count: no cancellation between tail copies is possible. -/
theorem supportCount_polynomial_mul_dilate_blocks
    {K : Type*} [Field K] (q : ℕ) (hq : 0 < q)
    (H : Polynomial K) (hH : H.natDegree < q)
    (T : PowerSeries K) (M : ℕ) :
    supportCount ((H : PowerSeries K) * dilate q T) (q * M) =
      H.support.card * supportCount T M := by
  classical
  have hfilter : (Finset.range q).filter (fun d => H.coeff d ≠ 0) = H.support := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_range, Polynomial.mem_support_iff]
    exact and_iff_right_of_imp (fun hd =>
      (Polynomial.le_natDegree_of_ne_zero hd).trans_lt hH)
  unfold supportCount
  rw [Finset.card_filter, sum_range_blocks_nat]
  calc
    (∑ m ∈ Finset.range M, ∑ d ∈ Finset.range q,
        if PowerSeries.coeff (q * m + d) ((H : PowerSeries K) * dilate q T) ≠ 0
        then 1 else 0) =
      ∑ m ∈ Finset.range M,
        H.support.card * (if PowerSeries.coeff m T ≠ 0 then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro m hm
      have hterm : ∀ d ∈ Finset.range q,
          PowerSeries.coeff (q * m + d) ((H : PowerSeries K) * dilate q T) =
            PowerSeries.coeff m T * H.coeff d := by
        intro d hd
        exact coeff_polynomial_mul_dilate q hq H hH T m d (Finset.mem_range.mp hd)
      trans ∑ d ∈ Finset.range q, if PowerSeries.coeff m T * H.coeff d ≠ 0 then 1 else 0
      · apply Finset.sum_congr rfl
        intro d hd
        rw [hterm d hd]
      by_cases ht : PowerSeries.coeff m T = 0
      · simp [ht]
      · simp only [mul_ne_zero_iff]
        simp only [ne_eq, ht, not_false_eq_true, true_and, if_true, mul_one]
        rw [← Finset.card_filter]
        exact congrArg Finset.card hfilter
    _ = H.support.card * ((Finset.range M).filter
        (fun n => PowerSeries.coeff n T ≠ 0)).card := by
      rw [← Finset.mul_sum, ← Finset.card_filter]

end IndependentZeroBlocks
