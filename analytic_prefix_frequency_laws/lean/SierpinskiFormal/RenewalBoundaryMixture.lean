import SierpinskiFormal.RadixLogDensityTransfer
import Mathlib.Analysis.Normed.Group.Tannery

/-! # Summable boundary mixtures with the original length clock

Finite boundary words cost a fixed number of letters. This module proves
that these delays disappear in Cesaro means and that a summable family of
bounded central sequences can be mixed without losing its computed means.
-/

noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace IndependentZeroBlocks

def delayedSequence (d : ℕ) (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  if d ≤ n then c (n - d) else 0

theorem norm_delayedSequence_le_one (d : ℕ) (c : ℕ → ℝ)
    (hc : ∀ n, ‖c n‖ ≤ 1) (n : ℕ) : ‖delayedSequence d c n‖ ≤ 1 := by
  unfold delayedSequence
  split_ifs
  · exact hc _
  · simp

theorem realCesaroMean_delayed_add (d N : ℕ) (c : ℕ → ℝ) :
    realCesaroMean (delayedSequence d c) (N + d) =
      (N : ℝ) / (N + d : ℕ) * realCesaroMean c N := by
  have hsum : (∑ n ∈ Finset.range (N + d), delayedSequence d c n) =
      ∑ n ∈ Finset.range N, c n := by
    rw [Nat.add_comm N d, Finset.sum_range_add]
    have hhead : (∑ n ∈ Finset.range d, delayedSequence d c n) = 0 := by
      apply Finset.sum_eq_zero
      intro n hn
      simp [delayedSequence, Nat.not_le.mpr (Finset.mem_range.mp hn)]
    rw [hhead, zero_add]
    apply Finset.sum_congr rfl
    intro n _
    simp [delayedSequence]
  unfold realCesaroMean
  rw [hsum]
  by_cases hN : N = 0
  · simp [hN]
  · have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
    field_simp

theorem tendsto_realCesaroMean_delayed (d : ℕ) (c : ℕ → ℝ) (L : ℝ)
    (hc : Tendsto (realCesaroMean c) atTop (𝓝 L)) :
    Tendsto (realCesaroMean (delayedSequence d c)) atTop (𝓝 L) := by
  apply (tendsto_add_atTop_iff_nat d).mp
  have hratio : Tendsto (fun N : ℕ ↦ (N : ℝ) / (N + d : ℕ)) atTop (𝓝 1) := by
    simpa only [Nat.cast_add] using tendsto_natCast_div_add_atTop (d : ℝ)
  simpa only [realCesaroMean_delayed_add, one_mul] using hratio.mul hc

theorem norm_realCesaroMean_le_one (c : ℕ → ℝ)
    (hc : ∀ n, ‖c n‖ ≤ 1) (N : ℕ) : ‖realCesaroMean c N‖ ≤ 1 := by
  by_cases hN : N = 0
  · simp [hN, realCesaroMean]
  · have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
    rw [realCesaroMean, norm_div, Real.norm_natCast]
    apply (div_le_one hNr).mpr
    exact (norm_sum_le _ _).trans (by simpa using
      (Finset.sum_le_sum (s := Finset.range N) (fun n _ ↦ hc n)))

variable {I : Type*}

def renewalBoundaryMixture (w : I → ℝ) (delay : I → ℕ)
    (c : I → ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑' i, w i * delayedSequence (delay i) (c i) N

theorem summable_weighted_delayedSequence
    (w : I → ℝ) (hw : Summable w) (hw0 : ∀ i, 0 ≤ w i)
    (delay : I → ℕ) (c : I → ℕ → ℝ) (hc : ∀ i n, ‖c i n‖ ≤ 1) (N : ℕ) :
    Summable (fun i ↦ w i * delayedSequence (delay i) (c i) N) := by
  apply hw.of_norm_bounded
  intro i
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hw0 i)]
  exact (mul_le_mul_of_nonneg_left
    (norm_delayedSequence_le_one (delay i) (c i) (hc i) N) (hw0 i)).trans_eq
      (mul_one _)

theorem realCesaroMean_renewalBoundaryMixture
    (w : I → ℝ) (hw : Summable w) (hw0 : ∀ i, 0 ≤ w i)
    (delay : I → ℕ) (c : I → ℕ → ℝ) (hc : ∀ i n, ‖c i n‖ ≤ 1) (N : ℕ) :
    realCesaroMean (renewalBoundaryMixture w delay c) N =
      ∑' i, w i * realCesaroMean (delayedSequence (delay i) (c i)) N := by
  have hs (n : ℕ) := summable_weighted_delayedSequence w hw hw0 delay c hc n
  unfold realCesaroMean renewalBoundaryMixture
  simp_rw [← mul_div_assoc, Finset.mul_sum]
  rw [tsum_div_const]
  congr 1
  exact (Summable.tsum_finsetSum (s := Finset.range N) (fun n _ ↦ hs n)).symm

/-- The actual delayed mixture has the mixture of the central Cesaro
limits. No independence between a return matrix and its length is assumed. -/
theorem tendsto_realCesaroMean_renewalBoundaryMixture
    (w : I → ℝ) (hw : Summable w) (hw0 : ∀ i, 0 ≤ w i)
    (delay : I → ℕ) (c : I → ℕ → ℝ) (L : I → ℝ)
    (hc : ∀ i n, ‖c i n‖ ≤ 1)
    (hL : ∀ i, Tendsto (realCesaroMean (c i)) atTop (𝓝 (L i))) :
    Tendsto (realCesaroMean (renewalBoundaryMixture w delay c)) atTop
      (𝓝 (∑' i, w i * L i)) := by
  change Tendsto (fun N ↦ realCesaroMean (renewalBoundaryMixture w delay c) N) _ _
  simp_rw [realCesaroMean_renewalBoundaryMixture w hw hw0 delay c hc]
  apply tendsto_tsum_of_dominated_convergence hw
  · intro i
    exact (tendsto_realCesaroMean_delayed (delay i) (c i) (L i) (hL i)).const_mul _
  · filter_upwards with N i
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hw0 i)]
    exact (mul_le_mul_of_nonneg_left
      (norm_realCesaroMean_le_one _ (norm_delayedSequence_le_one _ _ (hc i)) N)
      (hw0 i)).trans_eq (mul_one _)

end IndependentZeroBlocks
