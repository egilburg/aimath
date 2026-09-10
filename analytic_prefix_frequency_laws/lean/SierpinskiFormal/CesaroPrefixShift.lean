import SierpinskiFormal.RenewalBoundaryMixture

/-! # Discarding a fixed initial segment preserves a Cesaro limit -/

noncomputable section
open Filter Topology
open scoped BigOperators
namespace IndependentZeroBlocks

theorem tendsto_realCesaroMean_prefixShift (f : ℕ → ℝ) (a : ℝ)
    (hf : Tendsto (realCesaroMean f) atTop (𝓝 a)) (k : ℕ) :
    Tendsto (realCesaroMean (fun n ↦ f (k + n))) atTop (𝓝 a) := by
  have hr : Tendsto (fun N : ℕ ↦ ((N : ℝ) + k) / N) atTop (𝓝 1) := by
    simpa only [inv_div, inv_one] using
      (tendsto_natCast_div_add_atTop (k : ℝ)).inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have ht : Tendsto (fun N ↦ realCesaroMean f (N + k)) atTop (𝓝 a) :=
    (tendsto_add_atTop_iff_nat k).mpr hf
  have hhead : Tendsto (fun N : ℕ ↦ (∑ j ∈ Finset.range k, f j) / (N : ℝ))
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h := (hr.mul ht).sub hhead
  simp only [one_mul, sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hn : (N : ℝ) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
  have hnk : ((N + k : ℕ) : ℝ) ≠ 0 := (Nat.cast_pos.mpr (by omega : 0 < N + k)).ne'
  have hs : (∑ j ∈ Finset.range (N + k), f j) =
      (∑ j ∈ Finset.range k, f j) + (∑ j ∈ Finset.range N, f (k + j)) := by
    rw [Nat.add_comm N k, Finset.sum_range_add]
  dsimp [realCesaroMean]
  rw [hs]
  push_cast at hnk ⊢
  field_simp
  <;> ring

end IndependentZeroBlocks
