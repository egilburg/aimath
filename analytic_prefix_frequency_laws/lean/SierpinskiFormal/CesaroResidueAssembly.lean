import SierpinskiFormal.RadixLogDensityTransfer
import Mathlib.Algebra.BigOperators.Field

/-! # Reassembling finitely many length residues

The full Cesaro limit is already known for stable weighted word predicates.
Consequently identification of its finitely many block-length residue means
requires only an exact identity on multiples of the block length.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace IndependentZeroBlocks

theorem sum_range_mul_residues (c : ℕ → ℝ) (ell N : ℕ) :
    (∑ n ∈ Finset.range (N * ell), c n) =
      ∑ k ∈ Finset.range N, ∑ s ∈ Finset.range ell, c (k * ell + s) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]

theorem realCesaroMean_mul_residues (c : ℕ → ℝ) (ell N : ℕ) :
    realCesaroMean c (N * ell) =
      (∑ s ∈ Finset.range ell, realCesaroMean (fun n ↦ c (n * ell + s)) N) /
        (ell : ℝ) := by
  simp only [realCesaroMean, sum_range_mul_residues, Nat.cast_mul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_div, div_div]

/-- Existing full Cesaro convergence and residue-wise computed limits
identify the full mean as their arithmetic average. -/
theorem cesaroLimit_eq_average_residueLimits (c : ℕ → ℝ) (ell : ℕ)
    (hell : 0 < ell) (L : ℝ) (m : Fin ell → ℝ)
    (hL : Tendsto (realCesaroMean c) atTop (𝓝 L))
    (hm : ∀ s : Fin ell,
      Tendsto (realCesaroMean (fun n ↦ c (n * ell + s))) atTop (𝓝 (m s))) :
    L = (∑ s : Fin ell, m s) / (ell : ℝ) := by
  have hsub : Tendsto (fun N : ℕ ↦ N * ell) atTop atTop :=
    (tendsto_id : Tendsto (fun N : ℕ ↦ N) atTop atTop).atTop_mul_const' hell
  have hfull := hL.comp hsub
  have hmean : Tendsto
      (fun N ↦ (∑ s : Fin ell, realCesaroMean (fun n ↦ c (n * ell + s)) N) /
        (ell : ℝ)) atTop (𝓝 ((∑ s : Fin ell, m s) / (ell : ℝ))) :=
    (tendsto_finset_sum Finset.univ (fun s _ ↦ hm s)).div_const _
  apply tendsto_nhds_unique hfull
  convert hmean using 1
  funext N
  simp only [Function.comp_apply]
  rw [realCesaroMean_mul_residues]
  congr 1
  exact (Fin.sum_univ_eq_sum_range _ ell).symm

end IndependentZeroBlocks
