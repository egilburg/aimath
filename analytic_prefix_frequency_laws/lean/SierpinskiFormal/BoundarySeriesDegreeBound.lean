import SierpinskiFormal.BoundarySeriesAnalytic
import Mathlib.Data.Finset.NatAntidiagonal

/-!
# Total-degree form of the boundary series

This module defines the homogeneous terms obtained by grouping bidegrees
of the same total degree and proves their polynomial growth bound.
It does not identify the sum with a multilinear power series or prove holomorphy.
-/

noncomputable section

set_option maxHeartbeats 800000

open scoped BigOperators Topology
open Set Filter

namespace Sierpinski

variable {D : Type*} [Fintype D]

/-- The homogeneous boundary contribution of total degree `n`. -/
noncomputable def boundaryTotalDegree
    (c : List D → List D → ℂ) (n : ℕ) (p : D → ℂ) : ℂ :=
  ∑ ij ∈ Finset.antidiagonal n, boundaryBidegree c ij.1 ij.2 p

/-- The total-degree term has only `n+1` bidegrees, so its norm is bounded by
`(n+1) r^n`. -/
theorem norm_boundaryTotalDegree_le
    (c : List D → List D → ℂ) (hc : ∀ x z, ‖c x z‖ ≤ 1)
    (n : ℕ) (p : D → ℂ) :
    ‖boundaryTotalDegree c n p‖ ≤
      (n + 1 : ℝ) * finiteL1Norm p ^ n := by
  unfold boundaryTotalDegree
  calc
    ‖∑ ij ∈ Finset.antidiagonal n,
        boundaryBidegree c ij.1 ij.2 p‖ ≤
        ∑ ij ∈ Finset.antidiagonal n,
          ‖boundaryBidegree c ij.1 ij.2 p‖ := norm_sum_le _ _
    _ ≤ ∑ ij ∈ Finset.antidiagonal n,
          finiteL1Norm p ^ n := by
      apply Finset.sum_le_sum
      intro ij hij
      have hadd : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
      calc
        ‖boundaryBidegree c ij.1 ij.2 p‖ ≤
            finiteL1Norm p ^ ij.1 * finiteL1Norm p ^ ij.2 :=
          norm_boundaryBidegree_le c hc ij.1 ij.2 p
        _ = finiteL1Norm p ^ n := by rw [← pow_add, hadd]
    _ = (n + 1 : ℝ) * finiteL1Norm p ^ n := by
      rw [Finset.sum_const, Finset.Nat.card_antidiagonal]
      simp

end Sierpinski
