import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.NormedSpace.FunctionSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Normally convergent boundary-word series

This file isolates the analytic estimate behind the boundary series used in the
higher-rank renewal argument.  The series is grouped by the two word lengths,
so every summand is a finite polynomial.  Its norm is dominated by the product
of two geometric series in the finite `ℓ¹` norm of the parameter.
-/

open scoped BigOperators Topology
open Set Filter

namespace Sierpinski

section

variable {D : Type*} [Fintype D]

/-- The finite `ℓ¹` norm of a complex weight vector. -/
noncomputable def finiteL1Norm (p : D → ℂ) : ℝ := ∑ a, ‖p a‖

/-- The monomial belonging to a word represented as a map out of `Fin n`. -/
noncomputable def finWordMonomial (p : D → ℂ) {n : ℕ} (x : Fin n → D) : ℂ :=
  ∏ k, p (x k)

/-- The contribution of all pairs of words having lengths `i` and `j`. -/
noncomputable def boundaryBidegree
    (c : List D → List D → ℂ) (i j : ℕ) (p : D → ℂ) : ℂ :=
  ∑ x : Fin i → D, ∑ z : Fin j → D,
    c (List.ofFn x) (List.ofFn z) * finWordMonomial p x * finWordMonomial p z

/-- The boundary series, indexed by the two word lengths. -/
noncomputable def boundarySeries
    (c : List D → List D → ℂ) (p : D → ℂ) : ℂ :=
  ∑' ij : ℕ × ℕ, boundaryBidegree c ij.1 ij.2 p

lemma finiteL1Norm_nonneg (p : D → ℂ) : 0 ≤ finiteL1Norm p := by
  exact Finset.sum_nonneg fun _ _ ↦ norm_nonneg _

lemma sum_finWordMonomial_norm (p : D → ℂ) (n : ℕ) :
    (∑ x : Fin n → D, ∏ k, ‖p (x k)‖) = finiteL1Norm p ^ n := by
  simpa [finiteL1Norm] using (Fintype.sum_pow (fun a : D ↦ ‖p a‖) n).symm

/-- The fundamental normal-convergence estimate. -/
theorem norm_boundaryBidegree_le
    (c : List D → List D → ℂ) (hc : ∀ x z, ‖c x z‖ ≤ 1)
    (i j : ℕ) (p : D → ℂ) :
    ‖boundaryBidegree c i j p‖ ≤ finiteL1Norm p ^ i * finiteL1Norm p ^ j := by
  classical
  calc
    ‖boundaryBidegree c i j p‖
        ≤ ∑ x : Fin i → D, ‖∑ z : Fin j → D,
            c (List.ofFn x) (List.ofFn z) * finWordMonomial p x * finWordMonomial p z‖ := by
      exact norm_sum_le _ _
    _ ≤ ∑ x : Fin i → D, ∑ z : Fin j → D,
          ‖c (List.ofFn x) (List.ofFn z) * finWordMonomial p x * finWordMonomial p z‖ := by
      exact Finset.sum_le_sum fun _ _ ↦ norm_sum_le _ _
    _ ≤ ∑ x : Fin i → D, ∑ z : Fin j → D,
          (∏ k, ‖p (x k)‖) * (∏ k, ‖p (z k)‖) := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro z hz
      simp only [norm_mul, finWordMonomial, norm_prod]
      have hxnonneg : 0 ≤ ∏ k, ‖p (x k)‖ := Finset.prod_nonneg fun _ _ ↦ norm_nonneg _
      have hznonneg : 0 ≤ ∏ k, ‖p (z k)‖ := Finset.prod_nonneg fun _ _ ↦ norm_nonneg _
      exact mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_left hxnonneg (hc (List.ofFn x) (List.ofFn z))) hznonneg
    _ = finiteL1Norm p ^ i * finiteL1Norm p ^ j := by
      rw [← Finset.sum_mul_sum]
      rw [sum_finWordMonomial_norm, sum_finWordMonomial_norm]

/-- Each fixed-length contribution is a polynomial, hence analytic. -/
theorem analyticAt_boundaryBidegree
    (c : List D → List D → ℂ) (i j : ℕ) (p : D → ℂ) :
    AnalyticAt ℂ (boundaryBidegree c i j) p := by
  classical
  unfold boundaryBidegree
  have hinner (x : Fin i → D) : AnalyticAt ℂ (fun q : D → ℂ ↦
      ∑ z : Fin j → D,
        c (List.ofFn x) (List.ofFn z) * finWordMonomial q x * finWordMonomial q z) p := by
    have hterm (z : Fin j → D) : AnalyticAt ℂ (fun q : D → ℂ ↦
        c (List.ofFn x) (List.ofFn z) * finWordMonomial q x * finWordMonomial q z) p := by
      have hx' : AnalyticAt ℂ (fun q : D → ℂ ↦ finWordMonomial q x) p := by
        unfold finWordMonomial
        convert! Finset.analyticAt_prod Finset.univ (fun k _ ↦
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : D ↦ ℂ) (x k)).analyticAt p) using 1
        funext q
        simp only [Finset.prod_apply]
        apply Finset.prod_congr rfl
        intro k hk
        rfl
      have hz' : AnalyticAt ℂ (fun q : D → ℂ ↦ finWordMonomial q z) p := by
        unfold finWordMonomial
        convert! Finset.analyticAt_prod Finset.univ (fun k _ ↦
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : D ↦ ℂ) (z k)).analyticAt p) using 1
        funext q
        simp only [Finset.prod_apply]
        apply Finset.prod_congr rfl
        intro k hk
        rfl
      exact (analyticAt_const.fun_mul hx').fun_mul hz'
    convert! Finset.analyticAt_sum Finset.univ (fun z _ ↦ hterm z) using 1
    funext q
    simp only [Finset.sum_apply]
  convert! Finset.analyticAt_sum Finset.univ (fun x _ ↦ hinner x) using 1
  funext q
  simp only [Finset.sum_apply]

/-- The product of the two geometric majorants is summable. -/
lemma summable_boundaryMajorant {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun ij : ℕ × ℕ ↦ r ^ ij.1 * r ^ ij.2) := by
  exact (summable_geometric_of_lt_one hr0 hr1).mul_of_nonneg
    (summable_geometric_of_lt_one hr0 hr1) (fun _ ↦ pow_nonneg hr0 _)
    (fun _ ↦ pow_nonneg hr0 _)

/-- Absolute convergence at every point of the open finite `ℓ¹` ball. -/
theorem summable_boundaryBidegree
    (c : List D → List D → ℂ) (hc : ∀ x z, ‖c x z‖ ≤ 1)
    (p : D → ℂ) (hp : finiteL1Norm p < 1) :
    Summable (fun ij : ℕ × ℕ ↦ boundaryBidegree c ij.1 ij.2 p) := by
  apply Summable.of_norm_bounded
    (summable_boundaryMajorant (finiteL1Norm_nonneg p) hp)
  intro ij
  exact norm_boundaryBidegree_le c hc ij.1 ij.2 p

/-- The boundary series is bounded by the square of the geometric-series sum. -/
theorem norm_boundarySeries_le
    (c : List D → List D → ℂ) (hc : ∀ x z, ‖c x z‖ ≤ 1)
    (p : D → ℂ) (hp : finiteL1Norm p < 1) :
    ‖boundarySeries c p‖ ≤ (1 - finiteL1Norm p)⁻¹ ^ 2 := by
  let r := finiteL1Norm p
  have hr0 : 0 ≤ r := finiteL1Norm_nonneg p
  have hgeom : Summable (fun n : ℕ ↦ r ^ n) :=
    summable_geometric_of_lt_one hr0 hp
  have hmajor : Summable (fun ij : ℕ × ℕ ↦ r ^ ij.1 * r ^ ij.2) :=
    summable_boundaryMajorant hr0 hp
  have hnorm : Summable (fun ij : ℕ × ℕ ↦
      ‖boundaryBidegree c ij.1 ij.2 p‖) :=
    Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun ij ↦
      norm_boundaryBidegree_le c hc ij.1 ij.2 p) hmajor
  calc
    ‖boundarySeries c p‖ ≤ ∑' ij : ℕ × ℕ, ‖boundaryBidegree c ij.1 ij.2 p‖ :=
      norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' ij : ℕ × ℕ, r ^ ij.1 * r ^ ij.2 :=
      hnorm.tsum_le_tsum (fun ij ↦ norm_boundaryBidegree_le c hc ij.1 ij.2 p) hmajor
    _ = (∑' n : ℕ, r ^ n) * (∑' n : ℕ, r ^ n) :=
      (hgeom.tsum_mul_tsum hgeom hmajor).symm
    _ = (1 - r)⁻¹ * (1 - r)⁻¹ := by
      rw [tsum_geometric_of_lt_one hr0 hp]
    _ = (1 - finiteL1Norm p)⁻¹ ^ 2 := by simp [r, pow_two]

/-- Local normal convergence on every closed `ℓ¹` subball of radius `r < 1`. -/
theorem tendstoUniformlyOn_boundarySeries
    (c : List D → List D → ℂ) (hc : ∀ x z, ‖c x z‖ ≤ 1)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    TendstoUniformlyOn
      (fun s : Finset (ℕ × ℕ) ↦ fun p : D → ℂ ↦
        ∑ ij ∈ s, boundaryBidegree c ij.1 ij.2 p)
      (boundarySeries c) atTop {p | finiteL1Norm p ≤ r} := by
  apply tendstoUniformlyOn_tsum (summable_boundaryMajorant hr0 hr1)
  intro ij p hp
  apply (norm_boundaryBidegree_le c hc ij.1 ij.2 p).trans
  exact mul_le_mul
    (pow_le_pow_left₀ (finiteL1Norm_nonneg p) hp ij.1)
    (pow_le_pow_left₀ (finiteL1Norm_nonneg p) hp ij.2)
    (pow_nonneg (finiteL1Norm_nonneg p) _)
    (pow_nonneg hr0 _)

/-- Every point of the open `ℓ¹` ball lies in a larger closed subball on which
the boundary series converges normally. -/
theorem locallyNormallyConvergent_boundarySeries
    (c : List D → List D → ℂ) (hc : ∀ x z, ‖c x z‖ ≤ 1)
    (p : D → ℂ) (hp : finiteL1Norm p < 1) :
    ∃ r : ℝ, finiteL1Norm p < r ∧ r < 1 ∧
      TendstoUniformlyOn
        (fun s : Finset (ℕ × ℕ) ↦ fun q : D → ℂ ↦
          ∑ ij ∈ s, boundaryBidegree c ij.1 ij.2 q)
        (boundarySeries c) atTop {q | finiteL1Norm q ≤ r} := by
  refine ⟨(finiteL1Norm p + 1) / 2, by linarith, by linarith, ?_⟩
  apply tendstoUniformlyOn_boundarySeries c hc
  · have := finiteL1Norm_nonneg p
    linarith
  · linarith

end

end Sierpinski
