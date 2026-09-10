import SierpinskiFormal.BoundarySeriesDegreeBound
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Normed.Lp.PiLp

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2000000

open scoped BigOperators Topology NNReal ENNReal

namespace Sierpinski

variable {D : Type*} [Fintype D]

abbrev BoundaryL1 (D : Type*) [Fintype D] := PiLp 1 (fun _ : D ↦ ℂ)

/-- One word-pair coefficient as a multilinear map on the finite `ℓ¹` space. -/
noncomputable def boundaryMultilinearTerm
    (c : List D → List D → ℂ) {i j : ℕ}
    (x : Fin i → D) (z : Fin j → D) :
    ContinuousMultilinearMap ℂ (fun _ : Fin (i + j) ↦ BoundaryL1 D) ℂ :=
  c (List.ofFn x) (List.ofFn z) •
    (ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin (i + j)) ℂ).compContinuousLinearMap
      (fun k ↦ PiLp.proj 1 (fun _ : D ↦ ℂ) (Fin.addCases x z k))

@[simp] theorem boundaryMultilinearTerm_apply
    (c : List D → List D → ℂ) {i j : ℕ}
    (x : Fin i → D) (z : Fin j → D)
    (v : Fin (i + j) → BoundaryL1 D) :
    boundaryMultilinearTerm c x z v =
      c (List.ofFn x) (List.ofFn z) *
        ∏ k, v k (Fin.addCases x z k) := by
  simp [boundaryMultilinearTerm, ContinuousMultilinearMap.compContinuousLinearMap_apply]

/-- The multilinear coefficient belonging to one split `i+j=n`. -/
noncomputable def boundarySplitCoefficient
    (c : List D → List D → ℂ) (n : ℕ)
    (ij : {ij : ℕ × ℕ // ij ∈ Finset.antidiagonal n}) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n ↦ BoundaryL1 D) ℂ :=
    ContinuousMultilinearMap.domDomCongr
      (Fin.castOrderIso (Finset.mem_antidiagonal.mp ij.2))
      (∑ x : Fin ij.1.1 → D, ∑ z : Fin ij.1.2 → D,
        boundaryMultilinearTerm c x z)

/-- The degree-`n` multilinear coefficient, grouped by all splits `i+j=n`. -/
noncomputable def boundaryFormalCoefficient
    (c : List D → List D → ℂ) (n : ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n ↦ BoundaryL1 D) ℂ :=
  ∑ ij, boundarySplitCoefficient c n ij

/-- Formal multilinear series of the boundary expansion on the finite `ℓ¹` space. -/
noncomputable def boundaryFormalSeries
    (c : List D → List D → ℂ) :
    FormalMultilinearSeries ℂ (BoundaryL1 D) ℂ :=
  boundaryFormalCoefficient c

/-- Diagonal evaluation of the multilinear coefficient is the homogeneous
total-degree boundary term. -/
theorem boundaryFormalCoefficient_diag
    (c : List D → List D → ℂ) (n : ℕ) (p : BoundaryL1 D) :
    boundaryFormalCoefficient c n (fun _ ↦ p) =
      boundaryTotalDegree c n p := by
  classical
  simp only [boundaryFormalCoefficient, boundarySplitCoefficient, boundaryTotalDegree, boundaryBidegree,
    ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.domDomCongr_apply, Finset.sum_subtype,
    boundaryMultilinearTerm_apply, finWordMonomial]
  rw [← Finset.sum_subtype (Finset.antidiagonal n) (fun _ ↦ Iff.rfl)
    (fun ij ↦ ∑ x : Fin ij.1 → D, ∑ z : Fin ij.2 → D,
      c (List.ofFn x) (List.ofFn z) * ∏ k, p (Fin.addCases x z k))]
  apply Finset.sum_congr rfl
  intro ij hij
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro z hz
  rw [Fin.prod_univ_add]
  have hl : (fun i ↦ p (Fin.addCases x z (Fin.castAdd ij.2 i))) =
      (fun i ↦ p (x i)) := by
    funext i
    rw [Fin.addCases_left]
  have hr : (fun i ↦ p (Fin.addCases x z (Fin.natAdd ij.1 i))) =
      (fun i ↦ p (z i)) := by
    funext i
    rw [Fin.addCases_right]
  rw [hl, hr]
  ring

/-- A fixed bidegree coefficient has operator bound one in the `ℓ¹` norm. -/
theorem norm_boundaryMultilinearBidegree_apply_le
    (c : List D → List D → ℂ) (hc : ∀ x z, ‖c x z‖ ≤ 1)
    (i j : ℕ) (v : Fin (i + j) → BoundaryL1 D) :
    ‖(∑ x : Fin i → D, ∑ z : Fin j → D,
        boundaryMultilinearTerm c x z) v‖ ≤
      ∏ k, ‖v k‖ := by
  classical
  simp only [ContinuousMultilinearMap.sum_apply]
  calc
    ‖∑ x : Fin i → D, ∑ z : Fin j → D,
        boundaryMultilinearTerm c x z v‖ ≤
        ∑ x : Fin i → D, ‖∑ z : Fin j → D,
          boundaryMultilinearTerm c x z v‖ := norm_sum_le _ _
    _ ≤ ∑ x : Fin i → D, ∑ z : Fin j → D,
          ‖boundaryMultilinearTerm c x z v‖ := by
      exact Finset.sum_le_sum fun _ _ ↦ norm_sum_le _ _
    _ ≤ ∑ x : Fin i → D, ∑ z : Fin j → D,
        (∏ k : Fin i, ‖v (Fin.castAdd j k) (x k)‖) *
          ∏ k : Fin j, ‖v (Fin.natAdd i k) (z k)‖ := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.sum_le_sum
      intro z hz
      rw [boundaryMultilinearTerm_apply, norm_mul, norm_prod, Fin.prod_univ_add]
      have hl : (fun k ↦ ‖v (Fin.castAdd j k) (Fin.addCases x z (Fin.castAdd j k))‖) =
          (fun k ↦ ‖v (Fin.castAdd j k) (x k)‖) := by
        funext k
        rw [Fin.addCases_left]
      have hr : (fun k ↦ ‖v (Fin.natAdd i k) (Fin.addCases x z (Fin.natAdd i k))‖) =
          (fun k ↦ ‖v (Fin.natAdd i k) (z k)‖) := by
        funext k
        rw [Fin.addCases_right]
      rw [hl, hr]
      apply mul_le_of_le_one_left
      · exact mul_nonneg
          (Finset.prod_nonneg fun (k : Fin i) _ ↦
            norm_nonneg (v (Fin.castAdd j k) (x k)))
          (Finset.prod_nonneg fun (k : Fin j) _ ↦
            norm_nonneg (v (Fin.natAdd i k) (z k)))
      · exact hc (List.ofFn x) (List.ofFn z)
    _ = (∑ x : Fin i → D, ∏ k : Fin i, ‖v (Fin.castAdd j k) (x k)‖) *
        (∑ z : Fin j → D, ∏ k : Fin j, ‖v (Fin.natAdd i k) (z k)‖) := by
      rw [Finset.sum_mul_sum]
    _ = (∏ k : Fin i, ∑ a : D, ‖v (Fin.castAdd j k) a‖) *
        (∏ k : Fin j, ∑ a : D, ‖v (Fin.natAdd i k) a‖) := by
      rw [Fintype.prod_sum, Fintype.prod_sum]
    _ = (∏ k : Fin i, ‖v (Fin.castAdd j k)‖) *
        ∏ k : Fin j, ‖v (Fin.natAdd i k)‖ := by
      congr 1
      · apply Finset.prod_congr rfl
        intro k hk
        exact (PiLp.norm_eq_of_L1 (v (Fin.castAdd j k))).symm
      · apply Finset.prod_congr rfl
        intro k hk
        exact (PiLp.norm_eq_of_L1 (v (Fin.natAdd i k))).symm
    _ = ∏ k, ‖v k‖ :=
      (Fin.prod_univ_add (fun k : Fin (i + j) ↦ ‖v k‖)).symm

/-- A fixed bidegree multilinear coefficient has operator norm at most one. -/
theorem norm_boundaryMultilinearBidegree_le
    (c : List D → List D → ℂ) (hc : ∀ x z, ‖c x z‖ ≤ 1)
    (i j : ℕ) :
    ‖∑ x : Fin i → D, ∑ z : Fin j → D,
        boundaryMultilinearTerm c x z‖ ≤ 1 := by
  apply ContinuousMultilinearMap.opNorm_le_bound zero_le_one
  intro v
  simpa only [one_mul] using norm_boundaryMultilinearBidegree_apply_le c hc i j v

/-- The degree-`n` coefficient has operator norm at most `n+1`. -/
theorem norm_boundaryFormalCoefficient_le
    (c : List D → List D → ℂ) (hc : ∀ x z, ‖c x z‖ ≤ 1)
    (n : ℕ) :
    ‖boundaryFormalCoefficient c n‖ ≤ (n + 1 : ℝ) := by
  classical
  unfold boundaryFormalCoefficient
  calc
    ‖∑ ij : {ij : ℕ × ℕ // ij ∈ Finset.antidiagonal n},
        boundarySplitCoefficient c n ij‖ ≤
        ∑ ij : {ij : ℕ × ℕ // ij ∈ Finset.antidiagonal n},
          ‖boundarySplitCoefficient c n ij‖ := norm_sum_le _ _
    _ ≤ ∑ _ij : {ij : ℕ × ℕ // ij ∈ Finset.antidiagonal n}, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro ij hij
      unfold boundarySplitCoefficient
      rw [ContinuousMultilinearMap.norm_domDomCongr]
      exact norm_boundaryMultilinearBidegree_le c hc ij.1.1 ij.1.2
    _ = (n + 1 : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe,
        Finset.Nat.card_antidiagonal]
      simp

/-- The boundary formal series has radius of convergence at least one in the
finite `ℓ¹` norm. -/
theorem one_le_boundaryFormalSeries_radius
    (c : List D → List D → ℂ) (hc : ∀ x z, ‖c x z‖ ≤ 1) :
    (1 : ℝ≥0∞) ≤ (boundaryFormalSeries c).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr ↦ ?_
  have hrNN : r < 1 := by
    simpa only [← ENNReal.coe_one, ENNReal.coe_lt_coe] using hr
  have hrR : ‖(r : ℝ)‖ < 1 := by
    rw [Real.norm_of_nonneg r.coe_nonneg]
    exact NNReal.coe_lt_one.mpr hrNN
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  apply Summable.of_nonneg_of_le
  · intro n
    exact mul_nonneg (norm_nonneg _) (pow_nonneg r.coe_nonneg _)
  · intro n
    exact mul_le_mul_of_nonneg_right (norm_boundaryFormalCoefficient_le c hc n)
      (pow_nonneg r.coe_nonneg _)
  · have hnat := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hrR
    have hgeom := summable_geometric_of_norm_lt_one hrR
    convert! hnat.add hgeom using 1
    ext n
    simp only [Nat.cast_add, Nat.cast_one, pow_one]
    ring

/-- The sum of the formal multilinear series is the sum of the homogeneous
total-degree terms. -/
theorem boundaryFormalSeries_sum_eq_totalDegrees
    (c : List D → List D → ℂ) (p : BoundaryL1 D) :
    (boundaryFormalSeries c).sum p =
      ∑' n : ℕ, boundaryTotalDegree c n p := by
  unfold FormalMultilinearSeries.sum boundaryFormalSeries
  apply tsum_congr
  intro n
  exact boundaryFormalCoefficient_diag c n p

/-- Absolute convergence permits regrouping the bidegree sum by total degree. -/
theorem tsum_boundaryTotalDegree_eq_boundarySeries
    (c : List D → List D → ℂ) (hc : ∀ x z, ‖c x z‖ ≤ 1)
    (p : BoundaryL1 D) (hp : finiteL1Norm p < 1) :
    (∑' n : ℕ, boundaryTotalDegree c n p) = boundarySeries c p := by
  classical
  let f : ℕ × ℕ → ℂ := fun ij ↦ boundaryBidegree c ij.1 ij.2 p
  have hf : Summable f := summable_boundaryBidegree c hc p hp
  have hfsigma : Summable (fun s : Σ n : ℕ, {ij : ℕ × ℕ //
      ij ∈ Finset.antidiagonal n} ↦ f s.2.1) :=
    Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff.mpr hf
  calc
    (∑' n : ℕ, boundaryTotalDegree c n p) =
        ∑' n : ℕ, ∑' ij : {ij : ℕ × ℕ // ij ∈ Finset.antidiagonal n},
          f ij.1 := by
      apply tsum_congr
      intro n
      rw [boundaryTotalDegree]
      rw [Finset.sum_subtype (Finset.antidiagonal n) (fun _ ↦ Iff.rfl)
        (fun ij ↦ boundaryBidegree c ij.1 ij.2 p)]
      exact (hasSum_fintype _).tsum_eq.symm
    _ = ∑' s : Σ n : ℕ, {ij : ℕ × ℕ // ij ∈ Finset.antidiagonal n},
          f s.2.1 := by
      symm
      exact hfsigma.tsum_sigma' (fun _ ↦ (hasSum_fintype _).summable)
    _ = ∑' ij : ℕ × ℕ, f ij :=
      Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq f
    _ = boundarySeries c p := rfl

/-- On the open `ℓ¹` unit ball, the formal multilinear series sums to the
boundary series. -/
theorem boundaryFormalSeries_sum_eq_boundarySeries
    (c : List D → List D → ℂ) (hc : ∀ x z, ‖c x z‖ ≤ 1)
    (p : BoundaryL1 D) (hp : finiteL1Norm p < 1) :
    (boundaryFormalSeries c).sum p = boundarySeries c p :=
  (boundaryFormalSeries_sum_eq_totalDegrees c p).trans
    (tsum_boundaryTotalDegree_eq_boundarySeries c hc p hp)

/-- The boundary series is analytic on the open unit ball when its arguments
are equipped with the finite `ℓ¹` norm. -/
theorem analyticAt_boundarySeries_L1
    (c : List D → List D → ℂ) (hc : ∀ x z, ‖c x z‖ ≤ 1)
    (p : BoundaryL1 D) (hp : finiteL1Norm p < 1) :
    AnalyticAt ℂ (fun q : BoundaryL1 D ↦ boundarySeries c q) p := by
  have hradius : (0 : ℝ≥0∞) < (boundaryFormalSeries c).radius :=
    lt_of_lt_of_le zero_lt_one (one_le_boundaryFormalSeries_radius c hc)
  have hp_mem : p ∈ EMetric.ball 0 (boundaryFormalSeries c).radius := by
    change p ∈ Metric.eball 0 (boundaryFormalSeries c).radius
    rw [mem_eball_zero_iff, ← ofReal_norm_eq_enorm,
      PiLp.norm_eq_of_L1]
    exact lt_of_lt_of_le (ENNReal.ofReal_lt_one.mpr hp)
      (one_le_boundaryFormalSeries_radius c hc)
  have hformal : AnalyticAt ℂ (boundaryFormalSeries c).sum p :=
    ((boundaryFormalSeries c).hasFPowerSeriesOnBall hradius).analyticAt_of_mem hp_mem
  have hp_metric : p ∈ Metric.ball (0 : BoundaryL1 D) 1 := by
    rw [Metric.mem_ball, dist_zero_right, PiLp.norm_eq_of_L1]
    exact hp
  have hball_nhds : Metric.ball (0 : BoundaryL1 D) 1 ∈ 𝓝 p :=
    Metric.isOpen_ball.mem_nhds hp_metric
  have hevent : ∀ᶠ (q : BoundaryL1 D) in 𝓝 p,
      finiteL1Norm (q : D → ℂ) < 1 := by
    filter_upwards [hball_nhds] with q hq
    rw [Metric.mem_ball, dist_zero_right, PiLp.norm_eq_of_L1] at hq
    exact hq
  apply hformal.congr
  filter_upwards [hevent] with q hq
  exact boundaryFormalSeries_sum_eq_boundarySeries c hc q hq

/-- Full multivariate Fréchet analyticity of the boundary series at every
point of the finite `ℓ¹` unit ball. -/
theorem analyticAt_boundarySeries_of_finiteL1Norm_lt_one
    (c : List D → List D → ℂ) (hc : ∀ x z, ‖c x z‖ ≤ 1)
    (p : D → ℂ) (hp : finiteL1Norm p < 1) :
    AnalyticAt ℂ (boundarySeries c) p := by
  let e : BoundaryL1 D ≃L[ℂ] (D → ℂ) :=
    PiLp.continuousLinearEquiv 1 ℂ (fun _ : D ↦ ℂ)
  have hp' : finiteL1Norm (e.symm p) < 1 := by
    simpa only [e, PiLp.continuousLinearEquiv_symm_apply] using hp
  have hL1 := analyticAt_boundarySeries_L1 c hc (e.symm p) hp'
  have hcomp := hL1.comp (e.symm.analyticAt p)
  convert! hcomp using 1

end Sierpinski
