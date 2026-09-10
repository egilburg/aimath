import SierpinskiFormal.BoundarySeriesHolomorphic

/-! # Uniformly bounded Banach-valued word series are analytic

This includes bounded families of boundary branches and bounded linear
functionals on those families, allowing analytic moments without interchanging
an uncontrolled family of scalar derivatives.
-/

noncomputable section
open Filter Set Topology
open scoped BigOperators ENNReal
namespace Sierpinski

variable {D F : Type*} [Fintype D] [NormedAddCommGroup F] [NormedSpace ℂ F]

def wordMultilinearTerm (c : List D → F) {n : ℕ} (x : Fin n → D) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n ↦ BoundaryL1 D) F :=
  ((ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin n) ℂ).compContinuousLinearMap
    (fun k ↦ PiLp.proj 1 (fun _ : D ↦ ℂ) (x k))).smulRight (c (List.ofFn x))

@[simp] theorem wordMultilinearTerm_apply (c : List D → F) {n : ℕ}
    (x : Fin n → D) (v : Fin n → BoundaryL1 D) :
    wordMultilinearTerm c x v = (∏ k, v k (x k)) • c (List.ofFn x) := by
  simp [wordMultilinearTerm, ContinuousMultilinearMap.compContinuousLinearMap_apply]

def wordFormalSeries (c : List D → F) : FormalMultilinearSeries ℂ (BoundaryL1 D) F :=
  fun n ↦ ∑ x : Fin n → D, wordMultilinearTerm c x

theorem norm_wordFormalSeries_apply_le (c : List D → F) (hc : ∀ w, ‖c w‖ ≤ 1)
    (n : ℕ) (v : Fin n → BoundaryL1 D) :
    ‖wordFormalSeries c n v‖ ≤ ∏ k, ‖v k‖ := by
  classical
  simp only [wordFormalSeries, ContinuousMultilinearMap.sum_apply]
  calc
    ‖∑ x : Fin n → D, wordMultilinearTerm c x v‖ ≤
        ∑ x : Fin n → D, ‖wordMultilinearTerm c x v‖ := norm_sum_le _ _
    _ ≤ ∑ x : Fin n → D, ∏ k, ‖v k (x k)‖ := by
      apply Finset.sum_le_sum
      intro x _
      rw [wordMultilinearTerm_apply, norm_smul, norm_prod]
      exact mul_le_of_le_one_right (Finset.prod_nonneg fun k _ ↦ norm_nonneg _) (hc _)
    _ = ∏ k, ∑ a : D, ‖v k a‖ := by rw [Fintype.prod_sum]
    _ = ∏ k, ‖v k‖ := by
      apply Finset.prod_congr rfl
      intro k _
      exact (PiLp.norm_eq_of_L1 (v k)).symm

theorem norm_wordFormalSeries_le (c : List D → F) (hc : ∀ w, ‖c w‖ ≤ 1) (n : ℕ) :
    ‖wordFormalSeries c n‖ ≤ 1 := by
  apply ContinuousMultilinearMap.opNorm_le_bound zero_le_one
  intro v
  simpa using norm_wordFormalSeries_apply_le c hc n v

theorem one_le_wordFormalSeries_radius (c : List D → F) (hc : ∀ w, ‖c w‖ ≤ 1) :
    (1 : ℝ≥0∞) ≤ (wordFormalSeries c).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr ↦ ?_
  have hrR : ‖(r : ℝ)‖ < 1 := by
    rw [Real.norm_of_nonneg r.coe_nonneg]
    exact NNReal.coe_lt_one.mpr (by simpa using hr)
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  apply Summable.of_nonneg_of_le
    (fun n ↦ mul_nonneg (norm_nonneg _) (pow_nonneg r.coe_nonneg n))
    (fun n ↦ (mul_le_mul_of_nonneg_right (norm_wordFormalSeries_le c hc n)
      (pow_nonneg r.coe_nonneg n)).trans_eq (one_mul _))
  exact summable_geometric_of_norm_lt_one hrR

def banachWordSeries (c : List D → F) (p : D → ℂ) : F :=
  ∑' n : ℕ, ∑ x : Fin n → D, (∏ k, p (x k)) • c (List.ofFn x)

theorem wordFormalSeries_sum (c : List D → F) (p : BoundaryL1 D) :
    (wordFormalSeries c).sum p = banachWordSeries c p := by
  unfold FormalMultilinearSeries.sum banachWordSeries wordFormalSeries
  simp only [ContinuousMultilinearMap.sum_apply, wordMultilinearTerm_apply]

variable [CompleteSpace F]

theorem analyticAt_banachWordSeries_L1 (c : List D → F) (hc : ∀ w, ‖c w‖ ≤ 1)
    (p : BoundaryL1 D) (hp : ‖p‖ < 1) :
    AnalyticAt ℂ (fun z : BoundaryL1 D ↦ banachWordSeries c z) p := by
  have hr := one_le_wordFormalSeries_radius c hc
  have hpos : 0 < (wordFormalSeries c).radius := lt_of_lt_of_le zero_lt_one hr
  have hm : p ∈ EMetric.ball 0 (wordFormalSeries c).radius := by
    change p ∈ Metric.eball 0 (wordFormalSeries c).radius
    rw [mem_eball_zero_iff, ← ofReal_norm_eq_enorm]
    exact lt_of_lt_of_le (ENNReal.ofReal_lt_one.mpr hp) hr
  have h := ((wordFormalSeries c).hasFPowerSeriesOnBall hpos).analyticAt_of_mem hm
  simpa only [funext (wordFormalSeries_sum c)] using h

theorem analyticAt_banachWordSeries (c : List D → F) (hc : ∀ w, ‖c w‖ ≤ 1)
    (p : D → ℂ) (hp : finiteL1Norm p < 1) :
    AnalyticAt ℂ (banachWordSeries c) p := by
  let E : BoundaryL1 D ≃L[ℂ] (D → ℂ) := PiLp.continuousLinearEquiv 1 ℂ (fun _ : D ↦ ℂ)
  have hpn : ‖E.symm p‖ < 1 := by
    simpa [PiLp.norm_eq_of_L1, E, finiteL1Norm] using hp
  have h := (analyticAt_banachWordSeries_L1 c hc (E.symm p) hpn).comp (E.symm.analyticAt p)
  convert h using 1
  rfl

end Sierpinski
