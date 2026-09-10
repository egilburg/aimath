import SierpinskiFormal.SourceAtomicAnalytic

/-! # Joint holomorphy of finite-state-source exponential transforms -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter MeasureTheory Set Topology
open scoped BigOperators
namespace IndependentZeroBlocks
namespace FiniteStateSource

attribute [local instance] selectorMeasurableSpace selectorTopologicalSpace
variable {Q A J : Type*} [Fintype Q] [DecidableEq Q] [Fintype J]

def complexSourceSelectorWeights (S : FiniteStateSource Q A)
    (z : (r : Q) → S.Edge r → ℂ) (a : S.Selector) : ℂ :=
  ∏ r, normalizedComplexWeights (z r) (a r)

def complexifySourceWeights (S : FiniteStateSource Q A)
    (p : (r : Q) → S.Edge r → ℝ) : (r : Q) → S.Edge r → ℂ :=
  fun r e ↦ (p r e : ℂ)

theorem complexSourceSelectorWeights_ofReal (S : FiniteStateSource Q A)
    (p : (r : Q) → S.Edge r → ℝ) :
    S.complexSourceSelectorWeights (S.complexifySourceWeights p) =
      (fun a ↦ (sourceSelectorWeights (normalizedSourceWeights p) a : ℂ)) := by
  funext a
  simp [complexSourceSelectorWeights, complexifySourceWeights, sourceSelectorWeights,
    normalizedSourceWeights, normalizedRealWeights, normalizedComplexWeights,
    Complex.ofReal_prod, Complex.ofReal_div, Complex.ofReal_sum]

theorem analyticAt_complexSourceSelectorWeights (S : FiniteStateSource Q A)
    (z : (r : Q) → S.Edge r → ℂ) (hz : ∀ r, ∑ e, z r e ≠ 0) :
    AnalyticAt ℂ S.complexSourceSelectorWeights z := by
  apply AnalyticAt.pi
  intro a
  apply Finset.analyticAt_fun_prod
  intro r _
  have hr := (analyticAt_normalizedComplexWeights (z r) (hz r)).comp
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun r : Q ↦ S.Edge r → ℂ) r).analyticAt z)
  exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : S.Edge r ↦ ℂ) (a r)).analyticAt _).comp hr

def sourceComplexExpTransform (S : FiniteStateSource Q A) (h : List S.Selector)
    (m : J → BlockBranchCoefficients h)
    (hm : ∀ j s ξ u v, (m j s ξ u v : ℝ) ∈ Icc (0 : ℝ) 1)
    (z : (r : Q) → S.Edge r → ℂ) (t : J → ℂ) : ℂ :=
  blockComplexExpTransform h m hm (S.complexSourceSelectorWeights z) t

theorem analyticAt_sourceComplexExpTransform (S : FiniteStateSource Q A)
    (h : List S.Selector) (m : J → BlockBranchCoefficients h)
    (hm : ∀ j s ξ u v, (m j s ξ u v : ℝ) ∈ Icc (0 : ℝ) 1)
    (p : (r : Q) → S.Edge r → ℝ) (hp : ∀ r e, 0 < p r e) (t : J → ℂ) :
    AnalyticAt ℂ (fun zt : ((r : Q) → S.Edge r → ℂ) × (J → ℂ) ↦
      S.sourceComplexExpTransform h m hm zt.1 zt.2) (S.complexifySourceWeights p, t) := by
  have hsmall := finiteL1Norm_nonMarkerBlock_ofReal_lt_one
    (S.normalizedSelectorLaw p hp).weight (S.normalizedSelectorLaw_pos p hp)
    (S.normalizedSelectorLaw p hp).sum_eq_one h
  have hc := analyticAt_blockComplexExpTransform h m hm
    (S.complexSourceSelectorWeights (S.complexifySourceWeights p)) t (by
      rw [S.complexSourceSelectorWeights_ofReal p]
      exact hsmall)
  have hs : AnalyticAt ℂ S.complexSourceSelectorWeights (S.complexifySourceWeights p) :=
    S.analyticAt_complexSourceSelectorWeights _ (fun r ↦ complex_totalWeight_ne_zero (p r) (hp r))
  have hfst : AnalyticAt ℂ
      (Prod.fst : ((r : Q) → S.Edge r → ℂ) × (J → ℂ) → ((r : Q) → S.Edge r → ℂ))
      (S.complexifySourceWeights p, t) := analyticAt_fst
  have hmap := (hs.comp (f := Prod.fst) (x := (S.complexifySourceWeights p, t)) hfst).prod
    (analyticAt_snd : AnalyticAt ℂ
      (Prod.snd : ((r : Q) → S.Edge r → ℂ) × (J → ℂ) → (J → ℂ))
      (S.complexifySourceWeights p, t))
  exact hc.comp (f := fun zt ↦ (S.complexSourceSelectorWeights zt.1, zt.2))
    (x := (S.complexifySourceWeights p, t)) hmap

/-- For every fixed positive source law the joint transform is entire in all
transform coordinates. -/
theorem sourceComplexExpTransform_entire (S : FiniteStateSource Q A)
    (h : List S.Selector) (m : J → BlockBranchCoefficients h)
    (hm : ∀ j s ξ u v, (m j s ξ u v : ℝ) ∈ Icc (0 : ℝ) 1)
    (p : (r : Q) → S.Edge r → ℝ) (hp : ∀ r e, 0 < p r e) :
    ∀ t : J → ℂ, AnalyticAt ℂ (S.sourceComplexExpTransform h m hm (S.complexifySourceWeights p)) t := by
  intro t
  have h := S.analyticAt_sourceComplexExpTransform h m hm p hp t
  exact h.comp (f := fun t ↦ (S.complexifySourceWeights p, t)) (x := t)
    (analyticAt_const.prod analyticAt_id)

theorem sourceComplexExpTransform_eq_integral (S : FiniteStateSource Q A)
    (h : List S.Selector) (hh : h ≠ []) (m : J → BlockBranchCoefficients h)
    (hm : ∀ j s ξ u v, (m j s ξ u v : ℝ) ∈ Icc (0 : ℝ) 1)
    (p : (r : Q) → S.Edge r → ℝ) (hp : ∀ r e, 0 < p r e) (t : J → ℂ) :
    S.sourceComplexExpTransform h m hm (S.complexifySourceWeights p) t =
      ∫ ω, Complex.exp (∑ j, t j *
        (S.sourceBlockBranch h (m j) (hm j) p
          (initialMarkerGap (endoMarkerBlock h) (iidBlockPath h.length ω)) : ℂ))
        ∂(S.normalizedSelectorLaw p hp).iidMeasure := by
  unfold sourceComplexExpTransform
  rw [S.complexSourceSelectorWeights_ofReal]
  change blockComplexExpTransform h m hm (fun a ↦ ((S.normalizedSelectorLaw p hp).weight a : ℂ)) t = _
  have he := blockComplexExpTransform_eq_integral (S.normalizedSelectorLaw p hp)
    (S.normalizedSelectorLaw_pos p hp) h hh m hm t
  simpa only [S.sourceBlockBranch_eq h _ _ p hp] using he

end FiniteStateSource
end IndependentZeroBlocks
