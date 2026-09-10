import SierpinskiFormal.BanachWordSeriesList
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Normed.Algebra.Exponential

/-! # Uniform branch vectors, mixture functionals, and analytic transforms -/

noncomputable section
open Filter Set Topology IndependentZeroBlocks
open scoped BigOperators BoundedContinuousFunction
namespace Sierpinski

variable {D I E : Type*} [Fintype D] [TopologicalSpace D] [DiscreteTopology D]
  [TopologicalSpace I] [DiscreteTopology I]
  [NormedAddCommGroup E] [NormedSpace ℂ E]

def boundedWordCoefficient (c : I → List D → ℂ) (hc : ∀ i w, ‖c i w‖ ≤ 1)
    (w : List D) : I →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete (fun i ↦ c i w) 1 (fun i ↦ hc i w)

theorem norm_boundedWordCoefficient (c : I → List D → ℂ) (hc : ∀ i w, ‖c i w‖ ≤ 1)
    (w : List D) : ‖boundedWordCoefficient c hc w‖ ≤ 1 :=
  (BoundedContinuousFunction.norm_le zero_le_one).mpr fun i ↦ hc i w

def uniformWordBranch (c : I → List D → ℂ) (hc : ∀ i w, ‖c i w‖ ≤ 1)
    (q : ℂ) (z : D → ℂ) : I →ᵇ ℂ :=
  q • banachWordSeries (boundedWordCoefficient c hc) z

theorem uniformWordBranch_apply (c : I → List D → ℂ) (hc : ∀ i w, ‖c i w‖ ≤ 1)
    (q : ℂ) (z : D → ℂ) (hz : finiteL1Norm z < 1) (i : I) :
    uniformWordBranch c hc q z i = q * ∑' w, complexWordWeight z w * c i w := by
  change q * (BoundedContinuousFunction.evalCLM ℂ i)
    (banachWordSeries (boundedWordCoefficient c hc) z) = _
  rw [map_banachWordSeries _ (norm_boundedWordCoefficient c hc) z hz]
  rfl

theorem analyticAt_uniformWordBranch (c : I → List D → ℂ) (hc : ∀ i w, ‖c i w‖ ≤ 1)
    (q : E → ℂ) (z : E → D → ℂ) (x : E) (hq : AnalyticAt ℂ q x)
    (hz : AnalyticAt ℂ z x) (hsmall : finiteL1Norm (z x) < 1) :
    AnalyticAt ℂ (fun y ↦ uniformWordBranch c hc (q y) (z y)) x := by
  exact hq.fun_smul ((analyticAt_banachWordSeries _ (norm_boundedWordCoefficient c hc)
    (z x) hsmall).comp hz)

theorem norm_wordEvaluation (u : List D) :
    ‖(BoundedContinuousFunction.evalCLM ℂ u : (List D →ᵇ ℂ) →L[ℂ] ℂ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa using BoundedContinuousFunction.norm_coe_le_norm f u

def wordMixtureFunctional (q : ℂ) (z : D → ℂ) : (List D →ᵇ ℂ) →L[ℂ] ℂ :=
  q • banachWordSeries (fun u ↦ BoundedContinuousFunction.evalCLM ℂ u) z

theorem wordMixtureFunctional_apply (q : ℂ) (z : D → ℂ)
    (hz : finiteL1Norm z < 1) (f : List D →ᵇ ℂ) :
    wordMixtureFunctional q z f = q * ∑' u, complexWordWeight z u * f u := by
  change q * (ContinuousLinearMap.apply ℂ ℂ f)
    (banachWordSeries (fun u : List D ↦ BoundedContinuousFunction.evalCLM ℂ u) z) = _
  rw [map_banachWordSeries _ norm_wordEvaluation z hz]
  rfl

theorem analyticAt_wordMixtureFunctional (q : E → ℂ) (z : E → D → ℂ) (x : E)
    (hq : AnalyticAt ℂ q x) (hz : AnalyticAt ℂ z x) (hsmall : finiteL1Norm (z x) < 1) :
    AnalyticAt ℂ (fun y ↦ wordMixtureFunctional (q y) (z y)) x :=
  hq.fun_smul ((analyticAt_banachWordSeries _ norm_wordEvaluation (z x) hsmall).comp hz)

theorem analyticAt_wordMixture_test (q : E → ℂ) (z : E → D → ℂ)
    (f : E → (List D →ᵇ ℂ)) (x : E) (hq : AnalyticAt ℂ q x)
    (hz : AnalyticAt ℂ z x) (hsmall : finiteL1Norm (z x) < 1) (hf : AnalyticAt ℂ f x) :
    AnalyticAt ℂ (fun y ↦ wordMixtureFunctional (q y) (z y) (f y)) x := by
  exact (ContinuousLinearMap.id ℂ ((List D →ᵇ ℂ) →L[ℂ] ℂ)).analyticAt_bilinear _ |>.comp₂
    (analyticAt_wordMixtureFunctional q z x hq hz hsmall) hf

variable {J : Type*} [Fintype J]

theorem analyticAt_uniform_mixedMoment
    (c : J → List D → List D → ℂ) (hc : ∀ j u v, ‖c j u v‖ ≤ 1)
    (k : J → ℕ) (q : E → ℂ) (z : E → D → ℂ) (x : E)
    (hq : AnalyticAt ℂ q x) (hz : AnalyticAt ℂ z x) (hsmall : finiteL1Norm (z x) < 1) :
    AnalyticAt ℂ (fun y ↦ wordMixtureFunctional (q y) (z y)
      (∏ j, uniformWordBranch (c j) (hc j) (q y) (z y) ^ k j)) x := by
  apply analyticAt_wordMixture_test q z _ x hq hz hsmall
  apply Finset.analyticAt_fun_prod
  intro j _
  exact (analyticAt_uniformWordBranch (c j) (hc j) q z x hq hz hsmall).fun_pow (k j)

theorem analyticAt_uniform_expTransform
    (c : J → List D → List D → ℂ) (hc : ∀ j u v, ‖c j u v‖ ≤ 1)
    (t : J → E → ℂ) (q : E → ℂ) (z : E → D → ℂ) (x : E)
    (ht : ∀ j, AnalyticAt ℂ (t j) x)
    (hq : AnalyticAt ℂ q x) (hz : AnalyticAt ℂ z x) (hsmall : finiteL1Norm (z x) < 1) :
    AnalyticAt ℂ (fun y ↦ wordMixtureFunctional (q y) (z y)
      (NormedSpace.exp (∑ j, t j y • uniformWordBranch (c j) (hc j) (q y) (z y)))) x := by
  apply analyticAt_wordMixture_test q z _ x hq hz hsmall
  apply (NormedSpace.exp_analytic (𝕂 := ℂ) _).comp
  apply Finset.analyticAt_fun_sum
  intro j _
  exact (ht j).fun_smul (analyticAt_uniformWordBranch (c j) (hc j) q z x hq hz hsmall)

end Sierpinski
