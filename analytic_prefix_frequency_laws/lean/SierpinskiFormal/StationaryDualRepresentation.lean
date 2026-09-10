import Mathlib.Analysis.Normed.Module.DoubleDual
import SierpinskiFormal.StationaryDualPairing
import SierpinskiFormal.StationaryFiberBarycenter

/-! # The bounded dual field of a positive norming-fiber measure -/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace IndependentZeroBlocks

variable {X K E : Type*} [MeasurableSpace X]
variable [TopologicalSpace K] [CompactSpace K]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Signed evaluations of an isometric embedding form a norming family of
continuous linear functionals of norm at most one. -/
def signedNormingDual (J : E →ₗᵢ[ℝ] C(K, ℝ)) (ks : K × Bool) : E →L[ℝ] ℝ :=
  if ks.2 then -((ContinuousMap.evalCLM ℝ ks.1).comp J.toContinuousLinearMap)
  else (ContinuousMap.evalCLM ℝ ks.1).comp J.toContinuousLinearMap

@[simp] theorem signedNormingDual_apply
    (J : E →ₗᵢ[ℝ] C(K, ℝ)) (ks : K × Bool) (e : E) :
    signedNormingDual J ks e = if ks.2 then -(J e ks.1) else J e ks.1 := by
  simp only [signedNormingDual]
  split <;> rfl

theorem norm_signedNormingDual_le (J : E →ₗᵢ[ℝ] C(K, ℝ)) (ks : K × Bool) :
    ‖signedNormingDual J ks‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro e
  have h := ContinuousMap.norm_coe_le_norm (J e) ks.1
  simp only [J.norm_map] at h
  rw [signedNormingDual_apply]
  split <;> simpa using h

section Fibers

variable [MeasurableSpace K] [MeasurableSingletonClass K] [Countable K]

def normingFiberDualField (J : E →ₗᵢ[ℝ] C(K, ℝ))
    (ν : Measure (X × (K × Bool))) (μ : Measure X) : X → E →L[ℝ] ℝ :=
  countableFiberBarycenter ν μ (signedNormingDual J)

theorem memLp_top_normingFiberDualField (J : E →ₗᵢ[ℝ] C(K, ℝ))
    (ν : Measure (X × (K × Bool))) [IsFiniteMeasure ν]
    (μ : Measure X) [SigmaFinite μ] (hν : ν.fst = μ) :
    MemLp (normingFiberDualField J ν μ) ∞ μ := by
  apply memLp_top_of_bound
    (aestronglyMeasurable_countableFiberBarycenter ν μ hν
      (signedNormingDual J) 1 (norm_signedNormingDual_le J)) 1
  exact norm_countableFiberBarycenter_le_ae ν μ hν
    (signedNormingDual J) 1 (norm_signedNormingDual_le J)

def normingFiberDualLp (J : E →ₗᵢ[ℝ] C(K, ℝ))
    (ν : Measure (X × (K × Bool))) [IsFiniteMeasure ν]
    (μ : Measure X) [SigmaFinite μ] (hν : ν.fst = μ) :
    Lp (E →L[ℝ] ℝ) ∞ μ :=
  (memLp_top_normingFiberDualField J ν μ hν).toLp (normingFiberDualField J ν μ)

theorem normingFiberDualLp_coeFn (J : E →ₗᵢ[ℝ] C(K, ℝ))
    (ν : Measure (X × (K × Bool))) [IsFiniteMeasure ν]
    (μ : Measure X) [SigmaFinite μ] (hν : ν.fst = μ) :
    ⇑(normingFiberDualLp J ν μ hν) =ᵐ[μ] normingFiberDualField J ν μ :=
  (memLp_top_normingFiberDualField J ν μ hν).coeFn_toLp

end Fibers

section ContinuousKernel

variable [TopologicalSpace X] [CompactSpace X]

def normingDualKernelContinuous
    (J : E →ₗᵢ[ℝ] C(K, ℝ)) (g : C(X, E)) : C(X × (K × Bool), ℝ) := by
  refine ⟨fun z ↦ signedNormingDual J z.2 (g z.1), ?_⟩
  have heval : Continuous (fun z : X × (K × Bool) ↦ J (g z.1) z.2.1) :=
    ContinuousEval.continuous_eval.comp
      ((J.continuous.comp (g.continuous.comp continuous_fst)).prodMk
        (continuous_fst.comp continuous_snd))
  have hsign : Continuous (fun z : X × (K × Bool) ↦
      (if z.2.2 then (-1 : ℝ) else 1)) :=
    (continuous_of_discreteTopology :
      Continuous (fun b : Bool ↦ if b then (-1 : ℝ) else 1)).comp
      (continuous_snd.comp continuous_snd)
  convert hsign.mul heval using 1
  funext z
  rw [signedNormingDual_apply]
  split <;> simp_all

@[simp] theorem normingDualKernelContinuous_apply
    (J : E →ₗᵢ[ℝ] C(K, ℝ)) (g : C(X, E)) (z : X × (K × Bool)) :
    normingDualKernelContinuous J g z = signedNormingDual J z.2 (g z.1) := rfl

variable [BorelSpace X] [SecondCountableTopology X]
variable [MeasurableSpace K] [BorelSpace K] [Countable K] [T2Space K]

theorem integral_normingFiberDualField_apply_continuous
    (J : E →ₗᵢ[ℝ] C(K, ℝ))
    (ν : Measure (X × (K × Bool))) [IsFiniteMeasure ν]
    (μ : Measure X) [SigmaFinite μ] [IsFiniteMeasure μ] (hν : ν.fst = μ)
    (g : C(X, E)) :
    (∫ x, normingFiberDualField J ν μ x (g x) ∂μ) =
      ∫ z, normingDualKernelContinuous J g z ∂ν := by
  let η : X → (E →L[ℝ] ℝ) →L[ℝ] ℝ := fun x ↦
    NormedSpace.inclusionInDoubleDual ℝ E (g x)
  have hη : Measurable (fun z : X × (K × Bool) ↦
      η z.1 (signedNormingDual J z.2)) := by
    exact (normingDualKernelContinuous J g).continuous.measurable
  have hηbound : ∀ x, ‖η x‖ ≤ ‖g‖ := fun x ↦
    (NormedSpace.double_dual_bound ℝ E (g x)).trans (g.norm_coe_le_norm x)
  exact integral_apply_countableFiberBarycenter_eq ν μ hν
    (signedNormingDual J) 1 zero_le_one (norm_signedNormingDual_le J)
    η hη ‖g‖ (norm_nonneg g) hηbound

theorem dualFieldPairing_normingFiberDualLp_continuous
    (J : E →ₗᵢ[ℝ] C(K, ℝ))
    (ν : Measure (X × (K × Bool))) [IsFiniteMeasure ν]
    (μ : Measure X) [SigmaFinite μ] [IsFiniteMeasure μ] (hν : ν.fst = μ)
    (g : C(X, E)) :
    dualFieldPairing μ (normingFiberDualLp J ν μ hν)
      (ContinuousMap.toLp 1 μ ℝ g) =
      ∫ z, normingDualKernelContinuous J g z ∂ν := by
  rw [dualFieldPairing_apply]
  calc
    (∫ x, (normingFiberDualLp J ν μ hν x) ((ContinuousMap.toLp 1 μ ℝ g) x) ∂μ) =
        ∫ x, normingFiberDualField J ν μ x (g x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [normingFiberDualLp_coeFn J ν μ hν,
        ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) μ g] with x hη hg
      rw [hη, hg]
    _ = ∫ z, normingDualKernelContinuous J g z ∂ν :=
      integral_normingFiberDualField_apply_continuous J ν μ hν g

end ContinuousKernel

end IndependentZeroBlocks
