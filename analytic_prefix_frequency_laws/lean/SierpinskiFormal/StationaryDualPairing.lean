import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import SierpinskiFormal.GroupFlowStationaryState

/-! # Dual fields and tests on a compact weak range -/

noncomputable section

open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace IndependentZeroBlocks

variable {X K E : Type*} [MeasurableSpace X]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The continuous functional on Bochner L1 induced by an essentially
bounded field of continuous linear functionals. -/
def dualFieldPairing (μ : Measure X) (η : Lp (E →L[ℝ] ℝ) ∞ μ) :
    Lp E 1 μ →L[ℝ] ℝ :=
  (ContinuousLinearMap.id ℝ (E →L[ℝ] ℝ)).lpPairing μ ∞ 1 η

theorem dualFieldPairing_apply (μ : Measure X)
    (η : Lp (E →L[ℝ] ℝ) ∞ μ) (g : Lp E 1 μ) :
    dualFieldPairing μ η g = ∫ x, (η x) (g x) ∂μ :=
  (ContinuousLinearMap.id ℝ (E →L[ℝ] ℝ)).lpPairing_eq_integral η g

section CompactRange

variable [TopologicalSpace K] [CompactSpace K]

/-- Restriction of a dual functional to a bounded weakly continuous compact
range. The resulting map takes values in the supremum-norm space C(K). -/
def weakRangeDualRestriction
    (j : K → E) (B : ℝ) (hB : 0 ≤ B) (hj : ∀ k, ‖j k‖ ≤ B)
    (hjweak : ∀ φ : E →L[ℝ] ℝ, Continuous (fun k ↦ φ (j k))) :
    (E →L[ℝ] ℝ) →L[ℝ] C(K, ℝ) :=
  ({ toFun := fun φ ↦ ⟨fun k ↦ φ (j k), hjweak φ⟩
     map_add' := by intros; ext k; rfl
     map_smul' := by intros; ext k; rfl } :
      (E →L[ℝ] ℝ) →ₗ[ℝ] C(K, ℝ)).mkContinuous B (fun φ ↦ by
        apply (ContinuousMap.norm_le _ (mul_nonneg hB (norm_nonneg φ))).mpr
        intro k
        calc
          ‖φ (j k)‖ ≤ ‖φ‖ * ‖j k‖ := φ.le_opNorm _
          _ ≤ ‖φ‖ * B := mul_le_mul_of_nonneg_left (hj k) (norm_nonneg φ)
          _ = B * ‖φ‖ := mul_comm _ _)

@[simp] theorem weakRangeDualRestriction_apply
    (j : K → E) (B : ℝ) (hB : 0 ≤ B) (hj : ∀ k, ‖j k‖ ≤ B)
    (hjweak : ∀ φ : E →L[ℝ] ℝ, Continuous (fun k ↦ φ (j k)))
    (φ : E →L[ℝ] ℝ) (k : K) :
    weakRangeDualRestriction j B hB hj hjweak φ k = φ (j k) := rfl

theorem aestronglyMeasurable_weakRangeDualRestriction
    (μ : Measure X) (η : X → E →L[ℝ] ℝ)
    (hη : AEStronglyMeasurable η μ)
    (j : K → E) (B : ℝ) (hB : 0 ≤ B) (hj : ∀ k, ‖j k‖ ≤ B)
    (hjweak : ∀ φ : E →L[ℝ] ℝ, Continuous (fun k ↦ φ (j k))) :
    AEStronglyMeasurable
      (fun x ↦ weakRangeDualRestriction j B hB hj hjweak (η x)) μ :=
  (weakRangeDualRestriction j B hB hj hjweak).continuous.comp_aestronglyMeasurable hη

end CompactRange

section DenseContinuousTests

variable [TopologicalSpace X] [CompactSpace X] [NormalSpace X] [BorelSpace X]
variable [SecondCountableTopology X]

/-- Equality on continuous source functions determines a Bochner L1
functional. This promotes a Riesz construction's continuous-test formula to
the entire L1 space. -/
theorem eq_dualFieldPairing_of_continuous_tests
    (μ : Measure X) [IsFiniteMeasure μ] [μ.WeaklyRegular]
    (Λ : Lp E 1 μ →L[ℝ] ℝ) (η : Lp (E →L[ℝ] ℝ) ∞ μ)
    (h : ∀ g : C(X, E), Λ (ContinuousMap.toLp 1 μ ℝ g) =
      dualFieldPairing μ η (ContinuousMap.toLp 1 μ ℝ g)) :
    Λ = dualFieldPairing μ η := by
  apply DFunLike.coe_injective
  apply (ContinuousMap.toLp_denseRange E μ ℝ (p := 1) (by simp)).equalizer
    Λ.continuous (dualFieldPairing μ η).continuous
  exact funext h

end DenseContinuousTests

end IndependentZeroBlocks
