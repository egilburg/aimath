import SierpinskiFormal.StationaryDualRepresentation
import SierpinskiFormal.StationaryCompactnessPositiveMeasure

/-! # Bochner L1 duality from a countable compact norming space

The positive sign-doubling extension and countable RN fibers represent every
L1 functional by a strongly measurable bounded dual field. No duality or
Radon--Nikodym property is assumed as an extra hypothesis.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace IndependentZeroBlocks

variable {X K E : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [HasOuterApproxClosed X]
  [TopologicalSpace K] [CompactSpace K] [T2Space K] [Nonempty K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K] [Countable K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure X} [IsProbabilityMeasure μ] [μ.WeaklyRegular]

theorem normingDualKernelContinuous_eq_signedPairingContinuousMap
    (J : E →ₗᵢ[ℝ] C(K, ℝ)) (g : C(X, E)) :
    normingDualKernelContinuous J g = signedPairingContinuousMap J g := by
  ext z
  rcases z with ⟨x, k, s⟩
  cases s <;> simp [normingDualKernelContinuous_apply,
    signedNormingDual_apply, signedPairingContinuousMap_apply, boolSign]

/-- Every continuous functional on Bochner L1 has an essentially bounded,
strongly measurable dual-field representation when the value space embeds
isometrically in C(K) for a countable compact K. -/
theorem exists_dualFieldPairing_of_isometricContinuousMapEmbedding
    (J : E →ₗᵢ[ℝ] C(K, ℝ)) (Λ : Lp E 1 μ →L[ℝ] ℝ) :
    ∃ η : Lp (E →L[ℝ] ℝ) ∞ μ, Λ = dualFieldPairing μ η := by
  by_cases hΛ : Λ = 0
  · refine ⟨0, ?_⟩
    simp [hΛ, dualFieldPairing]
  obtain ⟨Ψ, hμ, hΨ⟩ := exists_positiveState_measure_representation J Λ hΛ
  let ν := stateRieszMeasure (X × (K × Bool)) Ψ
  let η := normingFiberDualLp J ν μ hμ
  have hnormalized : ‖Λ‖⁻¹ • Λ = dualFieldPairing μ η := by
    apply eq_dualFieldPairing_of_continuous_tests
    intro g
    change ‖Λ‖⁻¹ * Λ (ContinuousMap.toLp 1 μ ℝ g) =
      dualFieldPairing μ (normingFiberDualLp J ν μ hμ)
        (ContinuousMap.toLp 1 μ ℝ g)
    rw [dualFieldPairing_normingFiberDualLp_continuous,
      normingDualKernelContinuous_eq_signedPairingContinuousMap]
    exact (hΨ g).symm
  refine ⟨‖Λ‖ • η, ?_⟩
  have hsmul : dualFieldPairing μ (‖Λ‖ • η) = ‖Λ‖ • dualFieldPairing μ η := by
    simp [dualFieldPairing]
  rw [hsmul, ← hnormalized, smul_smul,
    mul_inv_cancel₀ (norm_ne_zero_iff.mpr hΛ), one_smul]

end IndependentZeroBlocks
