import SierpinskiFormal.StationaryCompactnessPositive
import SierpinskiFormal.StationaryCompactness

noncomputable section
open Set Filter Topology MeasureTheory
open scoped ENNReal
namespace IndependentZeroBlocks

variable {X K E : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [HasOuterApproxClosed X]
  [TopologicalSpace K] [CompactSpace K] [T2Space K] [Nonempty K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure X} [IsProbabilityMeasure μ]

theorem exists_positiveState_measure_representation
    (J : E →ₗᵢ[ℝ] C(K, ℝ))
    (Λ : Lp E 1 μ →L[ℝ] ℝ) (hΛ : Λ ≠ 0) :
    ∃ Ψ : PositiveNormalizedState (X × (K × Bool)),
      (stateRieszMeasure (X × (K × Bool)) Ψ).fst = μ ∧
      ∀ g : C(X, E),
        (∫ z, signedPairingContinuousMap J g z
          ∂stateRieszMeasure (X × (K × Bool)) Ψ) =
          ‖Λ‖⁻¹ * Λ (ContinuousMap.toLp 1 μ ℝ g) := by
  obtain ⟨Ψ, hΨ⟩ :=
    exists_positiveNormalizedState_extends_signedPairing
      (μ := μ) J Λ hΛ
  refine ⟨Ψ, ?_, ?_⟩
  · apply stateRieszMeasure_fst_eq_of_continuousMapFst Ψ
    intro a
    have h := hΨ (a, (0 : C(X, E)))
    have hrange : signedPairingRangeMap J (a, (0 : C(X, E))) =
        continuousMapFst (K := K × Bool) a := by
      ext p
      change a p.1 + boolSign p.2.2 * J ((0 : C(X, E)) p.1) p.2.1 = a p.1
      simp
    rw [hrange] at h
    simpa [normalizedSignedPairingBase_apply] using h
  · intro g
    rw [integral_stateRieszMeasure]
    have h := hΨ ((0 : C(X, ℝ)), g)
    have hrange : signedPairingRangeMap J ((0 : C(X, ℝ)), g) =
        signedPairingContinuousMap J g := by
      ext p
      change (0 : C(X, ℝ)) p.1 +
        boolSign p.2.2 * J (g p.1) p.2.1 =
          boolSign p.2.2 * J (g p.1) p.2.1
      simp
    rw [hrange] at h
    simpa [normalizedSignedPairingBase_apply] using h

end IndependentZeroBlocks
