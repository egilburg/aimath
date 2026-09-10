import SierpinskiFormal.ResetPrefixMean
import SierpinskiFormal.OneBoundaryMixture

/-! # The explicit one-boundary continuation branch after a reset -/

noncomputable section
open Filter Set Topology
open scoped BigOperators
namespace IndependentZeroBlocks

variable {R C X B : Type*} [CommRing R]
  [AddCommGroup X] [Module R X] [AddCommGroup B] [Module R B]
  [IsNoetherian R X] [IsNoetherian R (Module.Dual R X)]
  [IsNoetherian R B] [IsNoetherian R (Module.Dual R B)]
  [Fintype C] [Nonempty C] [DecidableEq C]
  [TopologicalSpace C] [DiscreteTopology C]

theorem exists_explicit_postReset_branch
    {d : ℕ} (op : (Fin d → Bool) → Bool)
    (T : C → Module.End R X) (e : C)
    (U : B →ₗ[R] X) (V : X →ₗ[R] B)
    (hfac : endoWord T [e] = U.comp V)
    (K : List C → (B ≃ₗ[R] B))
    (hK : ∀ y, (K y).toLinearMap = compressedReturn T U V y)
    (left : Fin d → Module.Dual R X) (seed : X) :
    ∃ m : List C → List C → ℚ,
      (∀ u v, (m u v : ℝ) ∈ Icc (0 : ℝ) 1) ∧
      ∀ (u t : List C) (p : C → ℝ),
      (∀ c, 0 < p c) → (∑ c, p c = 1) →
      Tendsto (realCesaroMean (fun n ↦ weightedWordExtensionAverage p
        (booleanWordIndicator (moduleBooleanCoefficientNonzero op T left seed))
        n (u ++ [e] ++ t))) atTop
        (𝓝 (p e * ∑' v : GapWords e, wordWeight p v.1 * (m u v.1 : ℝ))) := by
  obtain ⟨m, hm, hlimit⟩ := exists_postReset_weighted_mean op T e U V hfac K hK left seed
  refine ⟨m, hm, ?_⟩
  intro u t p hp hp1
  have h := hlimit u t p hp hp1
  have heq := twoBoundaryMean_eq_oneBoundaryMean p e (fun c ↦ (hp c).le) hp1 (hp e)
    (fun v : GapWords e ↦ (m u v.1 : ℝ)) (fun v ↦ hm u v.1)
  rwa [heq] at h

end IndependentZeroBlocks
