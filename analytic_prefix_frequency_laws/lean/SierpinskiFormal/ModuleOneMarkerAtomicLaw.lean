import SierpinskiFormal.IIDResetAtomicLaw
import SierpinskiFormal.ResetOneBoundaryMean

/-! # The actual one-marker atomic law for module Boolean observations -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter MeasureTheory Set Topology
open scoped BigOperators
namespace IndependentZeroBlocks

variable {R A X B : Type*} [CommRing R]
  [AddCommGroup X] [Module R X] [AddCommGroup B] [Module R B]
  [IsNoetherian R X] [IsNoetherian R (Module.Dual R X)]
  [IsNoetherian R B] [IsNoetherian R (Module.Dual R B)]
  [Fintype A] [Nonempty A] [DecidableEq A]
  [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [MeasurableSingletonClass A] [BorelSpace A]

theorem moduleBooleanCoefficientNonzero_hasBooleanDoubleLimitProperty
    {d : ℕ} (op : (Fin d → Bool) → Bool) (T : A → Module.End R X)
    (left : Fin d → Module.Dual R X) (seed : X) :
    HasBooleanDoubleLimitProperty (fun w z ↦
      moduleBooleanCoefficientNonzero op T left seed (z ++ w)) := by
  change HasBooleanDoubleLimitProperty
    (booleanCombine op (fun j (w z : List A) ↦
      nonzeroBool ((left j) (linearWord T (z ++ w) seed))))
  exact hasBooleanDoubleLimitProperty_booleanCombine op _
    (fun j ↦ noetherian_linearWord_rightKernel_hasBooleanDoubleLimitProperty T (left j) seed)

def oneMarkerBranch (e : A) (m : List A → List A → ℚ)
    (p : A → ℝ) (u : GapWords e) : ℝ :=
  p e * ∑' v : GapWords e, wordWeight p v.1 * (m u.1 v.1 : ℝ)

/-- A single rational family works for all positive normalized source laws.
The conclusion identifies the actual IID prefix limit with the actual initial
gap, proves L1 convergence, and computes its complete distribution. -/
theorem exists_module_oneMarker_atomic_law
    {d : ℕ} (op : (Fin d → Bool) → Bool)
    (T : A → Module.End R X) (e : A)
    (U : B →ₗ[R] X) (V : X →ₗ[R] B)
    (hfac : endoWord T [e] = U.comp V)
    (hbij : ∀ y : List A, Function.Bijective (compressedReturn T U V y))
    (left : Fin d → Module.Dual R X) (seed : X) :
    ∃ m : List A → List A → ℚ,
      (∀ u v, (m u v : ℝ) ∈ Icc (0 : ℝ) 1) ∧
      ∀ P : FiniteProbabilityWeights A, (∀ a, 0 < P.weight a) →
      (∀ u : GapWords e, oneMarkerBranch e m P.weight u ∈ Icc (0 : ℝ) 1) ∧
      (∀ᵐ ω ∂P.iidMeasure, Tendsto
        (fun N ↦ stationaryBooleanFrequency digitHead digitShift
          (moduleBooleanCoefficientNonzero op T left seed) N ω)
        atTop (𝓝 (oneMarkerBranch e m P.weight (initialMarkerGap e ω)))) ∧
      Tendsto (fun N ↦ ∫ ω, ‖stationaryBooleanFrequency digitHead digitShift
        (moduleBooleanCoefficientNonzero op T left seed) N ω -
        oneMarkerBranch e m P.weight (initialMarkerGap e ω)‖ ∂P.iidMeasure)
        atTop (𝓝 0) ∧
      P.iidMeasure.map (fun ω ↦ oneMarkerBranch e m P.weight (initialMarkerGap e ω)) =
        Measure.sum (fun u : GapWords e ↦
          ENNReal.ofReal (P.weight e * wordWeight P.weight u.1) •
            Measure.dirac (oneMarkerBranch e m P.weight u)) := by
  let K : List A → (B ≃ₗ[R] B) := fun y ↦
    LinearEquiv.ofBijective (compressedReturn T U V y) (hbij y)
  obtain ⟨m, hm, hmeans⟩ := exists_explicit_postReset_branch
    op T e U V hfac K (fun _ ↦ rfl) left seed
  refine ⟨m, hm, ?_⟩
  intro P hp
  refine ⟨?_, ?_⟩
  · intro u
    have h := oneBoundaryMean_mem_Icc P.weight e P.nonneg P.sum_eq_one (hp e)
      (fun v : GapWords e ↦ (m u.1 v.1 : ℝ)) (fun v ↦ hm u.1 v.1)
    simpa only [oneMarkerBranch, mul_assoc, tsum_mul_left] using h
  · exact iid_reset_atomic_law P e (hp e)
      (moduleBooleanCoefficientNonzero op T left seed)
      (moduleBooleanCoefficientNonzero_hasBooleanDoubleLimitProperty op T left seed)
      (oneMarkerBranch e m P.weight)
      (fun u t ↦ hmeans u.1 t P.weight hp P.sum_eq_one)

end IndependentZeroBlocks
