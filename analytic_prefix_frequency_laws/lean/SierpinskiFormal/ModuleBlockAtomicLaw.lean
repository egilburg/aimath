import SierpinskiFormal.ModuleBlockResetBranch
import SierpinskiFormal.HigherRankMeanBounds

/-! # A common reset gives the complete pathwise atomic block law -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter MeasureTheory Set Topology
open scoped BigOperators
namespace IndependentZeroBlocks

variable {A : Type*} [Fintype A] [Nonempty A] [DecidableEq A]
  [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [MeasurableSingletonClass A] [BorelSpace A]

/-- The full physical prefix frequency, with its common actual block boundary.
This record contains conclusions, and is constructed by the theorems below. -/
structure IIDBlockAtomicLaw (P : FiniteProbabilityWeights A) (ell : ℕ)
    (e : Fin ell → A) (q : List A → Bool) (D : GapWords e → ℝ) : Prop where
  branch_mem_Icc : ∀ u, D u ∈ Icc (0 : ℝ) 1
  pathwise : ∀ᵐ ω ∂P.iidMeasure, Tendsto
    (fun N ↦ stationaryBooleanFrequency digitHead digitShift q N ω)
    atTop (𝓝 (D (initialMarkerGap e (iidBlockPath ell ω))))
  in_L1 : Tendsto (fun N ↦ ∫ ω, ‖stationaryBooleanFrequency digitHead digitShift q N ω -
    D (initialMarkerGap e (iidBlockPath ell ω))‖ ∂P.iidMeasure) atTop (𝓝 0)
  law : P.iidMeasure.map (fun ω ↦ D (initialMarkerGap e (iidBlockPath ell ω))) =
    Measure.sum (fun u : GapWords e ↦
      ENNReal.ofReal (blockWeight P.weight ell e *
        wordWeight (blockWeight P.weight ell) u.1) • Measure.dirac (D u))

variable {R X B : Type*} [CommRing R]
  [AddCommGroup X] [Module R X] [AddCommGroup B] [Module R B]

theorem exists_module_blockReset_atomic_law
    [IsNoetherian R X] [IsNoetherian R (Module.Dual R X)]
    [IsNoetherian R B] [IsNoetherian R (Module.Dual R B)]
    {d : ℕ} (op : (Fin d → Bool) → Bool) (T : A → Module.End R X)
    (ell : ℕ) (hell : 0 < ell) (e : Fin ell → A)
    (U : B →ₗ[R] X) (V : X →ₗ[R] B)
    (hfac : endoWord (blockEndomorphism T ell) [e] = U.comp V)
    (hbij : ∀ y : List (Fin ell → A),
      Function.Bijective (compressedReturn (blockEndomorphism T ell) U V y))
    (left : Fin d → Module.Dual R X) (seed : X) :
    ∃ m : (s : Fin ell) → (Fin (s : ℕ) → A) →
        List (Fin ell → A) → List (Fin ell → A) → ℚ,
      (∀ s ξ u v, (m s ξ u v : ℝ) ∈ Icc (0 : ℝ) 1) ∧
      ∀ P : FiniteProbabilityWeights A, (∀ a, 0 < P.weight a) →
      IIDBlockAtomicLaw P ell e (moduleBooleanCoefficientNonzero op T left seed)
        (blockMarkerBranch ell e m P.weight) := by
  obtain ⟨m, hm, hmeans⟩ := exists_module_blockReset_branchMeans
    op T ell hell e U V hfac hbij left seed
  refine ⟨m, hm, ?_⟩
  intro P hp
  obtain ⟨hae, hL1, hlaw⟩ := iid_block_reset_atomic_law P ell hell e
    (blockLaw_weight_pos P hp ell e) (moduleBooleanCoefficientNonzero op T left seed)
    (moduleBooleanCoefficientNonzero_hasBooleanDoubleLimitProperty op T left seed)
    (blockMarkerBranch ell e m P.weight) (hmeans P hp)
  refine ⟨?_, hae, hL1, hlaw⟩
  intro u
  apply realCesaroLimit_mem_Icc _ (hmeans P hp u [])
  intro n
  apply weightedWordExtensionAverage_mem_Icc P.weight P.nonneg P.sum_eq_one
  · intro w
    simp only [booleanWordIndicator_apply, boolIndicator]
    split <;> norm_num
  · intro w
    simp only [booleanWordIndicator_apply, boolIndicator]
    split <;> norm_num

/-- The reset depends only on the Artinian module action, before the Boolean
operation, rows, seed, and positive source law. Every observation therefore
uses the same initial marker-free block gap. -/
theorem exists_commonReset_moduleBoolean_atomic_law
    [IsArtinianRing R] [Module.Finite R X] (T : A → Module.End R X) :
    ∃ h : List A, h ≠ [] ∧
      ∀ (d : ℕ) (op : (Fin d → Bool) → Bool)
        (left : Fin d → Module.Dual R X) (seed : X),
      ∃ m : (s : Fin h.length) → (Fin (s : ℕ) → A) →
          List (Fin h.length → A) → List (Fin h.length → A) → ℚ,
        (∀ s ξ u v, (m s ξ u v : ℝ) ∈ Icc (0 : ℝ) 1) ∧
        ∀ P : FiniteProbabilityWeights A, (∀ a, 0 < P.weight a) →
        IIDBlockAtomicLaw P h.length (endoMarkerBlock h)
          (moduleBooleanCoefficientNonzero op T left seed)
          (blockMarkerBranch h.length (endoMarkerBlock h) m P.weight) := by
  obtain ⟨h, hh, hmin⟩ := exists_minLengthWord T
  refine ⟨h, hh, ?_⟩
  intro d op left seed
  exact exists_module_blockReset_atomic_law op T h.length (List.length_pos_iff.mpr hh)
    (endoMarkerBlock h) (returnInclusion T h) (resetCorestrict T h)
    (block_reset_factorization T h)
    (fun y ↦ blockReturn_bijective_of_minLength T h hh hmin y) left seed

end IndependentZeroBlocks
