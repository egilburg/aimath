import SierpinskiFormal.ModuleOneMarkerAtomicLaw
import SierpinskiFormal.IIDBlockResetAtomicLaw

/-! # Full physical continuation branches from a single blocked reset -/

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

theorem moduleBoolean_contextAverage {d : ℕ}
    (op : (Fin d → Bool) → Bool) (T : A → Module.End R X)
    (left : Fin d → Module.Dual R X) (seed : X) (p : A → ℝ)
    (w : List A) (n : ℕ) :
    weightedWordExtensionAverage p
      (booleanWordIndicator (moduleBooleanCoefficientNonzero op T
        (fun j ↦ (left j).comp (endoWord T w)) seed)) n [] =
    weightedWordExtensionAverage p
      (booleanWordIndicator (moduleBooleanCoefficientNonzero op T left seed)) n w := by
  rw [weightedWordExtensionAverage_eq_tuple_sum, weightedWordExtensionAverage_eq_tuple_sum]
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  simp only [booleanWordIndicator_apply, List.nil_append, moduleBooleanCoefficientNonzero,
    moduleCoefficientNonzero, LinearMap.comp_apply, endoWord_append, Module.End.mul_apply]

def blockMarkerBranch (ell : ℕ) (e : Fin ell → A)
    (m : (s : Fin ell) → (Fin (s : ℕ) → A) →
      List (Fin ell → A) → List (Fin ell → A) → ℚ)
    (p : A → ℝ) (u : GapWords e) : ℝ :=
  (∑ s : Fin ell, ∑ ξ : Fin (s : ℕ) → A,
    wordWeight p (List.ofFn ξ) * oneMarkerBranch e (m s ξ) (blockWeight p ell) u) / (ell : ℝ)

theorem exists_module_blockReset_branchMeans
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
      ∀ (P : FiniteProbabilityWeights A), (∀ a, 0 < P.weight a) →
      ∀ (u : GapWords e) (t : List (Fin ell → A)),
      Tendsto (realCesaroMean (fun n ↦ weightedWordExtensionAverage P.weight
        (booleanWordIndicator (moduleBooleanCoefficientNonzero op T left seed)) n
        (flattenBlocks ell (u.1 ++ [e] ++ t))))
        atTop (𝓝 (blockMarkerBranch ell e m P.weight u)) := by
  let K : List (Fin ell → A) → (B ≃ₗ[R] B) := fun y ↦
    LinearEquiv.ofBijective (compressedReturn (blockEndomorphism T ell) U V y) (hbij y)
  have hs : ∀ (s : Fin ell) (ξ : Fin (s : ℕ) → A),
      ∃ m : List (Fin ell → A) → List (Fin ell → A) → ℚ,
        (∀ u v, (m u v : ℝ) ∈ Icc (0 : ℝ) 1) ∧
        ∀ (u t : List (Fin ell → A)) (p : (Fin ell → A) → ℝ),
        (∀ c, 0 < p c) → (∑ c, p c = 1) →
        Tendsto (realCesaroMean (fun n ↦ weightedWordExtensionAverage p
          (booleanWordIndicator (moduleBooleanCoefficientNonzero op (blockEndomorphism T ell)
            left (moduleSuffixSeed T (List.ofFn ξ) seed))) n (u ++ [e] ++ t)))
          atTop (𝓝 (p e * ∑' v : GapWords e, wordWeight p v.1 * (m u v.1 : ℝ))) :=
    fun s ξ ↦ exists_explicit_postReset_branch op (blockEndomorphism T ell) e U V hfac
      K (fun _ ↦ rfl) left (moduleSuffixSeed T (List.ofFn ξ) seed)
  choose m hm hmeans using hs
  refine ⟨m, hm, ?_⟩
  intro P hp u t
  let w := u.1 ++ [e] ++ t
  let left' : Fin d → Module.Dual R X :=
    fun j ↦ (left j).comp (endoWord T (flattenBlocks ell w))
  obtain ⟨H, hH⟩ := exists_all_context_annealed_means P
    (moduleBooleanCoefficientNonzero op T left seed)
    (moduleBooleanCoefficientNonzero_hasBooleanDoubleLimitProperty op T left seed)
  have hfull : Tendsto (realCesaroMean (fun n ↦ weightedWordExtensionAverage P.weight
      (booleanWordIndicator (moduleBooleanCoefficientNonzero op T left' seed)) n []))
      atTop (𝓝 (H (flattenBlocks ell w))) := by
    simpa only [left', moduleBoolean_contextAverage] using hH (flattenBlocks ell w)
  have hblock (s : Fin ell) (ξ : Fin (s : ℕ) → A) :
      Tendsto (realCesaroMean (fun n ↦ weightedWordExtensionAverage (blockWeight P.weight ell)
        (booleanWordIndicator (moduleBooleanCoefficientNonzero op (blockEndomorphism T ell)
          left' (moduleSuffixSeed T (List.ofFn ξ) seed))) n []))
        atTop (𝓝 (oneMarkerBranch e (m s ξ) (blockWeight P.weight ell) u)) := by
    have h := hmeans s ξ u.1 t (P.blockLaw ell).weight
      (blockLaw_weight_pos P hp ell) (P.blockLaw ell).sum_eq_one
    simpa only [left', ← endoWord_blockEndomorphism, moduleBoolean_contextAverage,
      oneMarkerBranch, FiniteProbabilityWeights.blockLaw, w] using h
  have heq := moduleBooleanLimit_eq_average_blockLimits op P.weight T left' seed ell hell
    (H (flattenBlocks ell w))
    (fun s ξ ↦ oneMarkerBranch e (m s ξ) (blockWeight P.weight ell) u) hfull hblock
  have h := hH (flattenBlocks ell w)
  rw [heq] at h
  exact h

end IndependentZeroBlocks
