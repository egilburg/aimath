import SierpinskiFormal.ModuleTranslatedReturnMean
import SierpinskiFormal.BooleanResetArtinianDensity

/-! # Exact return translation after an observed prefix containing a reset -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Set Topology
open scoped BigOperators
namespace IndependentZeroBlocks

variable {R C X B : Type*} [CommRing R]
  [AddCommGroup X] [Module R X] [AddCommGroup B] [Module R B]
  [DecidableEq C]
  [Fintype C] [Nonempty C] [TopologicalSpace C] [DiscreteTopology C]

theorem moduleReturnFreeGroupAction_typedMarkerGaps
    (T : C → Module.End R X) (e : C)
    (U : B →ₗ[R] X) (V : X →ₗ[R] B)
    (hfac : endoWord T [e] = U.comp V)
    (K : List C → (B ≃ₗ[R] B))
    (hK : ∀ y, (K y).toLinearMap = compressedReturn T U V y)
    (w : List C) :
    (moduleReturnFreeGroupAction (fun g : GapWords e ↦ K g.1)
      (positiveFreeGroupWord (moduleTypedMarkerGaps e w))).toLinearMap =
      compressedReturn T U V w := by
  rw [moduleReturnFreeGroupAction_positiveWord_toLinearMap]
  have hne : moduleTypedMarkerGaps e w ≠ [] := by
    intro hnil
    have hmap := congrArg (List.map Subtype.val) hnil
    rw [moduleTypedMarkerGaps_map_val] at hmap
    exact markerGaps_ne_nil e w (by simpa using hmap)
  cases hgs : moduleTypedMarkerGaps e w with
  | nil => exact (hne hgs).elim
  | cons g gs =>
    have hmaps : (g :: gs).map (fun d ↦ (K d.1).toLinearMap) =
        ((g :: gs).map Subtype.val).map (compressedReturn T U V) := by
      rw [List.map_map]
      exact List.map_congr_left fun d _ ↦ hK d.1
    rw [hmaps]
    have hprod := compressedReturn_prod_intercalate T [e] U V hfac g.1
      (gs.map Subtype.val)
    simp only [List.map_cons] at hprod ⊢
    rw [hprod]
    have hmap := congrArg (List.map Subtype.val) hgs
    rw [moduleTypedMarkerGaps_map_val] at hmap
    simpa [hmap] using congrArg (compressedReturn T U V) (intercalate_markerGaps e w)

/-- The future left boundary after `u e t` is a common return translation of
the row fixed by `u`, even if `t` already contains further resets. -/
theorem compressedBoundaryLeft_after_reset
    (T : C → Module.End R X) (e : C)
    (U : B →ₗ[R] X) (V : X →ₗ[R] B)
    (hfac : endoWord T [e] = U.comp V)
    (left : Module.Dual R X) (u t a : List C) :
    compressedBoundaryLeft T U (left.comp (endoWord T (u ++ [e] ++ t))) a =
      (compressedBoundaryLeft T U left u).comp (compressedReturn T U V (t ++ a)) := by
  ext b
  simp only [compressedBoundaryLeft, compressedReturn, LinearMap.comp_apply,
    endoWord_append, Module.End.mul_apply, hfac]

variable [IsNoetherian R X] [IsNoetherian R (Module.Dual R X)]
  [IsNoetherian R B] [IsNoetherian R (Module.Dual R B)]

/-- One rational family works for all observed prefixes after the reset,
all subsequent initial gaps, and all positive source laws. This closes the
algebraic invariance obligation; it does not yet identify a conditional law. -/
theorem exists_common_postReset_boundary_means
    {d : ℕ} (op : (Fin d → Bool) → Bool)
    (T : C → Module.End R X) (e : C)
    (U : B →ₗ[R] X) (V : X →ₗ[R] B)
    (hfac : endoWord T [e] = U.comp V)
    (K : List C → (B ≃ₗ[R] B))
    (hK : ∀ y, (K y).toLinearMap = compressedReturn T U V y)
    (left : Fin d → Module.Dual R X) (seed : X) :
    ∃ m : List C → List C → ℚ,
      ∀ (u t a v : List C) (p : C → ℝ),
      (∀ c, 0 < p c) → (∑ c, p c = 1) →
      Tendsto (realCesaroMean
        (moduleBooleanCentralReturnExactAverage op T U V
          (fun j ↦ compressedBoundaryLeft T U
            ((left j).comp (endoWord T (u ++ [e] ++ t))) a)
          (compressedBoundarySeed T V seed v) p))
        atTop (𝓝 (m u v : ℝ)) := by
  have hex : ∀ (u v : List C), ∃ q : ℚ,
      ∀ (z : FreeGroup (GapWords e)) (p : C → ℝ),
      (∀ c, 0 < p c) → (∑ c, p c = 1) →
      Tendsto (realCesaroMean (moduleBooleanCentralReturnExactAverage op T U V
        (moduleTranslatedReturnLeft K e
          (fun j ↦ compressedBoundaryLeft T U (left j) u) z)
        (compressedBoundarySeed T V seed v) p)) atTop (𝓝 (q : ℝ)) := by
    intro u v
    exact exists_rational_forall_translated_moduleBooleanCentralReturnCesaro
      op T e U V hfac K hK
      (fun j ↦ compressedBoundaryLeft T U (left j) u)
      (compressedBoundarySeed T V seed v)
  choose m hm using hex
  refine ⟨m, ?_⟩
  intro u t a v p hp hp1
  have ht := hm u v (positiveFreeGroupWord (moduleTypedMarkerGaps e (t ++ a))) p hp hp1
  have hrows : moduleTranslatedReturnLeft K e
        (fun j ↦ compressedBoundaryLeft T U (left j) u)
        (positiveFreeGroupWord (moduleTypedMarkerGaps e (t ++ a))) =
      fun j ↦ compressedBoundaryLeft T U
        ((left j).comp (endoWord T (u ++ [e] ++ t))) a := by
    funext j
    unfold moduleTranslatedReturnLeft
    rw [moduleReturnFreeGroupAction_typedMarkerGaps T e U V hfac K hK]
    exact (compressedBoundaryLeft_after_reset T e U V hfac (left j) u t a).symm
  rwa [hrows] at ht

/-- The annealed continuation limit after `u e t` depends on `u` alone.
The matrix action, source positivity and actual weighted-word observation
are explicit; no conditional pathwise determinism is a premise. -/
theorem exists_postReset_weighted_mean
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
        (𝓝 (∑' i : GapWords e × GapWords e,
          moduleBoundaryWeight p e i * (m u i.2.1 : ℝ))) := by
  obtain ⟨m, hm⟩ := exists_common_postReset_boundary_means op T e U V hfac K hK left seed
  refine ⟨m, ?_, ?_⟩
  · intro u v
    exact moduleBooleanCentralReturnCesaroLimit_mem_Icc op T U V
      (fun j ↦ compressedBoundaryLeft T U
        ((left j).comp (endoWord T (u ++ [e] ++ []))) [])
      (compressedBoundarySeed T V seed v) uniformAlphabetWeight
      (fun c ↦ (uniformAlphabetWeight_pos c).le) sum_uniformAlphabetWeight _
      (hm u [] [] v uniformAlphabetWeight uniformAlphabetWeight_pos sum_uniformAlphabetWeight)
  · intro u t p hp hp1
    let left' : Fin d → Module.Dual R X :=
      fun j ↦ (left j).comp (endoWord T (u ++ [e] ++ t))
    have hcentral : ∀ i : GapWords e × GapWords e,
        Tendsto (realCesaroMean (abstractBoundaryCentralSequence p
          (moduleBooleanBoundaryCentralPredicate op T U V left' seed) i))
          atTop (𝓝 (m u i.2.1 : ℝ)) := by
      intro i
      exact hm u t i.1.1 i.2.1 p hp hp1
    have ht := tendsto_weightedPredicate_of_boundary_cesaro p
      (fun c ↦ (hp c).le) hp1 e (hp e)
      (moduleBooleanCoefficientNonzero op T left' seed)
      (moduleBooleanBoundaryCentralPredicate op T U V left' seed)
      (moduleBooleanCoefficientNonzero_boundary op T e U V hfac left' seed)
      (fun i ↦ (m u i.2.1 : ℝ)) hcentral
    have hword (w : List C) : moduleBooleanCoefficientNonzero op T left' seed w =
        moduleBooleanCoefficientNonzero op T left seed ((u ++ [e] ++ t) ++ w) := by
      simp only [moduleBooleanCoefficientNonzero, moduleCoefficientNonzero, left',
        LinearMap.comp_apply, endoWord_append, Module.End.mul_apply]
    have havg : (fun n ↦ weightedWordExtensionAverage p
        (booleanWordIndicator (moduleBooleanCoefficientNonzero op T left' seed)) n []) =
        (fun n ↦ weightedWordExtensionAverage p
          (booleanWordIndicator (moduleBooleanCoefficientNonzero op T left seed))
          n (u ++ [e] ++ t)) := by
      funext n
      rw [weightedWordExtensionAverage_eq_tuple_sum, weightedWordExtensionAverage_eq_tuple_sum]
      apply Finset.sum_congr rfl
      intro w _
      congr 1
      change boolIndicator (moduleBooleanCoefficientNonzero op T left' seed (List.ofFn w)) = _
      exact congrArg boolIndicator (hword (List.ofFn w))
    rwa [havg] at ht

end IndependentZeroBlocks
