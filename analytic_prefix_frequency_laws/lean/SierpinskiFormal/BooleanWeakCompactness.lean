import SierpinskiFormal.CountableWeakBooleanClosure
import SierpinskiFormal.PositiveFunctionalDecomposition
import Mathlib.Analysis.Normed.Module.Dual

/-! # Weak compactness and countability of stable Boolean row closures

The double-limit hypothesis is the sole analytic hypothesis. Uniform
boundedness, weak convergence, weak compactness, and countability are proved.
-/

noncomputable section
open Filter Topology

namespace IndependentZeroBlocks

variable {X Y : Type*}

/-- Continuous extensions of the pointwise closure of a Boolean row family. -/
def booleanRowExtensionClosure (B : X → Y → Bool) : Set C(Ultrafilter Y, ℝ) :=
  booleanUltrafilterExtension '' closure (Set.range B)

theorem booleanRows_tendsto_weak_of_pointwise
    (B : X → Y → Bool) (hB : HasBooleanDoubleLimitProperty B)
    (u : ℕ → X) (g : Y → Bool)
    (hu : Tendsto (fun n ↦ B (u n)) atTop (𝓝 g))
    (l : C(Ultrafilter Y, ℝ) →L[ℝ] ℝ) :
    Tendsto (fun n ↦ l (booleanUltrafilterExtension (B (u n)))) atTop
      (𝓝 (l (booleanUltrafilterExtension g))) := by
  letI : MeasurableSpace (Ultrafilter Y) := borel (Ultrafilter Y)
  letI : BorelSpace (Ultrafilter Y) := ⟨rfl⟩
  have hp : ∀ y, ∀ᶠ n in atTop, B (u n) y = g y := by
    intro y
    have hy := tendsto_pi_nhds.mp hu y
    rw [nhds_discrete] at hy
    exact tendsto_pure.mp hy
  exact tendsto_functional_continuousMap_of_pointwise l
    (fun n ↦ booleanUltrafilterExtension (B (u n)))
    (booleanUltrafilterExtension g) 1
    (fun n ↦ booleanUltrafilterExtension_norm_le_one _) (fun U ↦
      booleanUltrafilterExtension_tendsto_of_pointwise_eventually B hB u g hp U)

theorem booleanRowExtensionClosure_weakly_compact [Countable Y]
    (B : X → Y → Bool) (hB : HasBooleanDoubleLimitProperty B) :
    IsCompact (toWeakSpace ℝ C(Ultrafilter Y, ℝ) '' booleanRowExtensionClosure B) := by
  simpa only [booleanRowExtensionClosure, Set.image_image] using
    booleanRowClosure_weakly_compact_of_sequential_weak_convergence B
      (booleanRows_tendsto_weak_of_pointwise B hB)

theorem booleanRowExtensionClosure_subset_weak_closure [Countable Y]
    (B : X → Y → Bool) (hB : HasBooleanDoubleLimitProperty B)
    (f : C(Ultrafilter Y, ℝ)) (hf : f ∈ booleanRowExtensionClosure B) :
    toWeakSpace ℝ C(Ultrafilter Y, ℝ) f ∈ closure
      (toWeakSpace ℝ C(Ultrafilter Y, ℝ) ''
        Set.range (fun x ↦ booleanUltrafilterExtension (B x))) := by
  obtain ⟨g, hg, rfl⟩ := hf
  obtain ⟨v, hv, ht⟩ := mem_closure_iff_seq_limit.mp hg
  choose u hu using hv
  have hut : Tendsto (fun n ↦ B (u n)) atTop (𝓝 g) := by
    simpa only [hu] using ht
  have hw : Tendsto (fun n ↦ toWeakSpace ℝ C(Ultrafilter Y, ℝ)
      (booleanUltrafilterExtension (B (u n)))) atTop
      (𝓝 (toWeakSpace ℝ C(Ultrafilter Y, ℝ) (booleanUltrafilterExtension g))) := by
    apply (WeakBilin.tendsto_iff_forall_eval_tendsto
      (B := (topDualPairing ℝ C(Ultrafilter Y, ℝ)).flip) (by
        intro x y hxy
        apply (NormedSpace.eq_iff_forall_dual_eq ℝ).2
        intro phi
        exact LinearMap.congr_fun hxy phi)).mpr
    intro l
    exact booleanRows_tendsto_weak_of_pointwise B hB u g hut l
  exact mem_closure_of_tendsto hw (Filter.Eventually.of_forall fun n ↦
    ⟨booleanUltrafilterExtension (B (u n)), ⟨u n, rfl⟩, rfl⟩)

theorem booleanRowExtensionClosure_countable [Countable X] [Countable Y]
    (B : X → Y → Bool) (hB : HasBooleanDoubleLimitProperty B) :
    (booleanRowExtensionClosure B).Countable := by
  apply countable_of_separated_subset_weak_closure
    (Set.range (fun x ↦ booleanUltrafilterExtension (B x)))
    (booleanRowExtensionClosure B) (Set.countable_range _) (by norm_num : (0 : ℝ) < 1)
  · rintro f ⟨g, hg, rfl⟩ f' ⟨g', hg', rfl⟩ hne
    apply one_le_dist_booleanUltrafilterExtension
    intro he
    exact hne (congrArg booleanUltrafilterExtension he)
  · exact booleanRowExtensionClosure_subset_weak_closure B hB

/-- A countable stable Boolean family on countably many columns has a
countable, weakly compact continuous row closure. -/
theorem booleanRowClosure_weakly_compact_and_countable [Countable X] [Countable Y]
    (B : X → Y → Bool) (hB : HasBooleanDoubleLimitProperty B) :
    IsCompact (toWeakSpace ℝ C(Ultrafilter Y, ℝ) '' booleanRowExtensionClosure B) ∧
    (booleanRowExtensionClosure B).Countable :=
  ⟨booleanRowExtensionClosure_weakly_compact B hB,
    booleanRowExtensionClosure_countable B hB⟩

end IndependentZeroBlocks
