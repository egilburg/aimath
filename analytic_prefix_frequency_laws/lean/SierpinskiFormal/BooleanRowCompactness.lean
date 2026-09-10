import SierpinskiFormal.BooleanUltrafilterExtension
import SierpinskiFormal.DenseSequentialExtension
import Mathlib.Analysis.LocallyConvex.WeakSpace

/-!
# Compactness from weak convergence of Boolean rows

For a countable column set, the pointwise row closure is compact and first
countable. If pointwise sequential limits of rows are weak limits of their
continuous ultrafilter extensions, that entire row closure has compact image
in the weak topology. This lemma isolates the remaining weak-convergence
input; it does not assume it has already been derived from DLP.
-/

noncomputable section

open Filter Topology

namespace IndependentZeroBlocks

theorem booleanRowClosure_weakly_compact_of_sequential_weak_convergence
    {X Y : Type*} [Countable Y] (B : X → Y → Bool)
    (hseq : ∀ (u : ℕ → X) (g : Y → Bool),
      Tendsto (fun n ↦ B (u n)) atTop (𝓝 g) →
      ∀ l : C(Ultrafilter Y, ℝ) →L[ℝ] ℝ,
        Tendsto (fun n ↦ l (booleanUltrafilterExtension (B (u n)))) atTop
          (𝓝 (l (booleanUltrafilterExtension g)))) :
    IsCompact ((fun g : Y → Bool ↦
      toWeakSpace ℝ C(Ultrafilter Y, ℝ) (booleanUltrafilterExtension g)) ''
        closure (Set.range B)) := by
  let K := ↥(closure (Set.range B))
  let row : X → K := fun x ↦ ⟨B x, subset_closure ⟨x, rfl⟩⟩
  letI : TopologicalSpace X := TopologicalSpace.induced row inferInstance
  have hdense : DenseRange row := by
    change Dense (Set.range row)
    rw [Subtype.dense_iff]
    simpa only [← Set.range_comp, Function.comp_def] using
      (Set.Subset.refl (closure (Set.range B)))
  have hdi : IsDenseInducing row := ⟨⟨rfl⟩, hdense⟩
  let e : K → WeakSpace ℝ C(Ultrafilter Y, ℝ) := fun g ↦
    toWeakSpace ℝ C(Ultrafilter Y, ℝ) (booleanUltrafilterExtension g.val)
  have he : Continuous e := by
    apply WeakBilin.continuous_of_continuous_eval
    intro l
    apply continuous_of_dense_sequential_limits row hdi
      (fun x ↦ l (booleanUltrafilterExtension (B x)))
      (fun g : K ↦ l (booleanUltrafilterExtension g.val))
    intro u g hu
    have hu' : Tendsto (fun n ↦ B (u n)) atTop (𝓝 g.val) :=
      (continuous_subtype_val.tendsto g).comp hu
    exact hseq u g.val hu' l
  have hK : IsCompact (closure (Set.range B)) := isClosed_closure.isCompact
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc := isCompact_univ.image he
  convert hc using 1
  ext z
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, Set.mem_univ _, rfl⟩
  · rintro ⟨g, _, rfl⟩
    exact ⟨g.val, g.property, rfl⟩

end IndependentZeroBlocks
