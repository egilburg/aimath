import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Sequences

/-! # Continuity of an extension from sequential limits on a dense domain -/

open Filter Topology

namespace IndependentZeroBlocks

/-- To prove continuity of an extension into a regular space, it suffices to
control all sequences from a dense inducing domain. The target domain is
first countable; the dense domain need not be complete. -/
theorem continuous_of_dense_sequential_limits
    {A B C : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [FirstCountableTopology B] [TopologicalSpace C] [T3Space C]
    (i : A → B) (hi : IsDenseInducing i) (f : A → C) (g : B → C)
    (hseq : ∀ (u : ℕ → A) (b : B),
      Tendsto (i ∘ u) atTop (𝓝 b) → Tendsto (f ∘ u) atTop (𝓝 (g b))) :
    Continuous g := by
  have hf (b : B) : Tendsto f (comap i (𝓝 b)) (𝓝 (g b)) := by
    apply Filter.tendsto_iff_seq_tendsto.mpr
    intro u hu
    exact hseq u b (tendsto_comap_iff.mp hu)
  have hc : Continuous (hi.extend f) := hi.continuous_extend fun b ↦ ⟨g b, hf b⟩
  have heq : hi.extend f = g := funext fun b ↦ hi.extend_eq_of_tendsto (hf b)
  simpa only [heq] using hc

end IndependentZeroBlocks
