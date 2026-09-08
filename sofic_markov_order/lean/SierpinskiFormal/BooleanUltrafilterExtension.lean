import SierpinskiFormal.BooleanFilterLimit
import Mathlib.Topology.Compactification.StoneCech
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Extending stable Boolean kernels to the compact space of ultrafilters

The double-limit property upgrades pointwise sequential convergence on the
original index set to pointwise convergence on its compact ultrafilter space.
This is a concrete step towards weak compactness, not an assertion of it.
-/

noncomputable section

open Filter Topology

namespace IndependentZeroBlocks

variable {X Y : Type*}

/-- The continuous real zero-one extension to the compact ultrafilter space. -/
def booleanUltrafilterExtension (g : Y → Bool) : C(Ultrafilter Y, ℝ) where
  toFun U := boolIndicator (Ultrafilter.extend g U)
  continuous_toFun := (continuous_of_discreteTopology (f := boolIndicator)).comp
    (continuous_ultrafilter_extend g)

@[simp] theorem booleanUltrafilterExtension_pure (g : Y → Bool) (y : Y) :
    booleanUltrafilterExtension g (pure y) = boolIndicator (g y) := by
  change boolIndicator (Ultrafilter.extend g (pure y)) = _
  exact congrArg boolIndicator (congrFun (ultrafilter_extend_extends g) y)

theorem booleanUltrafilterExtension_norm_le_one (g : Y → Bool) :
    ‖booleanUltrafilterExtension g‖ ≤ 1 := by
  apply (ContinuousMap.norm_le _ (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro U
  change ‖boolIndicator (Ultrafilter.extend g U)‖ ≤ 1
  cases Ultrafilter.extend g U <;> norm_num [boolIndicator]

/-- Along a Boolean DLP kernel, a pointwise eventual limit also converges at
every ultrafilter point. The ultrafilter row limits are constructed. -/
theorem booleanUltrafilterExtension_tendsto_of_pointwise_eventually
    (B : X → Y → Bool) (hB : HasBooleanDoubleLimitProperty B)
    (x : ℕ → X) (g : Y → Bool)
    (hpointwise : ∀ y, ∀ᶠ n in atTop, B (x n) y = g y)
    (U : Ultrafilter Y) :
    Tendsto (fun n ↦ booleanUltrafilterExtension (B (x n)) U) atTop
      (𝓝 (booleanUltrafilterExtension g U)) := by
  obtain ⟨h, c, hrow, hg, hlim⟩ :=
    exists_ultrafilter_rowValues_eventually_eq B hB x g hpointwise U
  have hrowValue (n : ℕ) : Ultrafilter.extend (B (x n)) U = h n :=
    ultrafilter_extend_eq_iff.mpr (tendsto_nhds_of_eventually_eq (hrow n))
  have hgValue : Ultrafilter.extend g U = c :=
    ultrafilter_extend_eq_iff.mpr (tendsto_nhds_of_eventually_eq hg)
  apply tendsto_nhds_of_eventually_eq
  filter_upwards [hlim] with n hn
  change boolIndicator (Ultrafilter.extend (B (x n)) U) =
    boolIndicator (Ultrafilter.extend g U)
  rw [hrowValue, hgValue, hn]

end IndependentZeroBlocks
