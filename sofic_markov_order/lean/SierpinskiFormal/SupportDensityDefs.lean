import SierpinskiFormal.SeedBlocks
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Filter.AtTopBot.Field

set_option autoImplicit false

namespace IndependentZeroBlocks

open Filter
open scoped Topology

/-- Number of nonzero coefficients strictly below `N`. -/
noncomputable def supportCount {K : Type*} [Semiring K]
    (F : PowerSeries K) (N : ℕ) : ℕ := by
  classical
  exact ((Finset.range N).filter fun n => PowerSeries.coeff n F ≠ 0).card

/-- The coefficient support has ordinary natural density zero. -/
def HasZeroSupportDensity {K : Type*} [Semiring K] (F : PowerSeries K) : Prop :=
  Tendsto (fun N : ℕ => (supportCount F N : ℝ) / (N : ℝ)) atTop (𝓝 0)

/-- An explicit positive eventual lower bound for the coefficient-support proportion. -/
def HasPositiveLowerSupportDensity {K : Type*} [Semiring K]
    (F : PowerSeries K) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    c * (N : ℝ) ≤ (supportCount F N : ℝ)

end IndependentZeroBlocks
