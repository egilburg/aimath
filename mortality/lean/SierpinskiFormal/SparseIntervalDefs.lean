import SierpinskiFormal.SupportDensityDefs

set_option autoImplicit false

namespace IndependentZeroBlocks

open Filter
open scoped Topology

/-- Number of indices below N satisfying a predicate. -/
noncomputable def predicateCount (S : ℕ → Prop) (N : ℕ) : ℕ := by
  classical
  exact ((Finset.range N).filter S).card

/-- Ordinary natural density zero for an arbitrary exceptional set. -/
def HasZeroPredicateDensity (S : ℕ → Prop) : Prop :=
  Tendsto (fun N : ℕ => (predicateCount S N : ℝ) / (N : ℝ)) atTop (𝓝 0)

/-- Arbitrarily late intervals on which Z holds, whose lengths are at least
a fixed positive fraction of their right endpoints. -/
def HasProportionalIntervals (Z : ℕ → Prop) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ start : ℕ, ∃ a length : ℕ,
    start ≤ a ∧ 0 < length ∧
      c * ((a + length : ℕ) : ℝ) ≤ (length : ℝ) ∧
      ∀ j : ℕ, j < length → Z (a + j)

end IndependentZeroBlocks
