import SierpinskiFormal.ConditionalLimitIdentification
import Mathlib.MeasureTheory.Constructions.Pi

/-! # The finite-prefix filtration generates the full one-sided path sigma algebra -/

noncomputable section
open MeasureTheory

namespace IndependentZeroBlocks

variable {A : Type*} [MeasurableSpace A]

/-- Information in coordinates zero through `n`, inclusive. -/
def prefixFiltration : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → A)) where
  seq n := ⨆ k ≤ n, MeasurableSpace.comap (fun ω : ℕ → A ↦ ω k) inferInstance
  mono' _ _ h := biSup_mono fun _ ↦ fun hk ↦ hk.trans h
  le' _ := iSup₂_le fun k _ ↦ (measurable_pi_apply k).comap_le

theorem iSup_prefixFiltration :
    (⨆ n, (prefixFiltration (A := A)) n) =
      (inferInstance : MeasurableSpace (ℕ → A)) := by
  apply le_antisymm
  · exact iSup_le (prefixFiltration.le)
  · change (⨆ k, MeasurableSpace.comap (fun ω : ℕ → A ↦ ω k) inferInstance) ≤ _
    apply iSup_le
    intro k
    exact le_iSup_of_le k (le_iSup_of_le k (le_iSup_of_le le_rfl le_rfl))

theorem measurable_prefix_coordinate {n k : ℕ} (hk : k ≤ n) :
    @Measurable (ℕ → A) A (prefixFiltration n) inferInstance (fun ω ↦ ω k) := by
  apply Measurable.of_comap_le
  exact le_iSup_of_le k (le_iSup_of_le hk le_rfl)

end IndependentZeroBlocks
