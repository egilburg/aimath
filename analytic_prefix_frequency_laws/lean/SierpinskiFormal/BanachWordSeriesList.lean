import SierpinskiFormal.BanachWordSeries
import SierpinskiFormal.RationalBoundarySeriesBridge

/-! # Exact list-sum interpretation of the analytic Banach word series -/

noncomputable section
open Filter Set Topology IndependentZeroBlocks
open scoped BigOperators
namespace Sierpinski

variable {D F G : Type*} [Fintype D]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]

theorem summable_banach_word_terms (c : List D → F) (hc : ∀ w, ‖c w‖ ≤ 1)
    (p : D → ℂ) (hp : finiteL1Norm p < 1) :
    Summable (fun w ↦ complexWordWeight p w • c w) := by
  apply Summable.of_norm_bounded (summable_norm_complexWordWeight p hp)
  intro w
  rw [norm_smul]
  exact mul_le_of_le_one_right (norm_nonneg _) (hc w)

theorem banachWordSeries_eq_tsum_list (c : List D → F) (hc : ∀ w, ‖c w‖ ≤ 1)
    (p : D → ℂ) (hp : finiteL1Norm p < 1) :
    banachWordSeries c p = ∑' w, complexWordWeight p w • c w := by
  let f : List D → F := fun w ↦ complexWordWeight p w • c w
  have hf := summable_banach_word_terms c hc p hp
  have hs : Summable (fun s : Σ n, Fin n → D ↦ f (List.ofFn s.2)) :=
    List.equivSigmaTuple.symm.summable_iff.mpr hf
  calc
    banachWordSeries c p = ∑' n : ℕ, ∑' x : Fin n → D, f (List.ofFn x) := by
      simp [banachWordSeries, f, complexWordWeight, List.map_ofFn, List.prod_ofFn, tsum_fintype]
    _ = ∑' s : Σ n, Fin n → D, f (List.ofFn s.2) :=
      (hs.tsum_sigma' (fun _ ↦ (hasSum_fintype _).summable)).symm
    _ = ∑' w, f w := List.equivSigmaTuple.symm.tsum_eq f

theorem map_banachWordSeries (c : List D → F) (hc : ∀ w, ‖c w‖ ≤ 1)
    (p : D → ℂ) (hp : finiteL1Norm p < 1) (T : F →L[ℂ] G) :
    T (banachWordSeries c p) = ∑' w, complexWordWeight p w • T (c w) := by
  rw [banachWordSeries_eq_tsum_list c hc p hp,
    T.map_tsum (summable_banach_word_terms c hc p hp)]
  simp only [map_smul]

end Sierpinski
