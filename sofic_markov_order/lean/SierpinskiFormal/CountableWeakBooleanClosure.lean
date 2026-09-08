import SierpinskiFormal.BooleanRowCompactness
import Mathlib.Topology.Algebra.Module.Basic

/-! # Countability of uniformly separated subsets of a countable weak closure -/

noncomputable section
open Filter Topology

namespace IndependentZeroBlocks

theorem countable_of_separated_subset_weak_closure
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S K : Set E) (hS : S.Countable) {ε : ℝ} (hε : 0 < ε)
    (hsep : ∀ x ∈ K, ∀ y ∈ K, x ≠ y → ε ≤ dist x y)
    (hweak : ∀ x ∈ K,
      toWeakSpace ℝ E x ∈ closure (toWeakSpace ℝ E '' S)) :
    K.Countable := by
  let V := Submodule.span ℝ S
  have hV : TopologicalSpace.IsSeparable (closure (V : Set E)) := hS.isSeparable.span.closure
  obtain ⟨D, hD, hVD⟩ := hV
  have hKD : K ⊆ closure D := by
    intro x hx
    have hmono : toWeakSpace ℝ E '' S ⊆ toWeakSpace ℝ E '' (V : Set E) :=
      Set.image_mono Submodule.subset_span
    have hw := closure_mono hmono (hweak x hx)
    rw [← V.convex.toWeakSpace_closure ℝ] at hw
    obtain ⟨z, hz, hzx⟩ := hw
    have he : z = x := (toWeakSpace ℝ E).injective hzx
    exact hVD (he ▸ hz)
  have hchoose : ∀ x : K, ∃ d : D, dist x.val d.val < ε / 3 := by
    intro x
    obtain ⟨d, hd, hdist⟩ := Metric.mem_closure_iff.mp (hKD x.property) (ε / 3) (by positivity)
    exact ⟨⟨d, hd⟩, hdist⟩
  choose d hd using hchoose
  haveI : Countable D := hD.to_subtype
  have hinj : Function.Injective d := by
    intro x y hxy
    apply Subtype.ext
    by_contra hne
    have hs := hsep x.val x.property y.val y.property hne
    have hx := hd x
    have hy := hd y
    have he : (d x).val = (d y).val := congrArg Subtype.val hxy
    have ht := dist_triangle x.val (d x).val y.val
    rw [he, dist_comm (d y).val y.val] at ht
    rw [he] at hx
    linarith
  exact Set.countable_coe_iff.mp hinj.countable

theorem booleanUltrafilterExtension_injective {Y : Type*} :
    Function.Injective (booleanUltrafilterExtension (Y := Y)) := by
  intro g h heq
  funext y
  apply boolIndicator_injective
  have hh := congrArg (fun f : C(Ultrafilter Y, ℝ) ↦ f (pure y)) heq
  simpa only [booleanUltrafilterExtension_pure] using hh

theorem one_le_dist_booleanUltrafilterExtension {Y : Type*}
    (g h : Y → Bool) (hne : g ≠ h) :
    1 ≤ dist (booleanUltrafilterExtension g) (booleanUltrafilterExtension h) := by
  obtain ⟨y, hy⟩ := Function.ne_iff.mp hne
  have heval := ContinuousMap.dist_apply_le_dist
    (f := booleanUltrafilterExtension g) (g := booleanUltrafilterExtension h) (pure y)
  rw [booleanUltrafilterExtension_pure, booleanUltrafilterExtension_pure] at heval
  have hd : dist (boolIndicator (g y)) (boolIndicator (h y)) = 1 := by
    cases hg : g y <;> cases hh : h y <;> simp_all [boolIndicator]
  rwa [hd] at heval

end IndependentZeroBlocks
