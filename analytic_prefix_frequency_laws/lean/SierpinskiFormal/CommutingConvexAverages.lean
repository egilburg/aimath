import SierpinskiFormal.IidCompactWordAverages

/-! # Uniqueness from commuting left and right convex averages

This elementary lemma is the uniqueness step for the reversible Boolean
group-flow argument.  It does not assume an invariant mean or a stable-group
measure theorem.  Its hypotheses say exactly which constant points lie in
which translation hulls.
-/

noncomputable section

open Set

namespace IndependentZeroBlocks

variable {E I J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mapsTo_closedConvexHulls_of_mapsTo
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E →L[ℝ] F) {s : Set E} {t : Set F} (hT : Set.MapsTo T s t) :
    Set.MapsTo T (closedConvexHull ℝ s) (closedConvexHull ℝ t) := by
  exact closedConvexHull_min
    (fun x hx ↦ subset_closedConvexHull (hT hx))
    ((convex_closedConvexHull (𝕜 := ℝ) (s := t)).linear_preimage T.toLinearMap)
    ((isClosed_closedConvexHull (𝕜 := ℝ) (s := t)).preimage T.continuous)

/-- A point fixed by every left operator and lying in the closed convex right
orbit agrees with a point fixed by every right operator and lying in the
closed convex left orbit.  The right operators are contractions and commute
with the left operators. -/
theorem eq_of_mem_commuting_closedConvexHulls
    (L : I → E →L[ℝ] E) (R : J → E →L[ℝ] E) (x a b : E)
    (hcomm : ∀ i j y, L i (R j y) = R j (L i y))
    (hRnorm : ∀ j, ‖R j‖ ≤ 1)
    (hLa : ∀ i, L i a = a) (hRb : ∀ j, R j b = b)
    (ha : a ∈ closedConvexHull ℝ (Set.range fun j ↦ R j x))
    (hb : b ∈ closedConvexHull ℝ (Set.range fun i ↦ L i x)) : a = b := by
  apply eq_of_dist_eq_zero
  apply le_antisymm _ dist_nonneg
  apply le_of_forall_pos_le_add
  intro ε hε
  rw [zero_add]
  rw [closedConvexHull_eq_closure_convexHull] at hb
  obtain ⟨y, hy, hby⟩ := Metric.mem_closure_iff.mp hb ε hε
  let ev : (E →L[ℝ] E) →ₗ[ℝ] E :=
    { toFun := fun P ↦ P x
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have himage : ev '' Set.range L = Set.range (fun i ↦ L i x) := by
    ext y
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨L i, ⟨i, rfl⟩, rfl⟩
  rw [← himage, ← ev.image_convexHull] at hy
  obtain ⟨P, hP, rfl⟩ := hy
  have hPa : P a = a := by
    apply convexHull_min (s := Set.range L)
      (t := {Q : E →L[ℝ] E | Q a = a})
      (by rintro _ ⟨i, rfl⟩; exact hLa i) ?_ hP
    intro Q hQ T hT s t hs ht hst
    change Q a = a at hQ
    change T a = a at hT
    change (s • Q + t • T) a = a
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      hQ, hT, ← add_smul, hst, one_smul]
  have hPR : ∀ j z, P (R j z) = R j (P z) := by
    apply convexHull_min (s := Set.range L)
      (t := {Q : E →L[ℝ] E | ∀ j z, Q (R j z) = R j (Q z)})
      (by rintro _ ⟨i, rfl⟩; exact hcomm i) ?_ hP
    intro Q hQ T hT s t hs ht hst j z
    change ∀ j z, Q (R j z) = R j (Q z) at hQ
    change ∀ j z, T (R j z) = R j (T z) at hT
    change (s • Q + t • T) (R j z) = R j ((s • Q + t • T) z)
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      hQ, hT, map_add, map_smul]
  have hx : ‖P x - b‖ ≤ ε := by
    rw [← dist_eq_norm, dist_comm]
    exact hby.le
  have hball : a ∈ P ⁻¹' Metric.closedBall b ε := by
    apply closedConvexHull_min (s := Set.range fun j ↦ R j x)
      (t := P ⁻¹' Metric.closedBall b ε) ?_
      ((convex_closedBall b ε).linear_preimage P.toLinearMap)
      (Metric.isClosed_closedBall.preimage P.continuous) ha
    rintro _ ⟨j, rfl⟩
    change dist (P (R j x)) b ≤ ε
    rw [hPR, dist_eq_norm, ← hRb j, ← map_sub]
    exact ((R j).le_of_opNorm_le (hRnorm j) (P x - b)).trans (by simpa using hx)
  change dist (P a) b ≤ ε at hball
  simpa only [hPa] using hball

end IndependentZeroBlocks
