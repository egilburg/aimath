import SierpinskiFormal.CommRingObservationGeometry
import SierpinskiFormal.ObservationFamilies

set_option autoImplicit false
namespace IndependentZeroBlocks

/-- Over every commutative ring, a finite family of observed outputs admits
one common invisible word precisely in the sparse branch. -/
theorem commRingMatrix_observed_family_classification
    {K I J : Type*} [CommRing K] [Fintype I] [Fintype J]
    (b : ℕ) (hb : 2 ≤ b) (M : Fin b → Matrix I I K) (u : ℕ → I → K)
    (hrec : ∀ n (r : Fin b), u (b * n + r.val) = Matrix.mulVecLin (M r) (u n))
    (l : J → Module.Dual K (I → K)) :
    (HasZeroPredicateDensity (fun n => ∃ i, l i (u n) ≠ 0) ↔
      ObservedFamilyWordMortal (fun r => Matrix.mulVecLin (M r)) l (u 0)) ∧
    (HasUniformRelativeHoles (fun n => ∃ i, l i (u n) ≠ 0) ↔
      ObservedFamilyWordMortal (fun r => Matrix.mulVecLin (M r)) l (u 0)) ∧
    ((∃ α : ℝ, α < 1 ∧ HasUniformPowerIntervalBound α (fun n => ∃ i, l i (u n) ≠ 0)) ↔
      ObservedFamilyWordMortal (fun r => Matrix.mulVecLin (M r)) l (u 0)) ∧
    (HasPositiveLowerPredicateDensity (fun n => ∃ i, l i (u n) ≠ 0) ↔
      ¬ObservedFamilyWordMortal (fun r => Matrix.mulVecLin (M r)) l (u 0)) := by
  have hc := fun i => commRingMatrix_observed_support_geometry_classification b hb M u hrec (l i)
  have hg := finite_support_geometry_of_component_classification
    (fun i n => l i (u n) ≠ 0)
    (fun i => ObservedWordMortal (fun r => Matrix.mulVecLin (M r)) (l i) (u 0))
    (fun i => (hc i).1) (fun i => (hc i).2.1) (fun i => (hc i).2.2.2)
  have hs := observedFamilyWordMortal_iff (fun r => Matrix.mulVecLin (M r)) l (u 0)
  exact ⟨hg.1.trans hs.symm, hg.2.1.trans hs.symm, hg.2.2.1.trans hs.symm,
    hg.2.2.2.trans (not_congr hs.symm)⟩

/-- Sparsity synchronizes automatically for finitely many observations.
Each observation may initially have a different invisible word. -/
theorem commRingMatrix_observed_family_sparse_iff_individual
    {K I J : Type*} [CommRing K] [Fintype I] [Fintype J]
    (b : ℕ) (hb : 2 ≤ b) (M : Fin b → Matrix I I K) (u : ℕ → I → K)
    (hrec : ∀ n (r : Fin b), u (b * n + r.val) = Matrix.mulVecLin (M r) (u n))
    (l : J → Module.Dual K (I → K)) :
    HasZeroPredicateDensity (fun n => ∃ i, l i (u n) ≠ 0) ↔
      ∀ i, HasZeroPredicateDensity (fun n => l i (u n) ≠ 0) := by
  rw [(commRingMatrix_observed_family_classification b hb M u hrec l).1,
    observedFamilyWordMortal_iff]
  exact forall_congr' (fun i => (commRingMatrix_observed_support_geometry_classification
    b hb M u hrec (l i)).1.symm)

end IndependentZeroBlocks
