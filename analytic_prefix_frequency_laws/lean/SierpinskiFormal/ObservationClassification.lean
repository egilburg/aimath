import SierpinskiFormal.ScalarObservationGeometry
import SierpinskiFormal.ObservationCertificate

set_option autoImplicit false
namespace IndependentZeroBlocks

section Noetherian
variable {K V : Type*} [CommRing K] [IsNoetherianRing K]
  [AddCommGroup V] [Module K V] [IsNoetherian K (Module.Dual K V)]

/-- Scalar support is sparse precisely when one digit word is invisible
in every left and right context. No observability premise is supplied. -/
theorem observed_density_zero_iff_mortal
    (b : ℕ) (hb : 2 ≤ b) (T : Fin b → Module.End K V) (u : ℕ → V)
    (hrec : ∀ n (r : Fin b), u (b * n + r.val) = T r (u n))
    (l : Module.Dual K V) :
    HasZeroPredicateDensity (fun n => l (u n) ≠ 0) ↔
      ObservedWordMortal T l (u 0) := by
  obtain ⟨d, rows, a, C, ha, hC⟩ := noetherian_observable_exists_finite_word_model T l
  exact (scalarObservation_density_zero_iff_zero_row_fiber b hb T u hrec l
    d rows a C ha hC).trans
    (observedWordMortal_iff_zero_row_fiber b hb T u hrec l d rows a C ha hC).symm

/-- A single intrinsic annihilation certificate classifies scalar support
geometry, including its positive-density opposite branch. -/
theorem observed_support_geometry_classification
    (b : ℕ) (hb : 2 ≤ b) (T : Fin b → Module.End K V) (u : ℕ → V)
    (hrec : ∀ n (r : Fin b), u (b * n + r.val) = T r (u n))
    (l : Module.Dual K V) :
    (HasZeroPredicateDensity (fun n => l (u n) ≠ 0) ↔
      ObservedWordMortal T l (u 0)) ∧
    (HasUniformRelativeHoles (fun n => l (u n) ≠ 0) ↔
      ObservedWordMortal T l (u 0)) ∧
    ((∃ α : ℝ, α < 1 ∧ HasUniformPowerIntervalBound α (fun n => l (u n) ≠ 0)) ↔
      ObservedWordMortal T l (u 0)) ∧
    (HasPositiveLowerPredicateDensity (fun n => l (u n) ≠ 0) ↔
      ¬ObservedWordMortal T l (u 0)) := by
  have hg := scalarObservation_sparse_geometry_of_finite_word_model b hb T u hrec l
    (noetherian_observable_exists_finite_word_model T l)
  have hc := observed_density_zero_iff_mortal b hb T u hrec l
  exact ⟨hc, hg.1.symm.trans hc, hg.2.1.symm.trans hc,
    hg.2.2.2.trans (not_congr hc)⟩

end Noetherian

/-- Over any field, finite dimension is the only state-space hypothesis:
the representation need not be minimal, observable, or normalized. -/
theorem finiteDimensional_observed_support_geometry
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (b : ℕ) (hb : 2 ≤ b) (T : Fin b → Module.End K V) (u : ℕ → V)
    (hrec : ∀ n (r : Fin b), u (b * n + r.val) = T r (u n))
    (l : Module.Dual K V) :
    (HasZeroPredicateDensity (fun n => l (u n) ≠ 0) ↔
      ObservedWordMortal T l (u 0)) ∧
    (HasUniformRelativeHoles (fun n => l (u n) ≠ 0) ↔
      ObservedWordMortal T l (u 0)) ∧
    ((∃ α : ℝ, α < 1 ∧ HasUniformPowerIntervalBound α (fun n => l (u n) ≠ 0)) ↔
      ObservedWordMortal T l (u 0)) ∧
    (HasPositiveLowerPredicateDensity (fun n => l (u n) ≠ 0) ↔
      ¬ObservedWordMortal T l (u 0)) := by
  exact observed_support_geometry_classification b hb T u hrec l

end IndependentZeroBlocks
