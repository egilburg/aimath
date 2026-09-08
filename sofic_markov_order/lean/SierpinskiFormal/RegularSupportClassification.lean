import SierpinskiFormal.ForbiddenWordGeometry
import SierpinskiFormal.RadixRegularRepresentation

set_option autoImplicit false
namespace IndependentZeroBlocks

/-- Intrinsic support classification for regular sequences over every
commutative ring; no supplied matrix representation is required. -/
theorem radixRegular_support_classification
    {K : Type*} [CommRing K] (b : ℕ) (hb : 2 ≤ b)
    (f : ℕ → K) (hregular : IsRadixRegular b f) :
    (HasZeroPredicateDensity (fun n => f n ≠ 0) ↔
      HasForbiddenDigitWord b (fun n => f n ≠ 0)) ∧
    (HasUniformRelativeHoles (fun n => f n ≠ 0) ↔
      HasForbiddenDigitWord b (fun n => f n ≠ 0)) ∧
    ((∃ α : ℝ, α < 1 ∧ HasUniformPowerIntervalBound α (fun n => f n ≠ 0)) ↔
      HasForbiddenDigitWord b (fun n => f n ≠ 0)) ∧
    (HasPositiveLowerPredicateDensity (fun n => f n ≠ 0) ↔
      ¬HasForbiddenDigitWord b (fun n => f n ≠ 0)) := by
  obtain ⟨d, M, u, l, hrec, hout⟩ := radixRegular_exists_matrix_representation b hb f hregular
  let T : Fin b → Module.End K (Fin d → K) := fun r => Matrix.mulVecLin (M r)
  have hg := commRingMatrix_observed_family_classification b hb M u hrec (fun _ : Unit => l)
  have hf := observedFamilyWordMortal_iff_forbidden_word b hb T u hrec (fun _ : Unit => l)
  have hsupp : (fun n => ∃ _i : Unit, l (u n) ≠ 0) = (fun n => f n ≠ 0) := by
    funext n
    apply propext
    simp [hout]
  rw [hsupp] at hg hf
  change ObservedFamilyWordMortal T (fun _ : Unit => l) (u 0) ↔
    HasForbiddenDigitWord b (fun n => f n ≠ 0) at hf
  exact ⟨hg.1.trans hf, hg.2.1.trans hf, hg.2.2.1.trans hf,
    hg.2.2.2.trans (not_congr hf)⟩

/-- Quantitative certificate form: every sparse regular sequence has a
nonempty forbidden word giving explicit global and translated bounds. -/
theorem radixRegular_sparse_quantitative_certificate
    {K : Type*} [CommRing K] (b : ℕ) (hb : 2 ≤ b)
    (f : ℕ → K) (hregular : IsRadixRegular b f)
    (hz : HasZeroPredicateDensity (fun n => f n ≠ 0)) :
    ∃ w : List (Fin b), 0 < w.length ∧
      AvoidsDigitWord b (fun n => f n ≠ 0) w ∧
      (∀ k, predicateCount (fun n => f n ≠ 0) ((b ^ w.length) ^ k) ≤
        (b ^ w.length - 1) ^ k) ∧
      (∀ a L, 1 ≤ L → (intervalPredicateCount (fun n => f n ≠ 0) a L : ℝ) ≤
        ((2 * (b ^ w.length - 1) : ℕ) : ℝ) * (L : ℝ) ^
          (Real.log ((b ^ w.length - 1 : ℕ) : ℝ) /
            Real.log ((b ^ w.length : ℕ) : ℝ))) := by
  obtain ⟨w, hlen, hw⟩ := (radixRegular_support_classification b hb f hregular).1.mp hz
  exact ⟨w, hlen, hw, avoidsDigitWord_radix_count b hb _ w hlen hw,
    avoidsDigitWord_interval_count b hb _ w hlen hw⟩

end IndependentZeroBlocks
