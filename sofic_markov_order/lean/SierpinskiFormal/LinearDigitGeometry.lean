import SierpinskiFormal.LinearDigitRepresentation
import SierpinskiFormal.ZeroCylinderGeometry
import SierpinskiFormal.OptimalUniformClassification

set_option autoImplicit false
namespace IndependentZeroBlocks

section Semiring
variable {K V : Type*} [Semiring K] [AddCommMonoid V] [Module K V]

/-- A common reachable-span annihilator produces holes at every location.
The zero digit need only fix the seed; padded word lengths are retained. -/
theorem linearDigit_uniformRelativeHoles_of_common_word
    (b : ℕ) (hb : 2 ≤ b) (T : Fin b → Module.End K V) (u : ℕ → V)
    (hrec : ∀ n (r : Fin b), u (b * n + r.val) = T r (u n))
    (hkill : ∃ w : List (Fin b), ∀ x ∈ linearReachableSpan T (u 0),
      linearWord T w x = 0) :
    HasUniformRelativeHoles (fun n => u n ≠ 0) := by
  obtain ⟨v, hv⟩ := hkill
  let w : List (Fin b) := ⟨0, by omega⟩ :: v
  have hw : ∀ x ∈ linearReachableSpan T (u 0), linearWord T w x = 0 := by
    intro x hx
    simp only [w, linearWord_cons, Module.End.mul_apply, hv x hx, map_zero]
  have hell : 0 < w.length := by simp [w]
  let B := b ^ w.length
  let d := Nat.ofDigits b (w.map Fin.val)
  have hB : 2 ≤ B := hb.trans (Nat.le_self_pow (by omega) b)
  have hd : d < B := by
    have h := Nat.ofDigits_lt_base_pow_length (by omega : 1 < b)
      (show ∀ r ∈ w.map Fin.val, r < b from by
        intro r hr
        obtain ⟨r', _, rfl⟩ := List.mem_map.mp hr
        exact r'.isLt)
    simpa [B, d] using h
  apply hasUniformRelativeHoles_of_radix_zeroCylinder B d hB hd
  intro k q j hj hbad
  apply hbad
  have hz := linearDigit_common_word_zero_cylinder b hb T u hrec w hw
    (w.length * k) q j (by simpa only [B, ← pow_mul] using hj)
  simpa only [B, d, ← pow_mul, Nat.mul_add, Nat.mul_one] using hz

end Semiring

section Noetherian
variable {K V : Type*} [Semiring K] [AddCommMonoid V] [Module K V]
  [IsNoetherian K V]

/-- Noetherian modules supply the finite generation needed for one common
annihilator; fields and finite-dimensional spaces are a special case. -/
theorem noetherian_reachable_mortal_iff_pointwise
    {ι : Type*} (T : ι → Module.End K V) (v0 : V) :
    (∃ w : List ι, ∀ x ∈ linearReachableSpan T v0, linearWord T w x = 0) ↔
      ∀ v : List ι, ∃ w : List ι, linearWord T w (linearWord T v v0) = 0 := by
  constructor
  · rintro ⟨w, hw⟩ v
    exact ⟨w, hw _ (linearWord_mem_linearReachableSpan T v0 v)⟩
  · intro hk
    exact linearReachableSpan_common_word_of_pointwise_of_fg T v0
      (isNoetherian_def.mp inferInstance _) hk


/-- The sparse branch of a finite-dimensional digit recurrence is exactly
annihilation of its entire reachable span by one padded digit word. -/
theorem linearDigit_density_zero_iff_reachable_annihilator
    (b : ℕ) (hb : 2 ≤ b) (T : Fin b → Module.End K V) (u : ℕ → V)
    (hrec : ∀ n (r : Fin b), u (b * n + r.val) = T r (u n)) :
    HasZeroPredicateDensity (fun n => u n ≠ 0) ↔
      ∃ w : List (Fin b), ∀ x ∈ linearReachableSpan T (u 0), linearWord T w x = 0 := by
  constructor
  · intro hz
    exact (noetherian_reachable_mortal_iff_pointwise T (u 0)).mpr
      (linearDigit_pointwise_mortal_of_zeroDensity b hb T u hrec hz)
  · intro hk
    exact (linearDigit_uniformRelativeHoles_of_common_word b hb T u hrec hk).toZeroPredicateDensity

/-- Failure of common annihilation gives a full surviving radix cone and
therefore positive lower support density. -/
theorem linearDigit_positive_lower_density_of_no_annihilator
    (b : ℕ) (hb : 2 ≤ b) (T : Fin b → Module.End K V) (u : ℕ → V)
    (hrec : ∀ n (r : Fin b), u (b * n + r.val) = T r (u n))
    (hnot : ¬∃ w : List (Fin b), ∀ x ∈ linearReachableSpan T (u 0), linearWord T w x = 0) :
    HasPositiveLowerPredicateDensity (fun n => u n ≠ 0) := by
  have himm : ∃ v : List (Fin b), ∀ w : List (Fin b),
      linearWord T w (linearWord T v (u 0)) ≠ 0 := by
    rw [noetherian_reachable_mortal_iff_pointwise T (u 0)] at hnot
    push_neg at hnot
    exact hnot
  obtain ⟨v, hv⟩ := himm
  let n := Nat.ofDigits b (v.map Fin.val)
  apply positiveLowerPredicateDensity_of_full_radixCone _ b hb n
  intro k j hj hz
  obtain ⟨w, _, _, hw⟩ := linearDigit_descendant_word b hb T u hrec n k j hj
  apply hv w
  rw [linearWord_apply_digitRecurrence_seed b T u hrec v]
  exact hw.trans hz

theorem linearDigit_positive_lower_density_iff_no_annihilator
    (b : ℕ) (hb : 2 ≤ b) (T : Fin b → Module.End K V) (u : ℕ → V)
    (hrec : ∀ n (r : Fin b), u (b * n + r.val) = T r (u n)) :
    HasPositiveLowerPredicateDensity (fun n => u n ≠ 0) ↔
      ¬∃ w : List (Fin b), ∀ x ∈ linearReachableSpan T (u 0), linearWord T w x = 0 := by
  constructor
  · intro hd hk
    exact hd.not_zeroDensity
      ((linearDigit_density_zero_iff_reachable_annihilator b hb T u hrec).mpr hk)
  · exact linearDigit_positive_lower_density_of_no_annihilator b hb T u hrec

theorem linearDigit_uniformRelativeHoles_iff_reachable_annihilator
    (b : ℕ) (hb : 2 ≤ b) (T : Fin b → Module.End K V) (u : ℕ → V)
    (hrec : ∀ n (r : Fin b), u (b * n + r.val) = T r (u n)) :
    HasUniformRelativeHoles (fun n => u n ≠ 0) ↔
      ∃ w : List (Fin b), ∀ x ∈ linearReachableSpan T (u 0), linearWord T w x = 0 := by
  constructor
  · intro hh
    exact (linearDigit_density_zero_iff_reachable_annihilator b hb T u hrec).mp
      hh.toZeroPredicateDensity
  · exact linearDigit_uniformRelativeHoles_of_common_word b hb T u hrec

/-- Counting, ordinary density and uniform local holes coincide for every
finite-dimensional linear digit recurrence over an arbitrary field. -/
theorem linearDigit_sparse_geometry_equivalences
    (b : ℕ) (hb : 2 ≤ b) (T : Fin b → Module.End K V) (u : ℕ → V)
    (hrec : ∀ n (r : Fin b), u (b * n + r.val) = T r (u n)) :
    (HasZeroPredicateDensity (fun n => u n ≠ 0) ↔
      HasUniformRelativeHoles (fun n => u n ≠ 0)) ∧
    (HasZeroPredicateDensity (fun n => u n ≠ 0) ↔
      ∃ α : ℝ, α < 1 ∧ HasUniformPowerIntervalBound α (fun n => u n ≠ 0)) ∧
    (HasZeroPredicateDensity (fun n => u n ≠ 0) ∨
      HasPositiveLowerPredicateDensity (fun n => u n ≠ 0)) := by
  have hholes : HasZeroPredicateDensity (fun n => u n ≠ 0) ↔
      HasUniformRelativeHoles (fun n => u n ≠ 0) :=
    (linearDigit_density_zero_iff_reachable_annihilator b hb T u hrec).trans
      (linearDigit_uniformRelativeHoles_iff_reachable_annihilator b hb T u hrec).symm
  refine ⟨hholes, ?_, ?_⟩
  · constructor
    · intro hz
      obtain ⟨α, _, hα, hbound⟩ := (hholes.mp hz).exists_uniform_interval_power_bound
      exact ⟨α, hα, hbound⟩
    · rintro ⟨α, hα, hbound⟩
      exact hbound.toPowerPredicateBound.toZeroPredicateDensity hα
  · by_cases hk : ∃ w : List (Fin b), ∀ x ∈ linearReachableSpan T (u 0), linearWord T w x = 0
    · exact Or.inl ((linearDigit_density_zero_iff_reachable_annihilator b hb T u hrec).mpr hk)
    · exact Or.inr (linearDigit_positive_lower_density_of_no_annihilator b hb T u hrec hk)

end Noetherian
end IndependentZeroBlocks
