import SierpinskiFormal.LinearObservationDescent
import SierpinskiFormal.ObservationClassification

set_option autoImplicit false
namespace IndependentZeroBlocks
open scoped BigOperators

/-- Intrinsic observed-word mortality can be read solely from the scalar
output sequence of a digit recurrence. -/
theorem observedWordMortal_iff_output_contexts
    {K V : Type*} [CommSemiring K] [AddCommMonoid V] [Module K V]
    (b : ℕ) (T : Fin b → Module.End K V) (u : ℕ → V)
    (hrec : ∀ n (r : Fin b), u (b * n + r.val) = T r (u n))
    (l : Module.Dual K V) :
    ObservedWordMortal T l (u 0) ↔
      ∃ w : List (Fin b), ∀ v z : List (Fin b),
        l (u (Nat.ofDigits b ((v ++ w ++ z).map Fin.val))) = 0 := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w, fun v z ↦ ?_⟩
    rw [← linearWord_apply_digitRecurrence_seed b T u hrec]
    exact hw v z
  · rintro ⟨w, hw⟩
    refine ⟨w, fun v z ↦ ?_⟩
    rw [linearWord_apply_digitRecurrence_seed b T u hrec]
    exact hw v z

section CoordinateRow

variable {R ι : Type*} [CommRing R] [Fintype ι]

/-- A standard coordinate vector, packaged noncomputably so downstream
statements need no explicit decidable-equality argument. -/
noncomputable def coordinateUnit (i : ι) : ι → R := by
  classical
  exact Pi.single i 1

/-- The dual functional represented by a finite coordinate row. -/
noncomputable def coordinateRowDual (a : ι → R) : Module.Dual R (ι → R) := by
  classical
  exact ∑ i, a i • LinearMap.proj i

@[simp] theorem coordinateRowDual_apply (a x : ι → R) :
    coordinateRowDual a x = ∑ i, a i * x i := by
  classical
  simp [coordinateRowDual, smul_eq_mul]

/-- Every functional on a finite coordinate module is represented by its
values on the standard coordinate vectors. -/
theorem dual_apply_eq_sum_single (l : Module.Dual R (ι → R)) (x : ι → R) :
    l x = ∑ i, l (coordinateUnit i) * x i := by
  classical
  have hx : x = ∑ i, x i • coordinateUnit (R := R) i := by
    funext j
    simp [coordinateUnit, Pi.single_apply]
  conv_lhs => rw [hx]
  simp [mul_comm]

end CoordinateRow

section ArbitraryCommRing

variable {K ι : Type*} [CommRing K] [Fintype ι]

/-- Scalar support geometry for finite matrix digit recurrences over an
arbitrary commutative ring.  The finite coefficients descend to a
Noetherian subring; the scalar output and intrinsic word certificate are
unchanged by that descent. -/
theorem commRingMatrix_observed_support_geometry_classification
    (b : ℕ) (hb : 2 ≤ b) (M : Fin b → Matrix ι ι K) (u : ℕ → ι → K)
    (hrec : ∀ n (r : Fin b),
      u (b * n + r.val) = Matrix.mulVecLin (M r) (u n))
    (l : Module.Dual K (ι → K)) :
    (HasZeroPredicateDensity (fun n ↦ l (u n) ≠ 0) ↔
      ObservedWordMortal (fun r ↦ Matrix.mulVecLin (M r)) l (u 0)) ∧
    (HasUniformRelativeHoles (fun n ↦ l (u n) ≠ 0) ↔
      ObservedWordMortal (fun r ↦ Matrix.mulVecLin (M r)) l (u 0)) ∧
    ((∃ α : ℝ, α < 1 ∧
      HasUniformPowerIntervalBound α (fun n ↦ l (u n) ≠ 0)) ↔
      ObservedWordMortal (fun r ↦ Matrix.mulVecLin (M r)) l (u 0)) ∧
    (HasPositiveLowerPredicateDensity (fun n ↦ l (u n) ≠ 0) ↔
      ¬ObservedWordMortal (fun r ↦ Matrix.mulVecLin (M r)) l (u 0)) := by
  classical
  let a : ι → K := fun i ↦ l (coordinateUnit i)
  obtain ⟨S, hS, M', u', a', hM', hu', ha', hrec', hout⟩ :=
    linearObservation_exists_noetherian_descent b hb M u a hrec
  let l' : Module.Dual S (ι → S) := coordinateRowDual a'
  have hl (n : ℕ) : ((l' (u' n) : S) : K) = l (u n) := by
    rw [show l' (u' n) = ∑ i, a' i * u' n i by
      exact coordinateRowDual_apply a' (u' n)]
    rw [hout n, dual_apply_eq_sum_single l (u n)]
  have hsupport : (fun n ↦ l' (u' n) ≠ 0) = (fun n ↦ l (u n) ≠ 0) := by
    funext n
    apply propext
    simp only [ne_eq, ← Subring.coe_eq_zero_iff, hl]
  have hmortal :
      ObservedWordMortal (fun r ↦ Matrix.mulVecLin (M' r)) l' (u' 0) ↔
        ObservedWordMortal (fun r ↦ Matrix.mulVecLin (M r)) l (u 0) := by
    rw [observedWordMortal_iff_output_contexts b
        (fun r ↦ Matrix.mulVecLin (M' r)) u' hrec' l',
      observedWordMortal_iff_output_contexts b
        (fun r ↦ Matrix.mulVecLin (M r)) u hrec l]
    apply exists_congr
    intro w
    constructor
    · intro hw v z
      apply (show l' (u' (Nat.ofDigits b ((v ++ w ++ z).map Fin.val))) = 0 ↔
        l (u (Nat.ofDigits b ((v ++ w ++ z).map Fin.val))) = 0 by
          rw [← Subring.coe_eq_zero_iff, hl]).mp
      exact hw v z
    · intro hw v z
      apply (show l' (u' (Nat.ofDigits b ((v ++ w ++ z).map Fin.val))) = 0 ↔
        l (u (Nat.ofDigits b ((v ++ w ++ z).map Fin.val))) = 0 by
          rw [← Subring.coe_eq_zero_iff, hl]).mpr
      exact hw v z
  have hgeometry := observed_support_geometry_classification b hb
    (fun r ↦ Matrix.mulVecLin (M' r)) u' hrec' l'
  rw [hsupport, hmortal] at hgeometry
  exact hgeometry

end ArbitraryCommRing
end IndependentZeroBlocks
