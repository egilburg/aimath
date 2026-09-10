import SierpinskiFormal.ArtinianCoefficientDescent
import SierpinskiFormal.ArtinianBlockDensity
import SierpinskiFormal.ArtinianBoundaryBounds

/-! # The rational boundary density law over arbitrary commutative rings

Finite matrix observations are transported faithfully to an Artinian
coefficient ring before choosing a minimum-image-length reset. The resulting
Boolean language and all its weighted word averages are unchanged.
-/

noncomputable section
open Filter Set
open scoped Topology BigOperators

namespace IndependentZeroBlocks

variable {R A ι : Type*} [CommRing R] [Fintype A]
  [Fintype ι] [DecidableEq ι]

def matrixObservationRow (left : ι → R) : Module.Dual R (ι → R) where
  toFun v := ∑ i, left i * v i
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum, mul_left_comm]

@[simp] theorem matrixObservationRow_apply (left v : ι → R) :
    matrixObservationRow left v = ∑ i, left i * v i := rfl

theorem endoWord_mulVecLin (M : A → Matrix ι ι R) (w : List A) :
    endoWord (fun a ↦ (M a).mulVecLin) w =
      (commRingMatrixWord M w).mulVecLin := by
  induction w with
  | nil =>
      ext x i
      simp [endoWord, commRingMatrixWord]
  | cons a w ih =>
      simp only [endoWord, List.map_cons, List.prod_cons] at ih ⊢
      rw [ih]
      ext x i
      simp [commRingMatrixWord, Matrix.mulVec_mulVec]

theorem commRingMatrixCoefficient_eq_moduleScalar
    (M : A → Matrix ι ι R) (left seed : ι → R) (w : List A) :
    commRingMatrixCoefficient M left seed w =
      matrixObservationRow left (endoWord (fun a ↦ (M a).mulVecLin) w seed) := by
  rw [endoWord_mulVecLin]
  rfl

theorem commRingMatrixCoefficientNonzero_eq_moduleScalar
    (M : A → Matrix ι ι R) (left seed : ι → R) :
    commRingMatrixCoefficientNonzero M left seed =
      fun w ↦ nonzeroBool
        (matrixObservationRow left (endoWord (fun a ↦ (M a).mulVecLin) w seed)) := by
  funext w
  exact congrArg nonzeroBool (commRingMatrixCoefficient_eq_moduleScalar M left seed w)

/-- The pure probability-side boundary law. The coefficients and reset word
are fixed independently of the strictly positive Bernoulli law. -/
def rationalWordBoundaryDensity (h : List A)
    (m : (s : Fin h.length) → (Fin (s : ℕ) → A) →
      GapWords (endoMarkerBlock h) × GapWords (endoMarkerBlock h) → ℚ)
    (p : A → ℝ) : ℝ :=
  (∑ s : Fin h.length, ∑ xi : Fin (s : ℕ) → A,
    wordWeight p (List.ofFn xi) *
      (∑' i : GapWords (endoMarkerBlock h) × GapWords (endoMarkerBlock h),
        moduleBoundaryWeight (blockWeight p h.length) (endoMarkerBlock h) i *
          (m s xi i : ℝ))) / (h.length : ℝ)

section Density

variable [TopologicalSpace A] [DiscreteTopology A] [Nonempty A] [DecidableEq A]

/-- Every scalar coefficient of a finite matrix tuple over any commutative
ring has the rational geometric boundary-density law. No Noetherian or
Artinian hypothesis is imposed on the original coefficient ring.

The reset is chosen after a faithful Artinian realization; no original-ring
minimum-rank or image-preservation assertion is made. The single rational
family is chosen before all positive normalized laws. -/
theorem exists_commRingMatrix_rational_boundaryDensity
    (M : A → Matrix ι ι R) (left seed : ι → R) :
    ∃ h : List A, h ≠ [] ∧
      ∃ m : (s : Fin h.length) → (Fin (s : ℕ) → A) →
          GapWords (endoMarkerBlock h) × GapWords (endoMarkerBlock h) → ℚ,
        ∀ (p : A → ℝ), (∀ a, 0 < p a) → (∑ a, p a = 1) →
          Tendsto
            (realCesaroMean (fun n ↦ weightedWordExtensionAverage p
              (booleanWordIndicator (commRingMatrixCoefficientNonzero M left seed)) n []))
            atTop (𝓝 (rationalWordBoundaryDensity h m p)) := by
  classical
  obtain ⟨S, Q, M', left', seed', _, hword⟩ :=
    exists_artinian_matrixObservation_lift M left seed
  obtain ⟨h, hh, _, U, V0, _, _, m, hm⟩ :=
    exists_minLengthWord_moduleBoundaryMeans_forall_positive_laws
      (fun a ↦ (M' a).mulVecLin) (matrixObservationRow left') seed'
  refine ⟨h, hh, m, ?_⟩
  intro p hp hp1
  have hpred : moduleCoefficientNonzero
      (fun a ↦ (M' a).mulVecLin) (matrixObservationRow left') seed' =
      commRingMatrixCoefficientNonzero M left seed := by
    calc
      _ = commRingMatrixCoefficientNonzero M' left' seed' :=
        (commRingMatrixCoefficientNonzero_eq_moduleScalar M' left' seed').symm
      _ = _ := funext hword
  simpa only [hpred, rationalWordBoundaryDensity] using (hm p hp hp1).2

/-- Bounded, law-independent rational boundary coefficients for every finite
matrix observation over every commutative ring. This is the final ring-general
scalar boundary-density endpoint. -/
theorem exists_commRingMatrix_bounded_rational_boundaryDensity
    (M : A → Matrix ι ι R) (left seed : ι → R) :
    ∃ h : List A, h ≠ [] ∧
      ∃ m : (s : Fin h.length) → (Fin (s : ℕ) → A) →
          GapWords (endoMarkerBlock h) × GapWords (endoMarkerBlock h) → ℚ,
        (∀ s xi i, (m s xi i : ℝ) ∈ Set.Icc 0 1) ∧
        ∀ (p : A → ℝ), (∀ a, 0 < p a) → (∑ a, p a = 1) →
          Tendsto
            (realCesaroMean (fun n ↦ weightedWordExtensionAverage p
              (booleanWordIndicator (commRingMatrixCoefficientNonzero M left seed)) n []))
            atTop (𝓝 (rationalWordBoundaryDensity h m p)) := by
  classical
  obtain ⟨S, Q, M', left', seed', _, hword⟩ :=
    exists_artinian_matrixObservation_lift M left seed
  obtain ⟨h, hh, m, hbound, hm⟩ :=
    exists_minLengthWord_bounded_moduleBoundaryMeans_forall_positive_laws
      (fun a ↦ (M' a).mulVecLin) (matrixObservationRow left') seed'
  refine ⟨h, hh, m, hbound, ?_⟩
  intro p hp hp1
  have hpred : moduleCoefficientNonzero
      (fun a ↦ (M' a).mulVecLin) (matrixObservationRow left') seed' =
      commRingMatrixCoefficientNonzero M left seed := by
    calc
      _ = commRingMatrixCoefficientNonzero M' left' seed' :=
        (commRingMatrixCoefficientNonzero_eq_moduleScalar M' left' seed').symm
      _ = _ := funext hword
  simpa only [hpred, rationalWordBoundaryDensity] using hm p hp hp1

end Density

end IndependentZeroBlocks
