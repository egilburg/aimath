import SierpinskiFormal.CommRingObservationGeometry
import SierpinskiFormal.MatrixSparseGeometry

set_option autoImplicit false
namespace IndependentZeroBlocks
open SierpinskiFormal
open scoped BigOperators

section CurrentProjection

variable {K ι : Type*} [CommRing K]

/-- The linear projection from a nonempty trailing window to its current
(`t = 0`) coefficient vector. -/
def matrixCurrentProjection (m : ℕ) (hm : 1 ≤ m) :
    (ι × Fin m → K) →ₗ[K] (ι → K) where
  toFun x i := x (i, ⟨0, by omega⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A functional on current coefficient vectors, lifted to the explicit
trailing-window state. -/
def matrixCurrentObservation (l : Module.Dual K (ι → K))
    (m : ℕ) (hm : 1 ≤ m) : Module.Dual K (ι × Fin m → K) :=
  l.comp (matrixCurrentProjection m hm)

@[simp] theorem matrixCurrentObservation_windowState
    (l : Module.Dual K (ι → K)) (U : ι → PowerSeries K)
    (m n : ℕ) (hm : 1 ≤ m) :
    matrixCurrentObservation l m hm (matrixWindowState U m n) =
      l (fun i ↦ PowerSeries.coeff n (U i)) := by
  apply congrArg l
  funext i
  simp [matrixCurrentObservation, matrixCurrentProjection, matrixWindowState]

end CurrentProjection

section PolynomialMatrix

variable {K ι : Type*} [CommRing K] [Fintype ι]

/-- The intrinsic observed-word certificate for a scalar observation of the
current coefficient vector, using the explicit degree-controlled window
transition. -/
def PolynomialMatrixCurrentObservedWordMortal
    (B : ι → ι → Polynomial K) (U : ι → PowerSeries K)
    (b : ℕ) (l : Module.Dual K (ι → K)) : Prop :=
  let m := polynomialDilationWindowThreshold B b
  ObservedWordMortal (matrixWindowEnd B b m)
    (matrixCurrentObservation l m (polynomialDilationWindowThreshold_pos B b))
    (matrixWindowState U m 0)

/-- Any fixed linear observation of the current coefficient vector in a
finite polynomial matrix Mahler system over an arbitrary commutative ring
has the complete sparse/dense support classification. -/
theorem polynomialMatrix_currentObservation_geometry_classification
    (B : ι → ι → Polynomial K) (U : ι → PowerSeries K)
    (b : ℕ) (hb : 2 ≤ b)
    (hEq : ∀ i, U i = ∑ j, (B i j : PowerSeries K) * dilate b (U j))
    (l : Module.Dual K (ι → K)) :
    (HasZeroPredicateDensity
        (fun n ↦ l (fun i ↦ PowerSeries.coeff n (U i)) ≠ 0) ↔
      PolynomialMatrixCurrentObservedWordMortal B U b l) ∧
    (HasUniformRelativeHoles
        (fun n ↦ l (fun i ↦ PowerSeries.coeff n (U i)) ≠ 0) ↔
      PolynomialMatrixCurrentObservedWordMortal B U b l) ∧
    ((∃ α : ℝ, α < 1 ∧ HasUniformPowerIntervalBound α
        (fun n ↦ l (fun i ↦ PowerSeries.coeff n (U i)) ≠ 0)) ↔
      PolynomialMatrixCurrentObservedWordMortal B U b l) ∧
    (HasPositiveLowerPredicateDensity
        (fun n ↦ l (fun i ↦ PowerSeries.coeff n (U i)) ≠ 0) ↔
      ¬PolynomialMatrixCurrentObservedWordMortal B U b l) := by
  let m := polynomialDilationWindowThreshold B b
  let L : Module.Dual K (ι × Fin m → K) :=
    matrixCurrentObservation l m (polynomialDilationWindowThreshold_pos B b)
  have hrec := matrixWindowEnd_recurrence B U b hb hEq
  have hg := commRingMatrix_observed_support_geometry_classification b hb
    (fun r ↦ matrixWindowTransition B b m r.val) (matrixWindowState U m) hrec L
  have hsupp :
      (fun n ↦ L (matrixWindowState U m n) ≠ 0) =
        (fun n ↦ l (fun i ↦ PowerSeries.coeff n (U i)) ≠ 0) := by
    funext n
    apply propext
    simp only [L, matrixCurrentObservation_windowState]
  rw [hsupp] at hg
  have hEnd : matrixWindowEnd B b m =
      (fun r ↦ Matrix.mulVecLin (matrixWindowTransition B b m r.val)) := by
    rfl
  simp only [PolynomialMatrixCurrentObservedWordMortal, m, L]
  rw [hEnd]
  exact hg

end PolynomialMatrix
end IndependentZeroBlocks
