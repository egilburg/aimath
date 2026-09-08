import SierpinskiFormal.CommRingObservationFamilies
import SierpinskiFormal.PolynomialMatrixObservation
import SierpinskiFormal.CommRingMatrixGeometry

set_option autoImplicit false
namespace IndependentZeroBlocks
open SierpinskiFormal
open scoped BigOperators

variable {K I J : Type*} [CommRing K] [Fintype I] [Fintype J]

/-- The common observed-word certificate for a finite family of linear
observations of polynomial matrix coefficient vectors. -/
def PolynomialMatrixObservedFamilyCertificate
    (B : I → I → Polynomial K) (U : I → PowerSeries K)
    (b : ℕ) (l : J → Module.Dual K (I → K)) : Prop :=
  let m := polynomialDilationWindowThreshold B b
  ObservedFamilyWordMortal (matrixWindowEnd B b m)
    (fun j => matrixCurrentObservation (l j) m (polynomialDilationWindowThreshold_pos B b))
    (matrixWindowState U m 0)

/-- One central sparse/dense theorem covers joint coefficients, selected
components, and arbitrary finite linear combinations of components. -/
theorem polynomialMatrix_observed_family_classification
    (B : I → I → Polynomial K) (U : I → PowerSeries K)
    (b : ℕ) (hb : 2 ≤ b)
    (hEq : ∀ i, U i = ∑ j, (B i j : PowerSeries K) * dilate b (U j))
    (l : J → Module.Dual K (I → K)) :
    (HasZeroPredicateDensity (fun n => ∃ j, l j (fun i => PowerSeries.coeff n (U i)) ≠ 0) ↔
      PolynomialMatrixObservedFamilyCertificate B U b l) ∧
    (HasUniformRelativeHoles (fun n => ∃ j, l j (fun i => PowerSeries.coeff n (U i)) ≠ 0) ↔
      PolynomialMatrixObservedFamilyCertificate B U b l) ∧
    ((∃ α : ℝ, α < 1 ∧ HasUniformPowerIntervalBound α
      (fun n => ∃ j, l j (fun i => PowerSeries.coeff n (U i)) ≠ 0)) ↔
      PolynomialMatrixObservedFamilyCertificate B U b l) ∧
    (HasPositiveLowerPredicateDensity
      (fun n => ∃ j, l j (fun i => PowerSeries.coeff n (U i)) ≠ 0) ↔
      ¬PolynomialMatrixObservedFamilyCertificate B U b l) := by
  let m := polynomialDilationWindowThreshold B b
  let L : J → Module.Dual K (I × Fin m → K) :=
    fun j => matrixCurrentObservation (l j) m (polynomialDilationWindowThreshold_pos B b)
  have hrec := matrixWindowEnd_recurrence B U b hb hEq
  have hg := commRingMatrix_observed_family_classification b hb
    (fun r => matrixWindowTransition B b m r.val) (matrixWindowState U m) hrec L
  have hsupp : (fun n => ∃ j, L j (matrixWindowState U m n) ≠ 0) =
      (fun n => ∃ j, l j (fun i => PowerSeries.coeff n (U i)) ≠ 0) := by
    funext n
    apply propext
    simp only [L, matrixCurrentObservation_windowState]
  rw [hsupp] at hg
  exact hg

/-- The earlier full-vector certificate is exactly the new observed-family
certificate when the observations are all coordinate projections. -/
theorem polynomialMatrix_jointCertificate_iff_observedCoordinates
    (B : I → I → Polynomial K) (U : I → PowerSeries K)
    (b : ℕ) (hb : 2 ≤ b)
    (hEq : ∀ i, U i = ∑ j, (B i j : PowerSeries K) * dilate b (U j)) :
    PolynomialMatrixSparseCertificate B U b ↔
      PolynomialMatrixObservedFamilyCertificate B U b (fun i => LinearMap.proj i) := by
  have ho := (polynomialMatrix_observed_family_classification B U b hb hEq
    (fun i => LinearMap.proj i)).1
  have hj := (commRing_polynomialMatrix_sparse_geometry_classification B U b hb hEq).1
  exact hj.symm.trans ho

end IndependentZeroBlocks
