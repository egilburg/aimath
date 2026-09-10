import SierpinskiFormal.MatrixWindowLift
import SierpinskiFormal.FiniteWindowSupport
import SierpinskiFormal.LinearDigitGeometry
import Mathlib.LinearAlgebra.Matrix.ToLin

set_option autoImplicit false
namespace IndependentZeroBlocks
open SierpinskiFormal
open scoped BigOperators

/-- Joint support of a family of coefficient series. -/
def polynomialMatrixJointSupport {K ι : Type*} [CommRing K]
    (U : ι → PowerSeries K) (n : ℕ) : Prop :=
  ∃ i, PowerSeries.coeff n (U i) ≠ 0

/-- The window support is exactly a finite union of right translates of the
original support. This is an equality, not merely a one-way estimate. -/
theorem matrixWindowState_support_eq
    {K ι : Type*} [CommRing K] (U : ι → PowerSeries K) (m : ℕ) :
    (fun n => matrixWindowState U m n ≠ 0) =
      backwardWindowSupport (polynomialMatrixJointSupport U) m := by
  funext n
  apply propext
  rw [backwardWindowSupport_iff_sub]
  constructor
  · intro hn
    have hp : ∃ p, matrixWindowState U m n p ≠ 0 := by
      by_contra h
      push_neg at h
      exact hn (funext h)
    obtain ⟨⟨i,t⟩, hp⟩ := hp
    have htn : t.val ≤ n := by
      by_contra h
      exact hp (by simp [matrixWindowState, h])
    exact ⟨t.val, t.isLt, htn, i, by simpa [matrixWindowState, htn] using hp⟩
  · rintro ⟨t, ht, htn, i, hi⟩ hz
    have h := congrFun hz (i, (⟨t, ht⟩ : Fin m))
    exact hi (by simpa [matrixWindowState, htn] using h)

/-- The explicit window transition regarded as a linear endomorphism. -/
noncomputable def matrixWindowEnd
    {K ι : Type*} [CommRing K] [Fintype ι]
    (B : ι → ι → Polynomial K) (b m : ℕ) (r : Fin b) :
    Module.End K (ι × Fin m → K) :=
  Matrix.mulVecLin (matrixWindowTransition B b m r.val)

/-- The degree-controlled window satisfies its digit recurrence as a vector
identity with explicit linear maps. -/
theorem matrixWindowEnd_recurrence
    {K ι : Type*} [CommRing K] [Fintype ι]
    (B : ι → ι → Polynomial K) (U : ι → PowerSeries K)
    (b : ℕ) (hb : 2 ≤ b)
    (hEq : ∀ i, U i = ∑ j, (B i j : PowerSeries K) * dilate b (U j)) :
    let m := polynomialDilationWindowThreshold B b
    ∀ n (r : Fin b), matrixWindowState U m (b * n + r.val) =
      matrixWindowEnd B b m r (matrixWindowState U m n) := by
  dsimp only
  intro n r
  funext p
  exact matrixWindowState_digit_recurrence B U b
    (polynomialDilationWindowThreshold B b) hb
    (polynomialDilationWindowThreshold_pos B b)
    (fun i j => (entry_natDegree_le_polynomialDilationMatrixDegree B i j).trans
      (polynomialDilationMatrixDegree_le_threshold_mul B b hb))
    hEq n r.val r.isLt p

/-- One word annihilates the reachable span of the explicit automatic window
lift. There is no supplied digit representation in this certificate. -/
def PolynomialMatrixSparseCertificate
    {K ι : Type*} [CommRing K] [Fintype ι]
    (B : ι → ι → Polynomial K) (U : ι → PowerSeries K) (b : ℕ) : Prop :=
  let m := polynomialDilationWindowThreshold B b
  ∃ w : List (Fin b), ∀ x ∈ linearReachableSpan (matrixWindowEnd B b m)
    (matrixWindowState U m 0), linearWord (matrixWindowEnd B b m) w x = 0

section Noetherian
variable {K ι : Type*} [CommRing K] [IsNoetherianRing K] [Fintype ι]

/-- Density zero for an arbitrary-degree polynomial matrix dilation system
is equivalent to one annihilating word on its degree-controlled reachable span.
This holds over Noetherian commutative rings, including fields and integers. -/
theorem polynomialMatrix_density_zero_iff_certificate
    (B : ι → ι → Polynomial K) (U : ι → PowerSeries K)
    (b : ℕ) (hb : 2 ≤ b)
    (hEq : ∀ i, U i = ∑ j, (B i j : PowerSeries K) * dilate b (U j)) :
    HasZeroPredicateDensity (polynomialMatrixJointSupport U) ↔
      PolynomialMatrixSparseCertificate B U b := by
  let m := polynomialDilationWindowThreshold B b
  have hrec := matrixWindowEnd_recurrence B U b hb hEq
  have hz := linearDigit_density_zero_iff_reachable_annihilator b hb
    (matrixWindowEnd B b m) (matrixWindowState U m) hrec
  rw [matrixWindowState_support_eq U m,
    hasZeroPredicateDensity_backwardWindowSupport_iff _
      (polynomialDilationWindowThreshold_pos B b)] at hz
  exact hz

theorem polynomialMatrix_uniformRelativeHoles_iff_certificate
    (B : ι → ι → Polynomial K) (U : ι → PowerSeries K)
    (b : ℕ) (hb : 2 ≤ b)
    (hEq : ∀ i, U i = ∑ j, (B i j : PowerSeries K) * dilate b (U j)) :
    HasUniformRelativeHoles (polynomialMatrixJointSupport U) ↔
      PolynomialMatrixSparseCertificate B U b := by
  let m := polynomialDilationWindowThreshold B b
  have hh := linearDigit_uniformRelativeHoles_iff_reachable_annihilator b hb
    (matrixWindowEnd B b m) (matrixWindowState U m)
    (matrixWindowEnd_recurrence B U b hb hEq)
  rw [matrixWindowState_support_eq U m,
    hasUniformRelativeHoles_backwardWindowSupport_iff _
      (polynomialDilationWindowThreshold_pos B b)] at hh
  exact hh

theorem polynomialMatrix_positive_lower_density_iff_no_certificate
    (B : ι → ι → Polynomial K) (U : ι → PowerSeries K)
    (b : ℕ) (hb : 2 ≤ b)
    (hEq : ∀ i, U i = ∑ j, (B i j : PowerSeries K) * dilate b (U j)) :
    HasPositiveLowerPredicateDensity (polynomialMatrixJointSupport U) ↔
      ¬PolynomialMatrixSparseCertificate B U b := by
  let m := polynomialDilationWindowThreshold B b
  have hd := linearDigit_positive_lower_density_iff_no_annihilator b hb
    (matrixWindowEnd B b m) (matrixWindowState U m)
    (matrixWindowEnd_recurrence B U b hb hEq)
  rw [matrixWindowState_support_eq U m,
    hasPositiveLowerPredicateDensity_backwardWindowSupport_iff _
      (polynomialDilationWindowThreshold_pos B b)] at hd
  exact hd

/-- One central algebra/density/local-geometry theorem for every finite
polynomial matrix dilation system over a Noetherian commutative ring. -/
theorem polynomialMatrix_sparse_geometry_classification
    (B : ι → ι → Polynomial K) (U : ι → PowerSeries K)
    (b : ℕ) (hb : 2 ≤ b)
    (hEq : ∀ i, U i = ∑ j, (B i j : PowerSeries K) * dilate b (U j)) :
    (HasZeroPredicateDensity (polynomialMatrixJointSupport U) ↔
      PolynomialMatrixSparseCertificate B U b) ∧
    (HasUniformRelativeHoles (polynomialMatrixJointSupport U) ↔
      PolynomialMatrixSparseCertificate B U b) ∧
    ((∃ α : ℝ, α < 1 ∧ HasUniformPowerIntervalBound α
      (polynomialMatrixJointSupport U)) ↔ PolynomialMatrixSparseCertificate B U b) ∧
    (HasPositiveLowerPredicateDensity (polynomialMatrixJointSupport U) ↔
      ¬PolynomialMatrixSparseCertificate B U b) := by
  have hz := polynomialMatrix_density_zero_iff_certificate B U b hb hEq
  have hh := polynomialMatrix_uniformRelativeHoles_iff_certificate B U b hb hEq
  refine ⟨hz, hh, ?_, polynomialMatrix_positive_lower_density_iff_no_certificate B U b hb hEq⟩
  constructor
  · rintro ⟨α, hα, hbound⟩
    exact hz.mp (hbound.toPowerPredicateBound.toZeroPredicateDensity hα)
  · intro hk
    obtain ⟨α, _, hα, hbound⟩ := (hh.mpr hk).exists_uniform_interval_power_bound
    exact ⟨α, hα, hbound⟩

end Noetherian
end IndependentZeroBlocks
