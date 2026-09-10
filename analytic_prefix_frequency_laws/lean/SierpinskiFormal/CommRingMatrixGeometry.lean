import SierpinskiFormal.MatrixCoefficientDescent
import SierpinskiFormal.MatrixCertificateTransfer

set_option autoImplicit false
namespace IndependentZeroBlocks
open SierpinskiFormal
open scoped BigOperators

/-- Descent preserves the exact automatic window threshold. -/
theorem matrixDescendedPolynomial_windowThreshold
    {K ι : Type*} [CommRing K] [Fintype ι]
    (B : ι → ι → Polynomial K) (U : ι → PowerSeries K) (b : ℕ) :
    polynomialDilationWindowThreshold (matrixDescendedPolynomial B U) b =
      polynomialDilationWindowThreshold B b := by
  simp [polynomialDilationWindowThreshold, polynomialDilationMatrixDegree,
    matrixDescendedPolynomial_natDegree]

/-- Injective coefficient descent preserves zero windows exactly. -/
theorem matrixDescendedSeries_window_eq_zero_iff
    {K ι : Type*} [CommRing K] [Fintype ι]
    (B : ι → ι → Polynomial K) (U : ι → PowerSeries K)
    (b : ℕ) (hb : 2 ≤ b)
    (hEq : ∀ i, U i = ∑ j, (B i j : PowerSeries K) * dilate b (U j))
    (m n : ℕ) :
    matrixWindowState (matrixDescendedSeries B U b hb hEq) m n = 0 ↔
      matrixWindowState U m n = 0 := by
  have hs := matrixWindowState_support_eq (matrixDescendedSeries B U b hb hEq) m
  rw [matrixDescendedSeries_jointSupport B U b hb hEq,
    ← matrixWindowState_support_eq U m] at hs
  have hn := congrFun hs n
  have hi := not_congr (Iff.of_eq hn)
  simpa only [not_not] using hi

/-- The ambient and descended reachable-span certificates are equivalent,
not merely sufficient for the same geometric conclusion. -/
theorem polynomialMatrix_certificate_descent_iff
    {K ι : Type*} [CommRing K] [Fintype ι]
    (B : ι → ι → Polynomial K) (U : ι → PowerSeries K)
    (b : ℕ) (hb : 2 ≤ b)
    (hEq : ∀ i, U i = ∑ j, (B i j : PowerSeries K) * dilate b (U j)) :
    PolynomialMatrixSparseCertificate (matrixDescendedPolynomial B U)
      (matrixDescendedSeries B U b hb hEq) b ↔
        PolynomialMatrixSparseCertificate B U b := by
  rw [polynomialMatrix_certificate_iff_zero_window_fiber _ _ b hb
      (matrixDescendedSeries_equation B U b hb hEq),
    polynomialMatrix_certificate_iff_zero_window_fiber B U b hb hEq,
    matrixDescendedPolynomial_windowThreshold]
  exact exists_congr fun w => forall_congr' fun n =>
    matrixDescendedSeries_window_eq_zero_iff B U b hb hEq _ _

/-- The Noetherian-ring hypothesis is unnecessary: finite input coefficients
lie in a Noetherian subring, and both support and certificate descend exactly. -/
theorem commRing_polynomialMatrix_sparse_geometry_classification
    {K ι : Type*} [CommRing K] [Fintype ι]
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
  have h := polynomialMatrix_sparse_geometry_classification
    (matrixDescendedPolynomial B U) (matrixDescendedSeries B U b hb hEq) b hb
    (matrixDescendedSeries_equation B U b hb hEq)
  rw [matrixDescendedSeries_jointSupport B U b hb hEq] at h
  have hc := polynomialMatrix_certificate_descent_iff B U b hb hEq
  exact ⟨h.1.trans hc, h.2.1.trans hc, h.2.2.1.trans hc,
    h.2.2.2.trans (not_congr hc)⟩

/-- Ordinary support density zero and uniform holes coincide over every
commutative coefficient ring, without an external representation hypothesis. -/
theorem commRing_polynomialMatrix_zeroDensity_iff_uniformRelativeHoles
    {K ι : Type*} [CommRing K] [Fintype ι]
    (B : ι → ι → Polynomial K) (U : ι → PowerSeries K)
    (b : ℕ) (hb : 2 ≤ b)
    (hEq : ∀ i, U i = ∑ j, (B i j : PowerSeries K) * dilate b (U j)) :
    HasZeroPredicateDensity (polynomialMatrixJointSupport U) ↔
      HasUniformRelativeHoles (polynomialMatrixJointSupport U) := by
  have h := commRing_polynomialMatrix_sparse_geometry_classification B U b hb hEq
  exact h.1.trans h.2.1.symm

/-- Every such coefficient support lies on exactly one side of the
zero-density / positive-lower-density divide. -/
theorem commRing_polynomialMatrix_density_dichotomy
    {K ι : Type*} [CommRing K] [Fintype ι]
    (B : ι → ι → Polynomial K) (U : ι → PowerSeries K)
    (b : ℕ) (hb : 2 ≤ b)
    (hEq : ∀ i, U i = ∑ j, (B i j : PowerSeries K) * dilate b (U j)) :
    HasZeroPredicateDensity (polynomialMatrixJointSupport U) ∨
      HasPositiveLowerPredicateDensity (polynomialMatrixJointSupport U) := by
  have h := commRing_polynomialMatrix_sparse_geometry_classification B U b hb hEq
  by_cases hc : PolynomialMatrixSparseCertificate B U b
  · exact Or.inl (h.1.mpr hc)
  · exact Or.inr (h.2.2.2.mpr hc)

end IndependentZeroBlocks
