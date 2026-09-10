import SierpinskiFormal.PolynomialDilationGaps

set_option autoImplicit false

/-!
# Automatic window threshold for polynomial dilation matrices

For a finite polynomial matrix, the maximum entry degree determines the least
positive integer window whose dilation degree bound is large enough.  This
packages that choice for the matrix zero-block criterion.
-/

namespace IndependentZeroBlocks

open SierpinskiFormal

/-- The maximum natural degree among the entries of a finite polynomial
matrix. -/
noncomputable def polynomialDilationMatrixDegree
    {K ι : Type*} [Semiring K] [Fintype ι]
    (B : ι → ι → Polynomial K) : ℕ :=
  Finset.univ.sup fun i => Finset.univ.sup fun j => (B i j).natDegree

/-- The least positive window predicted by the maximum degree and radix.
For `b ≥ 2`, the quotient is `ceil (D / (b - 1))`. -/
noncomputable def polynomialDilationWindowThreshold
    {K ι : Type*} [Semiring K] [Fintype ι]
    (B : ι → ι → Polynomial K) (b : ℕ) : ℕ :=
  max 1
    ((polynomialDilationMatrixDegree B + (b - 1) - 1) / (b - 1))

theorem entry_natDegree_le_polynomialDilationMatrixDegree
    {K ι : Type*} [Semiring K] [Fintype ι]
    (B : ι → ι → Polynomial K) (i j : ι) :
    (B i j).natDegree ≤ polynomialDilationMatrixDegree B := by
  classical
  exact le_trans (Finset.le_sup (s := Finset.univ) (f := fun j => (B i j).natDegree)
    (Finset.mem_univ j))
    (Finset.le_sup (s := Finset.univ)
      (f := fun i => Finset.univ.sup fun j => (B i j).natDegree)
      (Finset.mem_univ i))

theorem polynomialDilationWindowThreshold_pos
    {K ι : Type*} [Semiring K] [Fintype ι]
    (B : ι → ι → Polynomial K) (b : ℕ) :
    1 ≤ polynomialDilationWindowThreshold B b := by
  exact Nat.le_max_left _ _

/-- The automatic window satisfies the uniform matrix degree bound. -/
theorem polynomialDilationMatrixDegree_le_threshold_mul
    {K ι : Type*} [Semiring K] [Fintype ι]
    (B : ι → ι → Polynomial K) (b : ℕ) (hb : 2 ≤ b) :
    polynomialDilationMatrixDegree B ≤
      (b - 1) * polynomialDilationWindowThreshold B b := by
  let D := polynomialDilationMatrixDegree B
  let k := b - 1
  have hk : 0 < k := by dsimp [k]; omega
  have hkone : 1 ≤ k := hk
  let q := (D + k - 1) / k
  let m := max 1 q
  have hqm : q ≤ m := Nat.le_max_right _ _
  have hdiv : D + k - 1 ≤ m * k + k - 1 :=
    (Nat.div_le_iff_le_mul hk).mp hqm
  have hleft : D + k - 1 = D + (k - 1) := by omega
  have hright : m * k + k - 1 = m * k + (k - 1) := by omega
  have hD : D ≤ m * k := by
    rw [hleft, hright] at hdiv
    exact Nat.le_of_add_le_add_right hdiv
  simpa [D, k, q, m, polynomialDilationWindowThreshold, Nat.mul_comm] using hD

/-- The threshold is the least positive integer satisfying the maximum-degree
bound. -/
theorem polynomialDilationWindowThreshold_minimal
    {K ι : Type*} [Semiring K] [Fintype ι]
    (B : ι → ι → Polynomial K) (b m : ℕ) (hb : 2 ≤ b)
    (hm : 1 ≤ m)
    (hdegree : polynomialDilationMatrixDegree B ≤ (b - 1) * m) :
    polynomialDilationWindowThreshold B b ≤ m := by
  let D := polynomialDilationMatrixDegree B
  let k := b - 1
  have hk : 0 < k := by dsimp [k]; omega
  have hD : D ≤ m * k := by
    simpa [D, k, Nat.mul_comm] using hdegree
  have hceilNumerator : D + k - 1 ≤ m * k + k - 1 := by omega
  have hceil : (D + k - 1) / k ≤ m :=
    (Nat.div_le_iff_le_mul hk).mpr hceilNumerator
  simpa [polynomialDilationWindowThreshold, D, k] using
    (max_le hm hceil)

/-- Matrix zero blocks are controlled by one common block at the automatic
window threshold; callers need not supply a separate degree or window bound. -/
theorem polynomial_dilation_matrix_zeroBlocks_iff_threshold
    {K ι : Type*} [CommRing K] [Fintype ι]
    (B : ι → ι → Polynomial K) (U : ι → PowerSeries K)
    (b : ℕ) (hb : 2 ≤ b)
    (hEq : ∀ i, U i = ∑ j,
      (B i j : PowerSeries K) * dilate b (U j)) :
    HasArbitrarilyLongZeroBlocks
        (fun n i => PowerSeries.coeff n (U i)) ↔
      ∃ s, 1 ≤ s ∧ ∀ i t,
        t < polynomialDilationWindowThreshold B b →
          PowerSeries.coeff (s + t) (U i) = 0 := by
  let m := polynomialDilationWindowThreshold B b
  apply polynomial_dilation_matrix_zeroBlocks_iff B U b m hb
    (polynomialDilationWindowThreshold_pos B b)
  intro i j
  exact le_trans (entry_natDegree_le_polynomialDilationMatrixDegree B i j)
    (polynomialDilationMatrixDegree_le_threshold_mul B b hb)
  exact hEq

end IndependentZeroBlocks

#print axioms IndependentZeroBlocks.polynomialDilationMatrixDegree_le_threshold_mul
#print axioms IndependentZeroBlocks.polynomialDilationWindowThreshold_minimal
#print axioms IndependentZeroBlocks.polynomial_dilation_matrix_zeroBlocks_iff_threshold
