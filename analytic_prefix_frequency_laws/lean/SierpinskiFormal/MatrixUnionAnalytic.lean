import SierpinskiFormal.RationalBoundaryDensityAnalytic

set_option autoImplicit false

/-!
# Analytic densities of finite unions of matrix supports

A finite family of scalar matrix observations with a common state index is
combined into one observation over a finite product ring.  Its scalar value
is the tuple of the selected scalar values, so its nonzero support is exactly
their union.  The commutative-ring analytic-density theorem then applies
without any reducedness or nonemptiness assumption on the selected family.
-/

noncomputable section

open Filter
open scoped BigOperators Topology

namespace IndependentZeroBlocks

variable {A J ι R : Type*}
variable [Fintype A] [DecidableEq A] [TopologicalSpace A]
  [DiscreteTopology A] [Nonempty A]
variable [Fintype J] [DecidableEq J]
variable [Fintype ι] [DecidableEq ι]
variable [CommRing R]

/-- The Boolean union of the supports selected by `s`. -/
def matrixUnionPredicate (s : Finset J)
    (M : J → A → Matrix ι ι R) (left seed : J → ι → R)
    (w : List A) : Bool := by
  classical
  exact decide (∃ j, j ∈ s ∧
    commRingMatrixCoefficient (M j) (left j) (seed j) w ≠ 0)

/-- Product-ring transition matrices for a selected family. -/
def matrixUnionProductMatrix (s : Finset J)
    (M : J → A → Matrix ι ι R) :
    A → Matrix ι ι ({j : J // j ∈ s} → R) :=
  fun a i k j ↦ M j.1 a i k

/-- Product-ring observation row for a selected family. -/
def matrixUnionProductLeft (s : Finset J) (left : J → ι → R) :
    ι → ({j : J // j ∈ s} → R) :=
  fun i j ↦ left j.1 i

/-- Product-ring seed for a selected family. -/
def matrixUnionProductSeed (s : Finset J) (seed : J → ι → R) :
    ι → ({j : J // j ∈ s} → R) :=
  fun i j ↦ seed j.1 i

/-- Evaluation of the product-ring word matrix recovers the corresponding
component word matrix. -/
theorem matrixUnionProduct_word_apply (s : Finset J)
    (M : J → A → Matrix ι ι R) (w : List A) (i k : ι)
    (j : {j : J // j ∈ s}) :
    commRingMatrixWord (matrixUnionProductMatrix s M) w i k j =
      commRingMatrixWord (M j.1) w i k := by
  let ev : ({j : J // j ∈ s} → R) →+* R :=
    Pi.evalRingHom (fun _ : {j : J // j ∈ s} ↦ R) j
  have h := congrArg (fun N : Matrix ι ι R ↦ N i k)
    (map_commRingMatrixWord ev (matrixUnionProductMatrix s M) w)
  have hmatrix :
      (fun a ↦ (matrixUnionProductMatrix s M a).map ev) = M j.1 := by
    funext a i' k'
    rfl
  rw [hmatrix] at h
  exact h

/-- Evaluation of the product-ring scalar coefficient recovers the selected
component scalar coefficient. -/
theorem matrixUnionProduct_coefficient_apply (s : Finset J)
    (M : J → A → Matrix ι ι R) (left seed : J → ι → R)
    (w : List A) (j : {j : J // j ∈ s}) :
    commRingMatrixCoefficient
        (matrixUnionProductMatrix s M)
        (matrixUnionProductLeft s left)
        (matrixUnionProductSeed s seed) w j =
      commRingMatrixCoefficient (M j.1) (left j.1) (seed j.1) w := by
  let ev : ({j : J // j ∈ s} → R) →+* R :=
    Pi.evalRingHom (fun _ : {j : J // j ∈ s} ↦ R) j
  have h := map_commRingMatrixCoefficient ev
    (matrixUnionProductMatrix s M)
    (matrixUnionProductLeft s left)
    (matrixUnionProductSeed s seed) w
  have hmatrix :
      (fun a ↦ (matrixUnionProductMatrix s M a).map ev) = M j.1 := by
    funext a i k
    rfl
  rw [hmatrix] at h
  exact h

/-- The product-ring scalar is nonzero exactly when one selected scalar is
nonzero.  This remains valid for the empty selection (the empty product ring
is the zero ring). -/
theorem matrixUnionProduct_coefficient_ne_zero_iff (s : Finset J)
    (M : J → A → Matrix ι ι R) (left seed : J → ι → R)
    (w : List A) :
    commRingMatrixCoefficient
        (matrixUnionProductMatrix s M)
        (matrixUnionProductLeft s left)
        (matrixUnionProductSeed s seed) w ≠ 0 ↔
      ∃ j, j ∈ s ∧
        commRingMatrixCoefficient (M j) (left j) (seed j) w ≠ 0 := by
  classical
  constructor
  · intro h
    by_contra hnone
    push_neg at hnone
    apply h
    funext j
    rw [matrixUnionProduct_coefficient_apply]
    exact hnone j.1 j.2
  · rintro ⟨j, hjs, hj⟩ hzero
    let j' : {j : J // j ∈ s} := ⟨j, hjs⟩
    apply hj
    rw [← matrixUnionProduct_coefficient_apply s M left seed w j']
    exact congrFun hzero j'

/-- The Boolean support of the product-ring observation is the selected
finite union. -/
theorem matrixUnionProduct_nonzero_eq (s : Finset J)
    (M : J → A → Matrix ι ι R) (left seed : J → ι → R) :
    commRingMatrixCoefficientNonzero
        (matrixUnionProductMatrix s M)
        (matrixUnionProductLeft s left)
        (matrixUnionProductSeed s seed) =
      matrixUnionPredicate s M left seed := by
  funext w
  classical
  simp only [commRingMatrixCoefficientNonzero, matrixUnionPredicate]
  by_cases hz : commRingMatrixCoefficient
      (matrixUnionProductMatrix s M)
      (matrixUnionProductLeft s left)
      (matrixUnionProductSeed s seed) w = 0
  · have hnone : ¬ ∃ j, j ∈ s ∧
        commRingMatrixCoefficient (M j) (left j) (seed j) w ≠ 0 := by
      intro hsome
      exact (matrixUnionProduct_coefficient_ne_zero_iff s M left seed w).mpr hsome hz
    simp [nonzeroBool, hz, hnone]
  · have hsome : ∃ j, j ∈ s ∧
        commRingMatrixCoefficient (M j) (left j) (seed j) w ≠ 0 :=
      (matrixUnionProduct_coefficient_ne_zero_iff s M left seed w).mp hz
    simp [nonzeroBool, hz, hsome]

/-- Every selected finite union of scalar matrix supports has an actual
Bernoulli word Cesaro density which depends real-analytically on all strictly
positive (unnormalized) weights. -/
theorem exists_matrixUnion_analytic_density (s : Finset J)
    (M : J → A → Matrix ι ι R) (left seed : J → ι → R) :
    ∃ d : (A → ℝ) → ℝ,
      (∀ p : A → ℝ, (∀ a, 0 < p a) → AnalyticAt ℝ d p) ∧
      ∀ p : A → ℝ, (∀ a, 0 < p a) →
        Tendsto
          (realCesaroMean (fun n ↦ weightedWordExtensionAverage
            (normalizedRealWeights p)
            (booleanWordIndicator (matrixUnionPredicate s M left seed)) n []))
          atTop (𝓝 (d p)) := by
  obtain ⟨d, hdAnalytic, hdLimit⟩ :=
    exists_commRingMatrix_analytic_density
      (matrixUnionProductMatrix s M)
      (matrixUnionProductLeft s left)
      (matrixUnionProductSeed s seed)
  refine ⟨d, hdAnalytic, ?_⟩
  intro p hp
  simpa only [matrixUnionProduct_nonzero_eq] using hdLimit p hp

/-- Simultaneous presentation of the preceding result for every selected
subfamily. -/
theorem forall_finset_exists_matrixUnion_analytic_density
    (M : J → A → Matrix ι ι R) (left seed : J → ι → R) :
    ∀ s : Finset J,
      ∃ d : (A → ℝ) → ℝ,
        (∀ p : A → ℝ, (∀ a, 0 < p a) → AnalyticAt ℝ d p) ∧
        ∀ p : A → ℝ, (∀ a, 0 < p a) →
          Tendsto
            (realCesaroMean (fun n ↦ weightedWordExtensionAverage
              (normalizedRealWeights p)
              (booleanWordIndicator (matrixUnionPredicate s M left seed)) n []))
            atTop (𝓝 (d p)) :=
  fun s ↦ exists_matrixUnion_analytic_density s M left seed

end IndependentZeroBlocks
