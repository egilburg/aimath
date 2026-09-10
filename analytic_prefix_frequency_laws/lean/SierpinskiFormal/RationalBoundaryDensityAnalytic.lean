import SierpinskiFormal.RationalBoundarySeriesBridge
import SierpinskiFormal.BernoulliWeightNormalization

/-! # Analytic dependence of the actual rational boundary density

The parameter domain is the open positive orthant; weights are normalized
to probabilities. This gives an ordinary multivariate real-analytic
extension of the density on the interior of the probability simplex.
-/

noncomputable section
open Filter Set
open scoped BigOperators Topology
namespace IndependentZeroBlocks

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem norm_rationalBoundarySeriesCoefficient_le
    (h : List A)
    (m : (s : Fin h.length) → (Fin (s : ℕ) → A) →
      GapWords (endoMarkerBlock h) × GapWords (endoMarkerBlock h) → ℚ)
    (hm : ∀ s xi i, (m s xi i : ℝ) ∈ Set.Icc 0 1)
    (s : Fin h.length) (xi : Fin (s : ℕ) → A)
    (x y : List (NonMarkerBlock h)) :
    ‖rationalBoundarySeriesCoefficient h m s xi x y‖ ≤ 1 := by
  have hb := hm s xi (gapOfSubtypeList h x, gapOfSubtypeList h y)
  change ‖((m s xi (gapOfSubtypeList h x, gapOfSubtypeList h y) : ℝ) : ℂ)‖ ≤ 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb.1]
  exact hb.2

theorem analyticAt_complexBlockWeight (h : List A)
    (c : Fin h.length → A) (z : A → ℂ) :
    AnalyticAt ℂ (fun u ↦ complexBlockWeight u h c) z := by
  classical
  unfold complexBlockWeight Sierpinski.finWordMonomial
  apply Finset.analyticAt_fun_prod Finset.univ
  intro i _
  exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : A ↦ ℂ) (c i)).analyticAt z

theorem analyticAt_rationalBoundaryComplexExpression
    (h : List A)
    (m : (s : Fin h.length) → (Fin (s : ℕ) → A) →
      GapWords (endoMarkerBlock h) × GapWords (endoMarkerBlock h) → ℚ)
    (hm : ∀ s xi i, (m s xi i : ℝ) ∈ Set.Icc 0 1)
    (z : A → ℂ)
    (hz : Sierpinski.finiteL1Norm
      (fun c : NonMarkerBlock h ↦ complexBlockWeight z h c.1) < 1) :
    AnalyticAt ℂ (rationalBoundaryComplexExpression h m) z := by
  classical
  unfold rationalBoundaryComplexExpression
  simp only [div_eq_mul_inv]
  apply AnalyticAt.fun_mul _ analyticAt_const
  apply Finset.analyticAt_fun_sum Finset.univ
  intro s _
  apply Finset.analyticAt_fun_sum Finset.univ
  intro xi _
  have hxi : AnalyticAt ℂ (fun u : A → ℂ ↦ Sierpinski.finWordMonomial u xi) z := by
    apply Finset.analyticAt_fun_prod Finset.univ
    intro i _
    exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : A ↦ ℂ) (xi i)).analyticAt z
  have hmarker := (analyticAt_complexBlockWeight h (endoMarkerBlock h) z).pow 2
  have hvec : AnalyticAt ℂ
      (fun u : A → ℂ ↦ fun c : NonMarkerBlock h ↦ complexBlockWeight u h c.1) z :=
    AnalyticAt.pi fun c ↦ analyticAt_complexBlockWeight h c.1 z
  have hs := Sierpinski.analyticAt_boundarySeries_of_finiteL1Norm_lt_one
    (rationalBoundarySeriesCoefficient h m s xi)
    (norm_rationalBoundarySeriesCoefficient_le h m hm s xi)
    (fun c : NonMarkerBlock h ↦ complexBlockWeight z h c.1) hz
  have hseries : AnalyticAt ℂ (fun u : A → ℂ ↦
      Sierpinski.boundarySeries (rationalBoundarySeriesCoefficient h m s xi)
        (fun c : NonMarkerBlock h ↦ complexBlockWeight u h c.1)) z :=
    hs.comp (f := fun u : A → ℂ ↦
      fun c : NonMarkerBlock h ↦ complexBlockWeight u h c.1) (x := z) hvec
  exact hxi.fun_mul (hmarker.fun_mul hseries)

/-- An extension to the open positive orthant, using normalized weights. -/
def normalizedRationalBoundaryDensity
    (h : List A)
    (m : (s : Fin h.length) → (Fin (s : ℕ) → A) →
      GapWords (endoMarkerBlock h) × GapWords (endoMarkerBlock h) → ℚ)
    (p : A → ℝ) : ℝ :=
  (rationalBoundaryComplexExpression h m
    (normalizedComplexWeights (complexifyWeightVector p))).re

theorem analyticAt_normalizedRationalBoundaryDensity [Nonempty A]
    (h : List A)
    (m : (s : Fin h.length) → (Fin (s : ℕ) → A) →
      GapWords (endoMarkerBlock h) × GapWords (endoMarkerBlock h) → ℚ)
    (hm : ∀ s xi i, (m s xi i : ℝ) ∈ Set.Icc 0 1)
    (p : A → ℝ) (hp : ∀ a, 0 < p a) :
    AnalyticAt ℝ (normalizedRationalBoundaryDensity h m) p := by
  have hz := finiteL1Norm_nonMarkerBlock_ofReal_lt_one
    (normalizedRealWeights p) (normalizedRealWeights_pos p hp)
    (sum_normalizedRealWeights p hp) h
  have he := analyticAt_rationalBoundaryComplexExpression h m hm
    (complexifyWeightVector (normalizedRealWeights p)) hz
  rw [← normalizedComplexWeights_complexify] at he
  have hc : AnalyticAt ℂ
      (fun z : A → ℂ ↦ rationalBoundaryComplexExpression h m
        (normalizedComplexWeights z)) (complexifyWeightVector p) :=
    he.comp (f := normalizedComplexWeights) (x := complexifyWeightVector p)
      (analyticAt_normalizedComplexWeights _ (complex_totalWeight_ne_zero p hp))
  exact analyticAt_realPart_complexify _ p hc

theorem normalizedRationalBoundaryDensity_eq [Nonempty A]
    (h : List A) (hh : h ≠ [])
    (m : (s : Fin h.length) → (Fin (s : ℕ) → A) →
      GapWords (endoMarkerBlock h) × GapWords (endoMarkerBlock h) → ℚ)
    (hm : ∀ s xi i, (m s xi i : ℝ) ∈ Set.Icc 0 1)
    (p : A → ℝ) (hp : ∀ a, 0 < p a) :
    normalizedRationalBoundaryDensity h m p =
      rationalWordBoundaryDensity h m (normalizedRealWeights p) := by
  unfold normalizedRationalBoundaryDensity
  rw [normalizedComplexWeights_complexify]
  have he := rationalBoundaryComplexExpression_ofReal h hh m hm
    (normalizedRealWeights p) (normalizedRealWeights_pos p hp)
    (sum_normalizedRealWeights p hp)
  exact congrArg Complex.re he

section MatrixDensity

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
variable [TopologicalSpace A] [DiscreteTopology A] [Nonempty A]

/-- Consolidated structural theorem: a single nonempty reset and bounded
rational family, chosen before all positive weights, give an analytic
boundary expression equal to the actual normalized Bernoulli Cesaro limit. -/
theorem exists_commRingMatrix_analytic_rational_boundaryDensity
    (M : A → Matrix ι ι R) (left seed : ι → R) :
    ∃ h : List A, h ≠ [] ∧
      ∃ m : (s : Fin h.length) → (Fin (s : ℕ) → A) →
          GapWords (endoMarkerBlock h) × GapWords (endoMarkerBlock h) → ℚ,
        (∀ s xi i, (m s xi i : ℝ) ∈ Set.Icc 0 1) ∧
        (∀ p : A → ℝ, (∀ a, 0 < p a) →
          AnalyticAt ℝ (normalizedRationalBoundaryDensity h m) p) ∧
        ∀ p : A → ℝ, (∀ a, 0 < p a) →
          Tendsto
            (realCesaroMean (fun n ↦ weightedWordExtensionAverage
              (normalizedRealWeights p)
              (booleanWordIndicator (commRingMatrixCoefficientNonzero M left seed)) n []))
            atTop (𝓝 (normalizedRationalBoundaryDensity h m p)) := by
  obtain ⟨h, hh, m, hbound, hlimit⟩ :=
    exists_commRingMatrix_bounded_rational_boundaryDensity M left seed
  refine ⟨h, hh, m, hbound,
    fun p hp ↦ analyticAt_normalizedRationalBoundaryDensity h m hbound p hp, ?_⟩
  intro p hp
  rw [normalizedRationalBoundaryDensity_eq h hh m hbound p hp]
  exact hlimit _ (normalizedRealWeights_pos p hp) (sum_normalizedRealWeights p hp)

/-- The actual Bernoulli word Cesaro density of every scalar finite matrix
observation over every commutative ring is multivariate real analytic in
strictly positive weights. We normalize on the open positive orthant.
The function is selected before all weights, and is the actual limit. -/
theorem exists_commRingMatrix_analytic_density
    (M : A → Matrix ι ι R) (left seed : ι → R) :
    ∃ d : (A → ℝ) → ℝ,
      (∀ p : A → ℝ, (∀ a, 0 < p a) → AnalyticAt ℝ d p) ∧
      ∀ p : A → ℝ, (∀ a, 0 < p a) →
        Tendsto
          (realCesaroMean (fun n ↦ weightedWordExtensionAverage
            (normalizedRealWeights p)
            (booleanWordIndicator (commRingMatrixCoefficientNonzero M left seed)) n []))
          atTop (𝓝 (d p)) := by
  obtain ⟨h, hh, m, hbound, hlimit⟩ :=
    exists_commRingMatrix_bounded_rational_boundaryDensity M left seed
  refine ⟨normalizedRationalBoundaryDensity h m,
    fun p hp ↦ analyticAt_normalizedRationalBoundaryDensity h m hbound p hp, ?_⟩
  intro p hp
  rw [normalizedRationalBoundaryDensity_eq h hh m hbound p hp]
  exact hlimit _ (normalizedRealWeights_pos p hp) (sum_normalizedRealWeights p hp)

end MatrixDensity

end IndependentZeroBlocks
