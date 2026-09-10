import SierpinskiFormal.BooleanResetArtinianDensity
import SierpinskiFormal.MatrixFamilyArtinianRealization
import SierpinskiFormal.MatrixBooleanAnalytic

/-! # One reset-boundary theorem for every Boolean observation of a matrix family

A finite matrix family over any commutative ring is realized in one finite
Artinian module. One minimum-length reset is then chosen before every Boolean
operation and every positive letter law. The bounded rational boundary family
of each operation gives its actual analytic word-length Cesaro density.
-/

noncomputable section
open Filter Set
open scoped BigOperators Topology
namespace IndependentZeroBlocks

/-- The exact-length probability of a Boolean matrix observation, expressed
as a plain finite sum without any topology on the alphabet. -/
def matrixBooleanWordProbability {R A J ι : Type*} [CommRing R]
    [Fintype A] [Fintype ι] [DecidableEq ι]
    (p : A → ℝ) (op : (J → Bool) → Bool)
    (M : J → A → Matrix ι ι R) (left seed : J → ι → R) (n : ℕ) : ℝ :=
  ∑ w : Fin n → A, wordWeight p (List.ofFn w) *
    boolIndicator (op (fun j ↦
      nonzeroBool (commRingMatrixCoefficient (M j) (left j) (seed j) (List.ofFn w))))

section ModuleBounds

variable {R A X : Type*} [CommRing R] [IsArtinianRing R]
  [AddCommGroup X] [Module R X] [Module.Finite R X]
  [Fintype A] [Nonempty A] [DecidableEq A]
  [TopologicalSpace A] [DiscreteTopology A]

/-- The reset depends only on the module action. All later finite Boolean
observations have bounded rational boundary data independent of the law. -/
theorem exists_commonReset_bounded_moduleBooleanBoundaryDensity
    (T : A → Module.End R X) :
    ∃ h : List A, h ≠ [] ∧
      ∀ (d : ℕ) (op : (Fin d → Bool) → Bool)
        (left : Fin d → Module.Dual R X) (seed : X),
      ∃ m : (s : Fin h.length) → (Fin (s : ℕ) → A) →
          GapWords (endoMarkerBlock h) × GapWords (endoMarkerBlock h) → ℚ,
        (∀ s xi i, (m s xi i : ℝ) ∈ Set.Icc (0 : ℝ) 1) ∧
        ∀ (p : A → ℝ), (∀ a, 0 < p a) → (∑ a, p a = 1) →
          Tendsto (realCesaroMean (fun n ↦ weightedWordExtensionAverage p
            (booleanWordIndicator (moduleBooleanCoefficientNonzero op T left seed)) n []))
            atTop (𝓝 (rationalWordBoundaryDensity h m p)) := by
  classical
  obtain ⟨h, hh, hmin, U, V0, hfac, hbij, hall⟩ :=
    exists_commonReset_moduleBooleanBoundaryMeans_forall_positive_laws T
  refine ⟨h, hh, ?_⟩
  intro d op left seed
  obtain ⟨m, hm⟩ := hall d op left seed
  let pRef : A → ℝ := uniformAlphabetWeight
  have hpRefPos : ∀ a, 0 < pRef a := fun a ↦ uniformAlphabetWeight_pos a
  have hpRef1 : ∑ a, pRef a = 1 := sum_uniformAlphabetWeight
  have hRef := hm pRef hpRefPos hpRef1
  have hpBlock0 : ∀ c : Fin h.length → A,
      0 ≤ blockWeight pRef h.length c :=
    blockWeight_nonneg pRef (fun a ↦ (hpRefPos a).le) h.length
  have hpBlock1 : ∑ c : Fin h.length → A, blockWeight pRef h.length c = 1 :=
    sum_blockWeight_eq_one pRef hpRef1 h.length
  refine ⟨m, ?_, ?_⟩
  · intro s xi i
    apply realCesaroLimit_mem_Icc _ (hRef.1 s xi i)
    intro n
    unfold moduleBooleanBoundaryCentralSequence
    apply weightedWordExtensionAverage_mem_Icc _ hpBlock0 hpBlock1
    · intro w
      simp only [booleanWordIndicator_apply, boolIndicator]
      split <;> norm_num
    · intro w
      simp only [booleanWordIndicator_apply, boolIndicator]
      split <;> norm_num
  · intro p hp hp1
    exact (hm p hp hp1).2

end ModuleBounds

section MatrixFamily

variable {R A J ι : Type*} [CommRing R]
  [Fintype A] [Nonempty A] [DecidableEq A]
  [TopologicalSpace A] [DiscreteTopology A]
  [Fintype J] [Fintype ι] [DecidableEq ι]

theorem matrixBooleanWordProbability_eq_weightedAverage
    (p : A → ℝ) (op : (J → Bool) → Bool)
    (M : J → A → Matrix ι ι R) (left seed : J → ι → R) (n : ℕ) :
    matrixBooleanWordProbability p op M left seed n =
      weightedWordExtensionAverage p
        (booleanWordIndicator (matrixBooleanPredicate op M left seed)) n [] := by
  rw [weightedWordExtensionAverage_eq_tuple_sum]
  rfl

/-- Every Boolean operation on a fixed finite matrix family uses the same
reset. Each operation has one bounded rational family chosen before all
positive normalized laws. Empty families and state types are allowed. -/
theorem exists_commonReset_matrixBoolean_rational_boundaryDensity
    (M : J → A → Matrix ι ι R) (left seed : J → ι → R) :
    ∃ h : List A, h ≠ [] ∧
      ∀ op : (J → Bool) → Bool,
      ∃ m : (s : Fin h.length) → (Fin (s : ℕ) → A) →
          GapWords (endoMarkerBlock h) × GapWords (endoMarkerBlock h) → ℚ,
        (∀ s xi i, (m s xi i : ℝ) ∈ Set.Icc (0 : ℝ) 1) ∧
        ∀ (p : A → ℝ), (∀ a, 0 < p a) → (∑ a, p a = 1) →
          Tendsto (realCesaroMean (fun n ↦ weightedWordExtensionAverage p
            (booleanWordIndicator (matrixBooleanPredicate op M left seed)) n []))
            atTop (𝓝 (rationalWordBoundaryDensity h m p)) := by
  classical
  obtain ⟨S, Q, T, v, rows, hS, hArt, hFin, hFree, hword⟩ :=
    exists_matrixFamily_faithfulArtinian_realization M left seed
  letI := hFin
  obtain ⟨h, hh, hall⟩ := exists_commonReset_bounded_moduleBooleanBoundaryDensity T
  refine ⟨h, hh, ?_⟩
  intro op
  let E : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let op' : (Fin (Fintype.card J) → Bool) → Bool := fun b ↦ op (fun j ↦ b (E j))
  let rows' : Fin (Fintype.card J) → Module.Dual Q.Carrier (J → ι → Q.Carrier) :=
    fun j ↦ rows (E.symm j)
  obtain ⟨m, hbound, hm⟩ := hall (Fintype.card J) op' rows' v
  have hpred : moduleBooleanCoefficientNonzero op' T rows' v =
      matrixBooleanPredicate op M left seed := by
    funext w
    change op (fun j ↦ moduleCoefficientNonzero T (rows (E.symm (E j))) v w) = _
    simp only [Equiv.symm_apply_apply, hword]
    rfl
  refine ⟨m, hbound, ?_⟩
  intro p hp hp1
  simpa only [hpred] using hm p hp hp1

end MatrixFamily

section IntrinsicHeadline

variable {R A J ι : Type*} [CommRing R]
  [Fintype A] [Nonempty A] [DecidableEq A]
  [Fintype J] [Fintype ι] [DecidableEq ι]

/-- Consolidated central theorem: one reset for the whole finite matrix
family, and for every Boolean operation a bounded rational boundary family
whose very boundary function is analytic and equals the actual density. -/
theorem exists_commonReset_matrixBoolean_analytic_rational_boundaryDensity
    (M : J → A → Matrix ι ι R) (left seed : J → ι → R) :
    ∃ h : List A, h ≠ [] ∧
      ∀ op : (J → Bool) → Bool,
      ∃ m : (s : Fin h.length) → (Fin (s : ℕ) → A) →
          GapWords (endoMarkerBlock h) × GapWords (endoMarkerBlock h) → ℚ,
        (∀ s xi i, (m s xi i : ℝ) ∈ Set.Icc (0 : ℝ) 1) ∧
        (∀ p : A → ℝ, (∀ a, 0 < p a) →
          AnalyticAt ℝ (normalizedRationalBoundaryDensity h m) p ∧
            normalizedRationalBoundaryDensity h m p ∈ Set.Icc (0 : ℝ) 1) ∧
        ∀ p : A → ℝ, (∀ a, 0 < p a) →
          Tendsto (realCesaroMean
            (matrixBooleanWordProbability (normalizedRealWeights p) op M left seed))
            atTop (𝓝 (normalizedRationalBoundaryDensity h m p)) := by
  classical
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  obtain ⟨h, hh, hall⟩ :=
    exists_commonReset_matrixBoolean_rational_boundaryDensity M left seed
  refine ⟨h, hh, ?_⟩
  intro op
  obtain ⟨m, hbound, hm⟩ := hall op
  have hlimit : ∀ p : A → ℝ, (∀ a, 0 < p a) →
      Tendsto (realCesaroMean (fun n ↦ weightedWordExtensionAverage
        (normalizedRealWeights p)
        (booleanWordIndicator (matrixBooleanPredicate op M left seed)) n []))
        atTop (𝓝 (normalizedRationalBoundaryDensity h m p)) := by
    intro p hp
    rw [normalizedRationalBoundaryDensity_eq h hh m hbound p hp]
    exact hm _ (normalizedRealWeights_pos p hp) (sum_normalizedRealWeights p hp)
  refine ⟨m, hbound, ?_, ?_⟩
  swap
  · intro p hp
    change Tendsto (realCesaroMean (fun n ↦
      matrixBooleanWordProbability (normalizedRealWeights p) op M left seed n))
      atTop (𝓝 (normalizedRationalBoundaryDensity h m p))
    simpa only [matrixBooleanWordProbability_eq_weightedAverage] using hlimit p hp
  intro p hp
  refine ⟨analyticAt_normalizedRationalBoundaryDensity h m hbound p hp, ?_⟩
  apply realCesaroLimit_mem_Icc _ (hlimit p hp)
  intro n
  apply weightedWordExtensionAverage_mem_Icc _
    (fun a ↦ (normalizedRealWeights_pos p hp a).le) (sum_normalizedRealWeights p hp)
  · intro w
    simp only [booleanWordIndicator_apply, boolIndicator]
    split <;> norm_num
  · intro w
    simp only [booleanWordIndicator_apply, boolIndicator]
    split <;> norm_num

end IntrinsicHeadline

end IndependentZeroBlocks
