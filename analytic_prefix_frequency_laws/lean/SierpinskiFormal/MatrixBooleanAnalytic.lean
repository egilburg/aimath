import SierpinskiFormal.AnalyticWordMeanClosure
import SierpinskiFormal.MatrixUnionAnalytic
import SierpinskiFormal.BooleanUnionExpansion

/-! # Actual analytic densities for finite Boolean matrix observations

This is a closure application of the scalar boundary theorem. Finite unions
are encoded over product rings, while arbitrary Boolean indicators are finite
linear combinations of union indicators. The proof does not claim that a
Booleanized scalar series is recognizable or give a common reset for all
Boolean components.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace IndependentZeroBlocks

variable {A J ι R : Type*}
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [TopologicalSpace A] [DiscreteTopology A]
variable [Fintype J] [DecidableEq J] [Fintype ι] [DecidableEq ι] [CommRing R]

def matrixBooleanPredicate (op : (J → Bool) → Bool)
    (M : J → A → Matrix ι ι R) (left seed : J → ι → R)
    (w : List A) : Bool :=
  op (fun j ↦ nonzeroBool (commRingMatrixCoefficient (M j) (left j) (seed j) w))

theorem hasAnalyticWordMean_matrixUnion (s : Finset J)
    (M : J → A → Matrix ι ι R) (left seed : J → ι → R) :
    HasAnalyticWordMean (booleanWordIndicator (matrixUnionPredicate s M left seed)) :=
  exists_matrixUnion_analytic_density s M left seed

theorem booleanUnionIndicator_matrixCoefficient (s : Finset J)
    (M : J → A → Matrix ι ι R) (left seed : J → ι → R) (w : List A) :
    booleanUnionIndicator s (fun j ↦
      nonzeroBool (commRingMatrixCoefficient (M j) (left j) (seed j) w)) =
      booleanWordIndicator (matrixUnionPredicate s M left seed) w := by
  classical
  simp [booleanUnionIndicator, matrixUnionPredicate, nonzeroBool]

/-- Every finite Boolean combination of scalar matrix nonzero tests has an
actual analytic mean, including constant predicates and empty families. -/
theorem hasAnalyticWordMean_matrixBoolean
    (op : (J → Bool) → Bool)
    (M : J → A → Matrix ι ι R) (left seed : J → ι → R) :
    HasAnalyticWordMean (booleanWordIndicator (matrixBooleanPredicate op M left seed)) := by
  apply hasAnalyticWordMean_of_finite_linear_combination
    (g := fun s : Finset J ↦ booleanWordIndicator (matrixUnionPredicate s M left seed))
    (hg := fun s ↦ hasAnalyticWordMean_matrixUnion s M left seed)
    (c := booleanUnionConstant op) (a := booleanUnionCoefficient op)
  intro w
  have h := boolIndicator_eq_constant_add_sum_unionIndicators op
    (fun j ↦ nonzeroBool (commRingMatrixCoefficient (M j) (left j) (seed j) w))
  simpa only [booleanWordIndicator_apply, matrixBooleanPredicate,
    booleanUnionIndicator_matrixCoefficient] using h

/-- The finite Boolean closure has one analytic actual density function on
positive normalized weights. Its values lie in the probability interval.
The scalar reset-boundary theorem remains the structural input. -/
theorem exists_matrixBoolean_analytic_density
    (op : (J → Bool) → Bool)
    (M : J → A → Matrix ι ι R) (left seed : J → ι → R) :
    ∃ d : (A → ℝ) → ℝ,
      (∀ p : A → ℝ, (∀ a, 0 < p a) →
        AnalyticAt ℝ d p ∧ d p ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ p : A → ℝ, (∀ a, 0 < p a) →
        Tendsto (realCesaroMean (fun n ↦ weightedWordExtensionAverage
          (normalizedRealWeights p)
          (booleanWordIndicator (matrixBooleanPredicate op M left seed)) n []))
          atTop (𝓝 (d p)) := by
  obtain ⟨d, hd, hlimit⟩ := hasAnalyticWordMean_matrixBoolean op M left seed
  refine ⟨d, ?_, hlimit⟩
  intro p hp
  refine ⟨hd p hp, realCesaroLimit_mem_Icc (fun n ↦ ?_) (hlimit p hp)⟩
  apply weightedWordExtensionAverage_mem_Icc _
    (fun a ↦ (normalizedRealWeights_pos p hp a).le) (sum_normalizedRealWeights p hp)
  · intro w
    simp only [booleanWordIndicator_apply, boolIndicator]
    split <;> norm_num
  · intro w
    simp only [booleanWordIndicator_apply, boolIndicator]
    split <;> norm_num

end IndependentZeroBlocks
