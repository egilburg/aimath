import SierpinskiFormal.FiniteStateMatrixObservation
import SierpinskiFormal.MatrixBooleanBoundaryDensity

/-! # Common boundary densities after finite-state transduction

Finite-state source dynamics are absorbed into the observation representation.
The accepted common-reset theorem is then reused without changing its proof.
The reset is common to all initial states and all Boolean operations.
-/

noncomputable section
open Filter Set
open scoped BigOperators Topology

namespace IndependentZeroBlocks

/-- A finite-length expectation of an output-word observable under IID input
letters. This definition keeps the observable distinct from its source. -/
def transducedWordAverage {Q B A : Type*} [Fintype B]
    (T : FiniteStateTransducer Q B A) (p : B → ℝ)
    (F : List A → ℝ) (q : Q) (n : ℕ) : ℝ :=
  ∑ w : Fin n → B, wordWeight p (List.ofFn w) * F (T.outputWord q (List.ofFn w))

/-- Boolean evaluation of scalar observations, independently of any source. -/
def scalarWordBooleanValue {R A J : Type*} [Zero R]
    (op : (J → Bool) → Bool) (f : J → List A → R) (w : List A) : ℝ :=
  boolIndicator (op (fun j ↦ nonzeroBool (f j w)))

section MatrixTransduction

variable {Q B A J ι R : Type*} [CommRing R]
  [Fintype Q] [DecidableEq Q] [Fintype B] [DecidableEq B] [Nonempty B]
  [Fintype J] [Fintype ι] [DecidableEq ι]

/-- The enlarged family includes every starting state. -/
def transducedMatrixFamily (T : FiniteStateTransducer Q B A)
    (M : J → A → Matrix ι ι R) : (Q × J) → B → Matrix (Q × ι) (Q × ι) R :=
  fun qj ↦ T.matrixLift (M qj.2)

def transducedLeftFamily (left : J → ι → R) : (Q × J) → (Q × ι) → R :=
  fun qj ↦ FiniteStateTransducer.leftLift qj.1 (left qj.2)

def transducedSeedFamily (seed : J → ι → R) : (Q × J) → (Q × ι) → R :=
  fun qj ↦ FiniteStateTransducer.seedLift (seed qj.2)

omit [DecidableEq B] [Nonempty B] [Fintype J] in
theorem transducedWordAverage_matrixBoolean_eq
    (T : FiniteStateTransducer Q B A) (p : B → ℝ)
    (M : J → A → Matrix ι ι R) (left seed : J → ι → R)
    (op : (J → Bool) → Bool) (q : Q) (n : ℕ) :
    transducedWordAverage T p
      (scalarWordBooleanValue op (fun j ↦ commRingMatrixCoefficient (M j) (left j) (seed j)))
      q n =
    matrixBooleanWordProbability p (fun b ↦ op (fun j ↦ b (q, j)))
      (transducedMatrixFamily T M) (transducedLeftFamily left)
      (transducedSeedFamily seed) n := by
  classical
  unfold transducedWordAverage matrixBooleanWordProbability scalarWordBooleanValue
  apply Finset.sum_congr rfl
  intro w _
  simp only [transducedMatrixFamily, transducedLeftFamily, transducedSeedFamily,
    FiniteStateTransducer.coefficient_matrixLift]

/-- A common reset and law-independent rational boundary data for all
initial states and every Boolean operation after a finite-state transducer.
The output alphabet itself need not be finite. -/
theorem exists_commonReset_transduced_matrixBoolean_analytic_boundaryDensity
    (T : FiniteStateTransducer Q B A)
    (M : J → A → Matrix ι ι R) (left seed : J → ι → R) :
    ∃ h : List B, h ≠ [] ∧
      ∀ op : (J → Bool) → Bool,
      ∃ m : Q → (s : Fin h.length) → (Fin (s : ℕ) → B) →
          GapWords (endoMarkerBlock h) × GapWords (endoMarkerBlock h) → ℚ,
        (∀ q s xi i, (m q s xi i : ℝ) ∈ Set.Icc (0 : ℝ) 1) ∧
        (∀ q (p : B → ℝ), (∀ b, 0 < p b) →
          AnalyticAt ℝ (normalizedRationalBoundaryDensity h (m q)) p ∧
            normalizedRationalBoundaryDensity h (m q) p ∈ Set.Icc (0 : ℝ) 1) ∧
        ∀ q (p : B → ℝ), (∀ b, 0 < p b) →
          Tendsto (realCesaroMean
            (transducedWordAverage T (normalizedRealWeights p)
              (scalarWordBooleanValue op
                (fun j ↦ commRingMatrixCoefficient (M j) (left j) (seed j))) q))
            atTop (𝓝 (normalizedRationalBoundaryDensity h (m q) p)) := by
  classical
  obtain ⟨h, hh, hall⟩ :=
    exists_commonReset_matrixBoolean_analytic_rational_boundaryDensity
      (transducedMatrixFamily T M) (transducedLeftFamily left)
      (transducedSeedFamily seed)
  refine ⟨h, hh, ?_⟩
  intro op
  choose m hbound hanalytic hlimit using
    (fun q : Q ↦ hall (fun b ↦ op (fun j ↦ b (q, j))))
  refine ⟨m, hbound, hanalytic, ?_⟩
  intro q p hp
  have hfun :
      transducedWordAverage T (normalizedRealWeights p)
          (scalarWordBooleanValue op
            (fun j ↦ commRingMatrixCoefficient (M j) (left j) (seed j))) q =
        matrixBooleanWordProbability (normalizedRealWeights p)
          (fun b ↦ op (fun j ↦ b (q, j)))
          (transducedMatrixFamily T M) (transducedLeftFamily left)
          (transducedSeedFamily seed) := by
    funext n
    exact transducedWordAverage_matrixBoolean_eq T (normalizedRealWeights p)
      M left seed op q n
  rw [hfun]
  exact hlimit q p hp

end MatrixTransduction
end IndependentZeroBlocks
