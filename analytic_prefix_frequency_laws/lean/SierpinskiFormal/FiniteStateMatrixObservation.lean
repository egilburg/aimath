import SierpinskiFormal.FiniteStateTransducer
import SierpinskiFormal.ArtinianCoefficientDescent

set_option autoImplicit false

/-! # Pulling matrix observations back through finite-state transducers

A letter-to-letter transducer can be incorporated exactly into a matrix
observation by adjoining its finite state to the matrix index.  The theorem in
this file is an equality of coefficients over an arbitrary commutative ring;
it does not pass through support predicates or an assumed representation law.
-/

noncomputable section

open scoped BigOperators

namespace IndependentZeroBlocks
namespace FiniteStateTransducer

/-- Matrix transition on the product of a transducer state and the original
matrix index.  Its only nonzero state block follows the deterministic next
state and carries the matrix indexed by the emitted letter. -/
def matrixLift {Q B A ι R : Type*} [Zero R] (T : FiniteStateTransducer Q B A)
    (M : A → Matrix ι ι R) : B → Matrix (Q × ι) (Q × ι) R := by
  classical
  exact fun b si tj ↦
    if tj.1 = T.next si.1 b then M (T.emit si.1 b) si.2 tj.2 else 0

/-- A row supported at the chosen initial transducer state. -/
def leftLift {Q ι R : Type*} [Zero R] (q0 : Q) (left : ι → R) : Q × ι → R := by
  classical
  exact fun si ↦ if si.1 = q0 then left si.2 else 0

/-- The original seed repeated at every transducer state. -/
def seedLift {Q ι R : Type*} (seed : ι → R) : Q × ι → R :=
  fun si ↦ seed si.2

section MatrixLift

variable {Q B A ι R : Type*} [CommRing R]
  [Fintype Q] [DecidableEq Q] [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- One lifted transition applies the emitted matrix and reads the input
vector at the unique next transducer state. -/
theorem matrixLift_mulVec (T : FiniteStateTransducer Q B A)
    (M : A → Matrix ι ι R) (b : B) (v : Q × ι → R) (q : Q) (i : ι) :
    (matrixLift T M b).mulVec v (q, i) =
      (M (T.emit q b)).mulVec (fun j ↦ v (T.next q b, j)) i := by
  classical
  simp [matrixLift, Matrix.mulVec, dotProduct, Fintype.sum_prod_type]

/-- Evaluation of a lifted matrix word at one transducer state is evaluation
of the original matrix word on the emitted word. -/
theorem matrixLift_word_mulVec (T : FiniteStateTransducer Q B A)
    (M : A → Matrix ι ι R) (seed : ι → R) (q : Q) (w : List B) (i : ι) :
    (commRingMatrixWord (matrixLift T M) w).mulVec (seedLift seed) (q, i) =
      (commRingMatrixWord M (T.outputWord q w)).mulVec seed i := by
  induction w generalizing q i with
  | nil => simp [commRingMatrixWord, seedLift]
  | cons b w ih =>
      simp only [commRingMatrixWord, List.map_cons, List.prod_cons,
        outputWord_cons]
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      rw [matrixLift_mulVec]
      apply congrArg (fun v : ι → R ↦ (M (T.emit q b)).mulVec v i)
      funext j
      exact ih (T.next q b) j

/-- Exact scalar pullback along a finite-state transducer. -/
theorem coefficient_matrixLift (T : FiniteStateTransducer Q B A)
    (M : A → Matrix ι ι R) (q0 : Q) (left seed : ι → R) (w : List B) :
    commRingMatrixCoefficient (matrixLift T M) (leftLift q0 left)
        (seedLift seed) w =
      commRingMatrixCoefficient M left seed (T.outputWord q0 w) := by
  classical
  simp [commRingMatrixCoefficient, Fintype.sum_prod_type, leftLift,
    matrixLift_word_mulVec]

end MatrixLift
end FiniteStateTransducer
end IndependentZeroBlocks
