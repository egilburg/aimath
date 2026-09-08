import Mathlib.Data.Matrix.Mul
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

set_option autoImplicit false

/-!
# Matrix words and scalar extension

Word products multiply in written list order. Scalar extension preserves finite product range and reflects zero words.
-/

noncomputable section

open scoped BigOperators

namespace FiniteMonoidMortality

variable {F A ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]

/-- Chronological product of a matrix-labelled word. -/
def matrixWord (M : A → Matrix ι ι F) (w : List A) : Matrix ι ι F :=
  (w.map M).prod

@[simp] theorem matrixWord_nil (M : A → Matrix ι ι F) :
    matrixWord M [] = 1 := by
  simp [matrixWord]

@[simp] theorem matrixWord_append (M : A → Matrix ι ι F) (x y : List A) :
    matrixWord M (x ++ y) = matrixWord M x * matrixWord M y := by
  simp [matrixWord]


section ScalarExtension
variable {F K A ι : Type*} [Field F] [Field K] [Fintype ι] [DecidableEq ι]

/-- Scalar extension commutes with chronological matrix-word evaluation. -/
theorem matrixWord_map (f : F →+* K) (M : A → Matrix ι ι F) (w : List A) :
    matrixWord (fun a => (M a).map f) w = (matrixWord M w).map f := by
  induction w with
  | nil => simp
  | cons a w ih =>
      simpa [matrixWord] using congrArg (fun X => (M a).map f * X) ih

/-- A finite word monoid remains finite after scalar extension. -/
theorem finite_matrixWord_range_map (f : F →+* K) (M : A → Matrix ι ι F)
    (hfinite : (Set.range (matrixWord M)).Finite) :
    (Set.range (matrixWord (fun a => (M a).map f))).Finite := by
  have hrange : Set.range (matrixWord (fun a => (M a).map f)) =
      (fun X : Matrix ι ι F => X.map f) '' Set.range (matrixWord M) := by
    rw [← Set.range_comp]
    congr 1
    funext w
    exact matrixWord_map f M w
  rw [hrange]
  exact hfinite.image _

/-- Scalar extension between fields preserves and reflects zero words. -/
theorem matrixWord_map_eq_zero_iff (f : F →+* K) (M : A → Matrix ι ι F)
    (w : List A) :
    matrixWord (fun a => (M a).map f) w = 0 ↔ matrixWord M w = 0 := by
  rw [matrixWord_map]
  constructor
  · intro h
    ext i j
    apply f.injective
    simpa using congrFun (congrFun h i) j
  · intro h
    simp [h]
end ScalarExtension

end FiniteMonoidMortality
