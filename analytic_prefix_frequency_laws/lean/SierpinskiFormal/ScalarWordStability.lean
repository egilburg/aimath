import SierpinskiFormal.ScalarWordRepresentation
import SierpinskiFormal.FiniteModuleWordRepresentation

set_option autoImplicit false

/-!
# Double-limit stability for scalar word representations

Finite families of recognizable scalar word functions over an arbitrary
commutative ring have stable Boolean support predicates.  Both the alphabet
and the family index are arbitrary finite types.
-/

noncomputable section

namespace IndependentZeroBlocks

/-- The Boolean predicate obtained by applying a finite Boolean operation to
the nonzero bits of a family of scalar word functions. -/
def scalarWordBooleanPredicate {R A J : Type*} [Zero R]
    (op : (J → Bool) → Bool) (f : J → List A → R) (w : List A) : Bool :=
  op (fun j ↦ nonzeroBool (f j w))

namespace ScalarWordRepresentation

variable {R A J : Type*} [CommRing R] [Fintype A]

/-- The nonzero support kernel of one scalar word representation has the
sequential Boolean double-limit property over an arbitrary finite alphabet. -/
theorem wordNonzeroBool_hasBooleanDoubleLimitProperty
    {f : List A → R} (D : ScalarWordRepresentation R A f) :
    HasBooleanDoubleLimitProperty
      (fun x y : List A ↦ nonzeroBool (f (x ++ y))) := by
  letI := D.fintype
  letI := D.decidableEq
  let T : A → Module.End R (D.carrier → R) :=
    fun a ↦ Matrix.mulVecLin (D.transition a)
  let l : Module.Dual R (D.carrier → R) := coordinateRowDual D.left
  have hlinear (w : List A) :
      linearWord T w D.seed =
        (commRingMatrixWord D.transition w).mulVec D.seed := by
    induction w with
    | nil => simp [T]
    | cons a w ih =>
        rw [linearWord_cons, Module.End.mul_apply, ih]
        simp only [T, Matrix.mulVecLin_apply, commRingMatrixWord]
        rw [List.map_cons, List.prod_cons, Matrix.mulVec_mulVec]
  have hcoefficient (w : List A) :
      l (linearWord T w D.seed) = f w := by
    rw [hlinear]
    simpa only [l, coordinateRowDual_apply, commRingMatrixCoefficient] using
      D.coefficient w
  have h := finiteModule_wordNonzeroBool_hasBooleanDoubleLimitProperty
    T l D.seed
  simpa only [hcoefficient] using h

/-- A finite Boolean combination of nonzero tests of recognizable scalar word
functions has the double-limit property in the orientation used by stationary
right-prefix averages. -/
theorem family_booleanPredicate_hasBooleanDoubleLimitProperty
    [Fintype J] {f : J → List A → R}
    (D : ∀ j, ScalarWordRepresentation R A (f j))
    (op : (J → Bool) → Bool) :
    HasBooleanDoubleLimitProperty
      (fun w z : List A ↦ scalarWordBooleanPredicate op f (z ++ w)) := by
  classical
  let e : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let op' : (Fin (Fintype.card J) → Bool) → Bool :=
    fun values ↦ op (fun j ↦ values (e j))
  let kernel : Fin (Fintype.card J) → List A → List A → Bool :=
    fun k w z ↦ nonzeroBool (f (e.symm k) (z ++ w))
  have hkernel (k : Fin (Fintype.card J)) :
      HasBooleanDoubleLimitProperty (kernel k) := by
    have hk := (D (e.symm k)).wordNonzeroBool_hasBooleanDoubleLimitProperty
    intro x y rowLimit columnLimit rowOuter columnOuter
      hrow hcolumn hrowOuter hcolumnOuter
    exact (hk y x columnLimit rowLimit columnOuter rowOuter
      hcolumn hrow hcolumnOuter hrowOuter).symm
  have h := hasBooleanDoubleLimitProperty_booleanCombine op' kernel hkernel
  have heq : booleanCombine op' kernel =
      (fun w z : List A ↦ op (fun j ↦ nonzeroBool (f j (z ++ w)))) := by
    funext w z
    simp [booleanCombine, kernel, op']
  change HasBooleanDoubleLimitProperty
    (fun w z : List A ↦ op (fun j ↦ nonzeroBool (f j (z ++ w))))
  rw [← heq]
  exact h

end ScalarWordRepresentation

end IndependentZeroBlocks
