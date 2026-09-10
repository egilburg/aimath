import FiniteMonoidMortality.ImprovedMortalityBound
import FiniteMonoidMortality.MinimalRankCompression

set_option autoImplicit false

set_option maxRecDepth 10000

set_option maxHeartbeats 1000000

namespace FiniteMonoidMortality

def mortalityRotation : Matrix (Fin 2) (Fin 2) ℤ := !![-1, -1; 1, 0]

def mortalityProjection : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, 0]

def mortalityExample : Bool → Matrix (Fin 2) (Fin 2) ℤ
  | false => mortalityRotation
  | true => mortalityProjection

def mortalityExampleSet : Finset (Matrix (Fin 2) (Fin 2) ℤ) :=
  {1, mortalityRotation, mortalityRotation ^ 2, 0} ∪
    Finset.univ.image (fun p : Fin 3 × Fin 3 × Bool =>
      (if p.2.2 then (-1 : ℤ) else 1) •
        (mortalityRotation ^ p.1.val * mortalityProjection * mortalityRotation ^ p.2.1.val))

theorem mortalityExampleSet_one : (1 : Matrix (Fin 2) (Fin 2) ℤ) ∈ mortalityExampleSet := by
  decide

theorem mortalityExampleSet_closed :
    ∀ a : Bool, ∀ X ∈ mortalityExampleSet, mortalityExample a * X ∈ mortalityExampleSet := by
  decide +kernel

theorem mortalityExample_mem (w : List Bool) : matrixWord mortalityExample w ∈ mortalityExampleSet := by
  induction w with
  | nil => exact mortalityExampleSet_one
  | cons a w ih =>
    exact mortalityExampleSet_closed a _ ih

theorem mortalityExample_finite : (Set.range (matrixWord mortalityExample)).Finite := by
  apply mortalityExampleSet.finite_toSet.subset
  rintro X ⟨w, rfl⟩
  exact mortalityExample_mem w

theorem mortalityExample_zero : matrixWord mortalityExample [true, false, false, true] = 0 := by
  decide

theorem mortalityExample_minimal (w : List Bool) (hw : matrixWord mortalityExample w = 0) :
    4 ≤ w.length := by
  match w with
  | [] => exact False.elim (by simpa [matrixWord, mortalityExample] using hw)
  | [a] => cases a <;> exfalso <;> revert hw <;> decide
  | [a,b] => cases a <;> cases b <;> exfalso <;> revert hw <;> decide
  | [a,b,c] => cases a <;> cases b <;> cases c <;> exfalso <;> revert hw <;> decide
  | _ :: _ :: _ :: _ :: _ => simp

theorem mortalityExample_threshold_four :
    (Set.range (matrixWord mortalityExample)).Finite ∧
    (∃ w : List Bool, matrixWord mortalityExample w = 0 ∧ w.length = 4) ∧
    (∀ w : List Bool, matrixWord mortalityExample w = 0 → 4 ≤ w.length) :=
  ⟨mortalityExample_finite, ⟨[true,false,false,true], mortalityExample_zero, rfl⟩,
    mortalityExample_minimal⟩

end FiniteMonoidMortality
