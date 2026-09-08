import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! # Finite-word weights and tuple decomposition

Only the two elementary constructions used by the IID two-block realization
are retained: product weights and the head/tail equivalence for tuples.
-/
set_option autoImplicit false
namespace SoficMarkovOrder
variable {A R : Type*}
def wordWeight [Monoid R] (p : A → R) (w : List A) : R := (w.map p).prod

/-- Exact-length tuples split into their first letter and remaining tuple. -/
noncomputable def finSuccTupleEquiv (n : ℕ) :
    (Fin (n + 1) → A) ≃ A × (Fin n → A) where
  toFun x := (x 0, fun i => x i.succ)
  invFun ax := Fin.cons ax.1 ax.2
  left_inv x := by
    funext i
    exact Fin.cases rfl (fun j => rfl) i
  right_inv ax := by
    apply Prod.ext
    · rfl
    · funext i
      rfl


end SoficMarkovOrder
