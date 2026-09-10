import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

set_option autoImplicit false

namespace FiniteMonoidMortality

section Semiring

variable {K V ι : Type*} [Semiring K] [AddCommMonoid V] [Module K V]

def linearWord (T : ι → Module.End K V) (w : List ι) : Module.End K V :=
  (w.map T).prod

@[simp] theorem linearWord_nil (T : ι → Module.End K V) : linearWord T [] = 1 := by
  simp [linearWord]

@[simp] theorem linearWord_cons (T : ι → Module.End K V) (i : ι) (w : List ι) :
    linearWord T (i :: w) = T i * linearWord T w := by
  simp [linearWord]

def linearOrbit (T : ι → Module.End K V) (v0 : V) : Set V :=
  Set.range fun w : List ι => linearWord T w v0

def linearReachableSpan (T : ι → Module.End K V) (v0 : V) : Submodule K V :=
  Submodule.span K (linearOrbit T v0)

theorem linearWord_mem_linearReachableSpan (T : ι → Module.End K V)
    (v0 : V) (w : List ι) : linearWord T w v0 ∈ linearReachableSpan T v0 :=
  Submodule.subset_span ⟨w, rfl⟩

end Semiring

section Field

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

end Field

end FiniteMonoidMortality
