import Mathlib.MeasureTheory.Constructions.Pi

/-! # One-sided sequence space and finite prefixes -/
set_option autoImplicit false
namespace SoficMarkovOrder
open MeasureTheory
variable {A : Type*}

/-- The left shift on one-sided sequences. -/
def sequenceShift (s : ℕ → A) : ℕ → A := fun n => s (n + 1)

/-- The zeroth letter on the canonical sequence space. -/
def sequenceHead (s : ℕ → A) : A := s 0

@[simp] theorem sequenceShift_apply (s : ℕ → A) (n : ℕ) :
    sequenceShift s n = s (n + 1) := rfl

@[simp] theorem sequenceHead_apply (s : ℕ → A) : sequenceHead s = s 0 := rfl

variable [MeasurableSpace A]

 theorem measurable_sequenceShift : Measurable (sequenceShift : (ℕ → A) → ℕ → A) := by
  apply measurable_pi_lambda
  intro n
  exact measurable_pi_apply (n + 1)


section Prefix

variable {Ω A : Type*}

/-- The first `n` letters seen along the forward orbit of `x`. -/
def orbitPrefix (letter : Ω → A) (T : Ω → Ω) : ℕ → Ω → List A
  | 0, _ => []
  | n + 1, x => letter x :: orbitPrefix letter T n (T x)

@[simp] theorem orbitPrefix_zero (letter : Ω → A) (T : Ω → Ω) (x : Ω) :
    orbitPrefix letter T 0 x = [] := rfl

@[simp] theorem orbitPrefix_succ (letter : Ω → A) (T : Ω → Ω)
    (n : ℕ) (x : Ω) :
    orbitPrefix letter T (n + 1) x =
      [letter x] ++ orbitPrefix letter T n (T x) := rfl

end Prefix

end SoficMarkovOrder
