import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-! # Independent finite selector weights

The realization uses a random emission selector on each ordered state pair.
Normalization and single-coordinate marginals give the finite probability law.
-/
set_option autoImplicit false
noncomputable section
namespace SoficMarkovOrder
open scoped BigOperators
variable {Q : Type*} [Fintype Q] [DecidableEq Q] {E : Q → Type*} [∀ q, Fintype (E q)]
def selectorWeight (p : (q : Q) → E q → ℝ) (f : (q : Q) → E q) : ℝ :=
  ∏ q, p q (f q)

/-- The total selector mass factors into the row masses. -/
theorem sum_selectorWeight (p : (q : Q) → E q → ℝ) :
    (∑ f : ((q : Q) → E q), selectorWeight p f) =
      ∏ q, ∑ e : E q, p q e := by
  classical
  unfold selectorWeight
  exact (Fintype.prod_sum p).symm

theorem sum_selectorWeight_eq_one (p : (q : Q) → E q → ℝ)
    (hp1 : ∀ q, ∑ e : E q, p q e = 1) :
    (∑ f : ((q : Q) → E q), selectorWeight p f) = 1 := by
  rw [sum_selectorWeight]
  simp [hp1]

/-- Under normalized rows, averaging a function of one selector coordinate
gives the corresponding row average. -/
theorem sum_selectorWeight_mul_apply (p : (q : Q) → E q → ℝ)
    (hp1 : ∀ q, ∑ e : E q, p q e = 1)
    (q : Q) (g : E q → ℝ) :
    (∑ f : ((q : Q) → E q), selectorWeight p f * g (f q)) =
      ∑ e : E q, p q e * g e := by
  classical
  let p' : (r : Q) → E r → ℝ :=
    Function.update p q (fun e ↦ p q e * g e)
  have hweight (f : ((q : Q) → E q)) :
      selectorWeight p' f = selectorWeight p f * g (f q) := by
    unfold selectorWeight
    rw [← Finset.mul_prod_erase Finset.univ (fun r ↦ p' r (f r))
      (Finset.mem_univ q)]
    rw [← Finset.mul_prod_erase Finset.univ (fun r ↦ p r (f r))
      (Finset.mem_univ q)]
    simp only [p', Function.update_self]
    have hrest :
        (∏ r ∈ Finset.univ.erase q, p' r (f r)) =
          ∏ r ∈ Finset.univ.erase q, p r (f r) := by
      apply Finset.prod_congr rfl
      intro r hr
      have hrq : r ≠ q := (Finset.mem_erase.mp hr).1
      simp [p', Function.update_of_ne hrq]
    rw [hrest]
    ring
  have hrow :
      (∏ r, ∑ e : E r, p' r e) =
        ∑ e : E q, p q e * g e := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun r ↦ ∑ e : E r, p' r e) (Finset.mem_univ q)]
    simp only [p', Function.update_self]
    have hrest :
        (∏ r ∈ Finset.univ.erase q, ∑ e : E r, p' r e) = 1 := by
      apply Finset.prod_eq_one
      intro r hr
      have hrq : r ≠ q := (Finset.mem_erase.mp hr).1
      simpa [p', Function.update_of_ne hrq] using hp1 r
    rw [hrest, mul_one]
  calc
    (∑ f : ((q : Q) → E q), selectorWeight p f * g (f q)) =
        ∑ f : ((q : Q) → E q), selectorWeight p' f := by
          apply Finset.sum_congr rfl
          intro f _
          exact (hweight f).symm
    _ = ∏ r, ∑ e : E r, p' r e := sum_selectorWeight p'
    _ = ∑ e : E q, p q e * g e := hrow


end SoficMarkovOrder
