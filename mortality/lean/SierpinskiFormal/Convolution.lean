import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Polynomially weighted Lucas convolutions

This component proves the complete-block calculation used for repeated poles.
The Lucas identity and characteristic condition are explicit hypotheses.  The
connection between these weighted sums and rational-function partial fractions
is a separate formalization obligation.
-/

namespace SierpinskiFormal.Convolution

open scoped BigOperators

variable {K : Type*} [CommRing K]

/-- Split a finite sum into complete blocks of a fixed base. -/
theorem sum_range_blocks (f : ℕ → K) (q M : ℕ) :
    (∑ j ∈ Finset.range (q * M), f j) =
      ∑ m ∈ Finset.range M, ∑ d ∈ Finset.range q, f (q * m + d) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- Complete blocks followed by the final partial block. -/
theorem sum_range_blocks_partial (f : ℕ → K) (q M e : ℕ) :
    (∑ j ∈ Finset.range (q * M + e + 1), f j) =
      (∑ m ∈ Finset.range M, ∑ d ∈ Finset.range q, f (q * m + d)) +
        ∑ d ∈ Finset.range (e + 1), f (q * M + d) := by
  rw [Nat.add_assoc, Finset.sum_range_add, sum_range_blocks]

/-- A polynomially weighted prefix. Binomial coefficients for a pole of order
`s` are polynomial weights when `(s-1)!` is invertible; no such identification
is assumed or proved by this definition. -/
def weighted (P : Polynomial K) (v : ℕ → K) (n : ℕ) : K :=
  ∑ j ∈ Finset.range (n + 1), P.eval ((n : K) - (j : K)) * v j

def fullWeight (P : Polynomial K) (v : ℕ → K) (q e : ℕ) : K :=
  ∑ d ∈ Finset.range q, P.eval ((e : K) - (d : K)) * v d

def partialWeight (P : Polynomial K) (v : ℕ → K) (e : ℕ) : K :=
  ∑ d ∈ Finset.range (e + 1), P.eval ((e : K) - (d : K)) * v d

/-- Base-q blocking works in characteristic p whenever q is zero in the field,
including q=p^f rather than just q=p. -/
theorem weighted_block (P : Polynomial K) (v : ℕ → K) (q M e : ℕ)
    (hq : (q : K) = 0) (he : e < q)
    (hlucas : ∀ m d, d < q → v (q * m + d) = v m * v d) :
    weighted P v (q * M + e) =
      fullWeight P v q e * (∑ m ∈ Finset.range M, v m) +
        partialWeight P v e * v M := by
  unfold weighted
  rw [sum_range_blocks_partial]
  congr 1
  · calc
      (∑ m ∈ Finset.range M, ∑ d ∈ Finset.range q,
          P.eval (((q * M + e : ℕ) : K) - ((q * m + d : ℕ) : K)) *
            v (q * m + d)) =
          ∑ m ∈ Finset.range M, fullWeight P v q e * v m := by
        apply Finset.sum_congr rfl
        intro m hm
        unfold fullWeight
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro d hd
        rw [hlucas m d (Finset.mem_range.mp hd)]
        simp only [Nat.cast_add, Nat.cast_mul, hq, zero_mul, zero_add]
        ring
      _ = fullWeight P v q e * ∑ m ∈ Finset.range M, v m := by
        rw [Finset.mul_sum]
  · unfold partialWeight
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    have hdq : d < q := by have := Finset.mem_range.mp hd; omega
    rw [hlucas M d hdq]
    simp only [Nat.cast_add, Nat.cast_mul, hq, zero_mul, zero_add]
    ring

/-- Both coordinates of the zero state are necessary: vanishing of the
coefficient and its inclusive prefix sum kills every polynomial weight. -/
theorem weighted_zero_of_state (P : Polynomial K) (v : ℕ → K) (q M e : ℕ)
    (hq : (q : K) = 0) (he : e < q)
    (hlucas : ∀ m d, d < q → v (q * m + d) = v m * v d)
    (hv : v M = 0) (hf : (∑ m ∈ Finset.range (M + 1), v m) = 0) :
    weighted P v (q * M + e) = 0 := by
  have hpref : (∑ m ∈ Finset.range M, v m) = 0 := by
    simpa [Finset.sum_range_succ, hv] using hf
  rw [weighted_block P v q M e hq he hlucas, hpref, hv]
  simp

/-- The inclusive prefix sum has the two-coordinate transition used in the
common-word argument. This is derived from Lucas, rather than postulated. -/
theorem prefix_digit (v : ℕ → K) (q M e : ℕ)
    (hq : (q : K) = 0) (he : e < q)
    (hlucas : ∀ m d, d < q → v (q * m + d) = v m * v d) :
    (∑ j ∈ Finset.range (q * M + e + 1), v j) =
      (∑ d ∈ Finset.range q, v d) * (∑ j ∈ Finset.range (M + 1), v j) +
      ((∑ d ∈ Finset.range (e + 1), v d) - (∑ d ∈ Finset.range q, v d)) *
        v M := by
  have hb := weighted_block (1 : Polynomial K) v q M e hq he hlucas
  simp only [weighted, fullWeight, partialWeight, Polynomial.eval_one, one_mul] at hb
  rw [hb, Finset.sum_range_succ (n := M)]
  ring

/-- Twisting by a base-q Frobenius-fixed scalar preserves the Lucas rule. -/
theorem twist_lucas (t : ℕ → K) (q : ℕ) (gamma : K)
    (hgamma : gamma ^ q = gamma)
    (ht : ∀ m d, d < q → t (q * m + d) = t m * t d) :
    ∀ m d, d < q →
      t (q * m + d) * gamma ^ (q * m + d) =
        (t m * gamma ^ m) * (t d * gamma ^ d) := by
  intro m d hd
  rw [ht m d hd, pow_add, pow_mul, hgamma]
  ring

/-- The first nonzero positive digit gives the common low-digit transition. -/
theorem first_digit_prefix (v : ℕ → K) (d : ℕ) (hd : 0 < d)
    (hzero : v 0 = 1) (hlow : ∀ j, 0 < j → j < d → v j = 0) :
    (∑ j ∈ Finset.range (d + 1), v j) = 1 + v d := by
  rw [Finset.sum_range_succ]
  have hs : (∑ j ∈ Finset.range d, v j) = v 0 := by
    apply Finset.sum_eq_single 0
    · intro j hj hj0
      exact hlow j (Nat.pos_of_ne_zero hj0) (Finset.mem_range.mp hj)
    · intro hnot
      exact False.elim (hnot (Finset.mem_range.mpr hd))
  rw [hs, hzero]

end SierpinskiFormal.Convolution

#print axioms SierpinskiFormal.Convolution.weighted_block
#print axioms SierpinskiFormal.Convolution.weighted_zero_of_state
