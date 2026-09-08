import Lean.Elab.Tactic.Omega

/-!
# Descendant intervals and trimmed zero blocks

This file isolates the elementary natural-number argument used after a digit
automaton has reached an absorbing zero state.  If `Z n` remains true after
appending any base-`q` digit, then every base-`q` descendant of a positive
seed satisfies `Z`.  The resulting intervals move arbitrarily far out.

The last theorem also records the trimming needed for a polynomial factor:
if the coefficient at `n` vanishes whenever the preceding `h + 1` values of
an auxiliary sequence vanish, descendant intervals for the auxiliary
sequence give arbitrarily long zero blocks for the coefficient sequence.
-/

namespace SierpinskiFormal

universe u v

/-- A sequence has zero blocks of every requested length starting beyond
every requested lower bound. -/
def HasArbitrarilyLongZeroBlocks {α : Type u} [Zero α] (f : Nat → α) : Prop :=
  ∀ length start, ∃ s, start ≤ s ∧ ∀ i, i < length → f (s + i) = 0

/-- A predicate that holds at a seed and is preserved by appending one
base-`q` digit holds throughout every descendant interval.

The proof explicitly writes the final digit as `j % q` and the remaining
prefix as `j / q`. -/
theorem descendants_of_append
    {q seed : Nat} {Z : Nat → Prop}
    (hq : 2 ≤ q) (hseed : Z seed)
    (happend : ∀ n d, d < q → Z n → Z (q * n + d)) :
    ∀ E j, j < q ^ E → Z (seed * q ^ E + j) := by
  intro E
  induction E with
  | zero =>
      intro j hj
      have hj0 : j = 0 := by simpa using hj
      simpa [hj0] using hseed
  | succ E ih =>
      intro j hj
      have hqpos : 0 < q := by omega
      have hjdiv : j / q < q ^ E := by
        apply (Nat.div_lt_iff_lt_mul hqpos).2
        simpa [Nat.pow_succ] using hj
      have hz := happend (seed * q ^ E + j / q) (j % q)
        (Nat.mod_lt _ hqpos) (ih (j / q) hjdiv)
      have hjdecomp : q * (j / q) + j % q = j := Nat.div_add_mod j q
      have hindex : q * (seed * q ^ E + j / q) + j % q =
          seed * q ^ (E + 1) + j := by
        calc
          q * (seed * q ^ E + j / q) + j % q =
              q * (seed * q ^ E) + (q * (j / q) + j % q) := by
                rw [Nat.mul_add]
                ac_rfl
          _ = q * (seed * q ^ E) + j := by rw [hjdecomp]
          _ = seed * (q ^ E * q) + j := by ac_rfl
          _ = seed * q ^ (E + 1) + j := by rw [Nat.pow_succ]
      rw [← hindex]
      exact hz

/-- The sequence form of `descendants_of_append`. -/
theorem zero_on_descendants_of_append
    {α : Type u} [Zero α] {q seed : Nat} {f : Nat → α}
    (hq : 2 ≤ q) (hseed : f seed = 0)
    (happend : ∀ n d, d < q → f n = 0 → f (q * n + d) = 0) :
    ∀ E j, j < q ^ E → f (seed * q ^ E + j) = 0 :=
  descendants_of_append hq hseed happend

/-- A useful explicit growth estimate for choosing descendant depths. -/
theorem exponent_lt_base_pow (q E : Nat) (hq : 2 ≤ q) : E < q ^ E := by
  exact Nat.lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_left hq E)

/-- Full descendant intervals of a positive seed contain arbitrarily long
zero blocks at unbounded indices. -/
theorem hasArbitrarilyLongZeroBlocks_of_descendants
    {α : Type u} [Zero α] {q seed : Nat} {f : Nat → α}
    (hq : 2 ≤ q) (hseedpos : 1 ≤ seed)
    (hdesc : ∀ E j, j < q ^ E → f (seed * q ^ E + j) = 0) :
    HasArbitrarilyLongZeroBlocks f := by
  intro length start
  let E := length + start + 1
  have hE : E < q ^ E := exponent_lt_base_pow q E hq
  refine ⟨seed * q ^ E, ?_, ?_⟩
  · have hpow_le : q ^ E ≤ seed * q ^ E := by
      exact Nat.le_mul_of_pos_left _ hseedpos
    omega
  · intro i hi
    exact hdesc E i (by omega)

/-- An absorbing zero seed therefore suffices for arbitrarily long zero
blocks.  This packages the two elementary steps commonly used after proving
a zero state for a digit recurrence. -/
theorem hasArbitrarilyLongZeroBlocks_of_append
    {α : Type u} [Zero α] {q seed : Nat} {f : Nat → α}
    (hq : 2 ≤ q) (hseedpos : 1 ≤ seed) (hseed : f seed = 0)
    (happend : ∀ n d, d < q → f n = 0 → f (q * n + d) = 0) :
    HasArbitrarilyLongZeroBlocks f :=
  hasArbitrarilyLongZeroBlocks_of_descendants hq hseedpos
    (zero_on_descendants_of_append hq hseed happend)

/-- If a predicate is inherited by descendants and a predicate at a parent
kills every coefficient in its next base-`q` block, then `u` vanishes on
every positive-depth descendant interval of the seed.  This is the form
used when an absorbing pole state kills a weighted convolution one block
later. -/
theorem zero_on_positive_depth_descendants_of_parent
    {α : Type u} [Zero α] {q seed : Nat} {Z : Nat → Prop} {u : Nat → α}
    (hq : 2 ≤ q) (hseed : Z seed)
    (happend : ∀ n d, d < q → Z n → Z (q * n + d))
    (hkill : ∀ M e, e < q → Z M → u (q * M + e) = 0) :
    ∀ E, 1 ≤ E → ∀ j, j < q ^ E → u (seed * q ^ E + j) = 0 := by
  intro E hE
  cases E with
  | zero => omega
  | succ E =>
      intro j hj
      have hqpos : 0 < q := by omega
      have hjdiv : j / q < q ^ E := by
        apply (Nat.div_lt_iff_lt_mul hqpos).2
        simpa [Nat.pow_succ] using hj
      have hzparent : Z (seed * q ^ E + j / q) :=
        descendants_of_append hq hseed happend E (j / q) hjdiv
      have hu := hkill (seed * q ^ E + j / q) (j % q)
        (Nat.mod_lt _ hqpos) hzparent
      have hjdecomp : q * (j / q) + j % q = j := Nat.div_add_mod j q
      have hindex : q * (seed * q ^ E + j / q) + j % q =
          seed * q ^ (E + 1) + j := by
        calc
          q * (seed * q ^ E + j / q) + j % q =
              q * (seed * q ^ E) + (q * (j / q) + j % q) := by
                rw [Nat.mul_add]
                ac_rfl
          _ = q * (seed * q ^ E) + j := by rw [hjdecomp]
          _ = seed * (q ^ E * q) + j := by ac_rfl
          _ = seed * q ^ (E + 1) + j := by rw [Nat.pow_succ]
      rw [← hindex]
      exact hu

/-- A parent-state condition that kills the following digit block produces
arbitrarily long zero blocks at unbounded indices. -/
theorem hasArbitrarilyLongZeroBlocks_of_parent
    {α : Type u} [Zero α] {q seed : Nat} {Z : Nat → Prop} {u : Nat → α}
    (hq : 2 ≤ q) (hseedpos : 1 ≤ seed) (hseed : Z seed)
    (happend : ∀ n d, d < q → Z n → Z (q * n + d))
    (hkill : ∀ M e, e < q → Z M → u (q * M + e) = 0) :
    HasArbitrarilyLongZeroBlocks u := by
  intro length start
  let E := length + start + 1
  have hE : E < q ^ E := exponent_lt_base_pow q E hq
  have hEpos : 1 ≤ E := by simp [E]
  refine ⟨seed * q ^ E, ?_, ?_⟩
  · have hpow_le : q ^ E ≤ seed * q ^ E := by
      exact Nat.le_mul_of_pos_left _ hseedpos
    omega
  · intro i hi
    exact zero_on_positive_depth_descendants_of_parent hq hseed happend hkill
      E hEpos i (by omega)

/-- Short named interface for the parent-state zero-block argument. -/
theorem toZeroBlocks
    {α : Type u} [Zero α] {q seed : Nat} {Z : Nat → Prop} {u : Nat → α}
    (hq : 2 ≤ q) (hseedpos : 1 ≤ seed) (hseed : Z seed)
    (happend : ∀ n d, d < q → Z n → Z (q * n + d))
    (hkill : ∀ M e, e < q → Z M → u (q * M + e) = 0) :
    HasArbitrarilyLongZeroBlocks u :=
  hasArbitrarilyLongZeroBlocks_of_parent hq hseedpos hseed happend hkill

/-- Trim `h` positions from the left of a zero interval for `f`.  Every
backward shift by at most `h` then remains inside that interval, so the
corresponding value of `u` vanishes. -/
theorem zero_on_trimmed_interval_of_finite_shifts
    {α : Type u} {β : Type v} [Zero α] [Zero β]
    {start width h : Nat} {f : Nat → α} {u : Nat → β}
    (hzero : ∀ j, j < width → f (start + j) = 0)
    (hu : ∀ n, (∀ i, i ≤ h → f (n - i) = 0) → u n = 0) :
    ∀ offset, h + offset < width → u (start + h + offset) = 0 := by
  intro offset hoffset
  apply hu
  intro i hi
  have hindex : h + offset - i < width := by omega
  have hsub : start + h + offset - i = start + (h + offset - i) := by
    omega
  rw [hsub]
  exact hzero (h + offset - i) hindex

/-- If `u n` vanishes whenever the `h + 1` preceding values of `f` vanish,
then descendant zero intervals for `f`, trimmed by `h` on the left, give
arbitrarily long zero blocks for `u`.

The descendant hypothesis starts at depth one, matching the repeated-pole
application where a zero pair at a parent kills the next complete block. -/
theorem hasArbitrarilyLongZeroBlocks_of_finite_shifts
    {α : Type u} {β : Type v} [Zero α] [Zero β]
    {q seed h : Nat} {f : Nat → α} {u : Nat → β}
    (hq : 2 ≤ q) (hseedpos : 1 ≤ seed)
    (hdesc : ∀ E, 1 ≤ E → ∀ j, j < q ^ E →
      f (seed * q ^ E + j) = 0)
    (hu : ∀ n, (∀ i, i ≤ h → f (n - i) = 0) → u n = 0) :
    HasArbitrarilyLongZeroBlocks u := by
  intro length start
  let E := length + start + h + 1
  have hE : E < q ^ E := exponent_lt_base_pow q E hq
  have hEpos : 1 ≤ E := by simp [E]
  refine ⟨seed * q ^ E + h, ?_, ?_⟩
  · have hpow_le : q ^ E ≤ seed * q ^ E := by
      exact Nat.le_mul_of_pos_left _ hseedpos
    omega
  · intro offset hoffset
    exact zero_on_trimmed_interval_of_finite_shifts
      (hzero := hdesc E hEpos) hu offset (by omega)

end SierpinskiFormal
