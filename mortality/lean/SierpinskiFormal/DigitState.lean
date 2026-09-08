import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# The common digit word and its absorbing state

This file verifies the finite-field state argument in Sections 4–5 of
`pass8/rational_multiplier.md`.  It does not assert that an arbitrary generating
function has the required coefficient recurrence.  The recurrence is the
explicit transition below, and the final sequence lemma takes it as a hypothesis.
The finite-extension variant uses characteristic `p` and digit base `q`, allowing
the pole parameters to live in any finite field of cardinality `q`.
-/

namespace SierpinskiFormal.DigitState

open scoped BigOperators

variable {K : Type*} [CommRing K]

/-- The two coordinates are the normalized prefix sum and coefficient. -/
def transition (H F w : K) (s : K × K) : K × K :=
  (H * s.1 + (F - H) * s.2, w * s.2)

@[simp] theorem transition_zero (H F w : K) :
    transition H F w (0, 0) = (0, 0) := by
  simp [transition]

/-- Reading a low digit repeatedly, starting at the constant coefficient. -/
def lowState (H c : K) : ℕ → K × K
  | 0 => (1, 1)
  | n + 1 => transition H (1 + c) c (lowState H c n)

theorem lowState_one (c : K) (n : ℕ) :
    lowState 1 c n = (∑ j ∈ Finset.range (n + 1), c ^ j, c ^ n) := by
  induction n with
  | zero => simp [lowState]
  | succ n ih =>
    rw [lowState, ih]
    apply Prod.ext
    · simp only [transition, Prod.fst, Finset.sum_range_succ, pow_succ]
      ring
    · simp only [transition, Prod.snd, pow_succ]
      ring

/-- The geometric-sum identity, also valid at `c = 1`. -/
theorem geometric_mul (c : K) (n : ℕ) :
    (c - 1) * (∑ j ∈ Finset.range n, c ^ j) = c ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
    ring

/-- Word length for characteristic `p` and an extension with `q` elements. -/
def extensionLength (p q : ℕ) : ℕ := p * (q - 1) - 1

theorem extensionLength_add_one (p q : ℕ) (hp : 0 < p) (hq : 1 < q) :
    extensionLength p q + 1 = p * (q - 1) := by
  have hpos : 0 < p * (q - 1) := Nat.mul_pos hp (by omega)
  unfold extensionLength
  omega

/-- The finite-extension version needs only characteristic `p` and the stated
multiplicative exponent identity; no splitting-prime hypothesis is used. -/
theorem extension_geometric_zero {L : Type*} [Field L]
    (p q : ℕ) [CharP L p] (hp : 0 < p) (hq : 1 < q)
    (c : L) (hpow : c ^ (q - 1) = 1) :
    (∑ j ∈ Finset.range (extensionLength p q + 1), c ^ j) = 0 := by
  rw [extensionLength_add_one p q hp hq]
  by_cases h1 : c = 1
  · subst c
    have hpzero : (p : L) = 0 := CharP.cast_eq_zero L p
    simp [Nat.cast_mul, hpzero]
  · have hpow' : c ^ (p * (q - 1)) = 1 := by
      rw [Nat.mul_comm p, pow_mul, hpow, one_pow]
    have hgeom := geometric_mul c (p * (q - 1))
    rw [hpow', sub_self] at hgeom
    exact (mul_eq_zero.mp hgeom).resolve_left (sub_ne_zero.mpr h1)

/-- Number of repeated low digits in the manuscript's common word. -/
def commonLength (p : ℕ) : ℕ := p * (p - 1) - 1

theorem commonLength_add_one (p : ℕ) [Fact p.Prime] :
    commonLength p + 1 = p * (p - 1) := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hpos : 0 < p * (p - 1) := Nat.mul_pos (by omega) (by omega)
  unfold commonLength
  omega

/-- A single length annihilates the geometric sum for every nonzero element,
including the element one. -/
theorem common_geometric_zero (p : ℕ) [Fact p.Prime]
    (c : ZMod p) (hc : c ≠ 0) :
    (∑ j ∈ Finset.range (commonLength p + 1), c ^ j) = 0 := by
  rw [commonLength_add_one]
  by_cases h1 : c = 1
  · subst c
    simp [Nat.cast_mul]
  · have hpow : c ^ (p * (p - 1)) = 1 := by
      rw [Nat.mul_comm p, pow_mul, ZMod.pow_card_sub_one_eq_one hc, one_pow]
    have hgeom := geometric_mul c (p * (p - 1))
    rw [hpow, sub_self] at hgeom
    exact (mul_eq_zero.mp hgeom).resolve_left (sub_ne_zero.mpr h1)

theorem lowState_common_fst_zero (p : ℕ) [Fact p.Prime]
    (c : ZMod p) (hc : c ≠ 0) :
    (lowState 1 c (commonLength p)).1 = 0 := by
  rw [lowState_one]
  exact common_geometric_zero p c hc

/-- A high digit kills every branch-pole state without a multiplicity bound. -/
@[simp] theorem high_branch (s : K × K) :
    transition 0 0 0 s = (0, 0) := by
  simp [transition]

/-- A high digit kills an off-branch state whose prefix sum is zero. -/
theorem high_off_branch (s : K × K) (hs : s.1 = 0) :
    transition 1 1 0 s = (0, 0) := by
  simp [transition, hs]

/-- The same low-word length followed by one high digit works for branch
and off-branch poles.  The nonzero condition is only needed off the branch. -/
theorem common_seed (p : ℕ) [Fact p.Prime] (H c : ZMod p)
    (hH : H = 0 ∨ H = 1) (hc : H = 1 → c ≠ 0) :
    transition H H 0 (lowState H c (commonLength p)) = (0, 0) := by
  rcases hH with hH | hH
  · subst H
    exact high_branch _
  · subst H
    exact high_off_branch _ (lowState_common_fst_zero p c (hc rfl))

/-- A common seed over an arbitrary characteristic-`p` field containing the
required multiplicative roots.  This permits a finite extension of `F_p`. -/
theorem extension_common_seed {L : Type*} [Field L]
    (p q : ℕ) [CharP L p] (hp : 0 < p) (hq : 1 < q) (H c : L)
    (hH : H = 0 ∨ H = 1) (hpow : H = 1 → c ^ (q - 1) = 1) :
    transition H H 0 (lowState H c (extensionLength p q)) = (0, 0) := by
  rcases hH with hH | hH
  · subst H
    exact high_branch _
  · subst H
    apply high_off_branch
    rw [lowState_one]
    exact extension_geometric_zero p q hp hq c (hpow rfl)

/-- In a finite field the multiplicative exponent condition follows from
Lagrange's theorem, so only the nonzero low-digit coefficient is required. -/
theorem finite_field_common_seed {L : Type*} [Field L] [Fintype L]
    (p : ℕ) [CharP L p] (hp : 0 < p) (H c : L)
    (hH : H = 0 ∨ H = 1) (hc : H = 1 → c ≠ 0) :
    transition H H 0 (lowState H c (extensionLength p (Fintype.card L))) = (0, 0) := by
  apply extension_common_seed p (Fintype.card L) hp
    (Fintype.one_lt_card_iff_nontrivial.mpr inferInstance) H c hH
  intro h
  exact FiniteField.pow_card_sub_one_eq_one c (hc h)

/-- Every further digit word preserves the zero state. -/
theorem word_absorbs {D : Type*} (H : K) (F w : D → K) (digits : List D) :
    digits.foldl (fun s d => transition H (F d) (w d) s) (0, 0) = (0, 0) := by
  induction digits with
  | nil => rfl
  | cons d ds ih =>
    rw [List.foldl_cons, transition_zero]
    exact ih

/-- The index represented by a repeated digit; it depends only on the base and
digit, not on the pole parameter. -/
def lowIndex (B d : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => B * lowIndex B d n + d

theorem sequence_lowState (B d : ℕ) (H c : K) (F w : ℕ → K)
    (s : ℕ → K × K) (hd : d < B) (hs : s 0 = (1, 1))
    (hrec : ∀ m e, e < B → s (B * m + e) = transition H (F e) (w e) (s m))
    (hF : F d = 1 + c) (hw : w d = c) (n : ℕ) :
    s (lowIndex B d n) = lowState H c n := by
  induction n with
  | zero => exact hs
  | succ n ih =>
    rw [lowIndex, hrec _ d hd, hF, hw, ih]
    rfl

/-- A coefficient-recurrence bridge to one explicit, pole-independent integer
index.  The characteristic is `p`; the digit base is `q`. -/
theorem sequence_extension_seed {L : Type*} [Field L]
    (p q d e : ℕ) [CharP L p] (hp : 0 < p) (hq : 1 < q)
    (H c : L) (F w : ℕ → L) (s : ℕ → L × L)
    (hd : d < q) (he : e < q) (hs : s 0 = (1, 1))
    (hrec : ∀ m a, a < q → s (q * m + a) = transition H (F a) (w a) (s m))
    (hH : H = 0 ∨ H = 1) (hpow : H = 1 → c ^ (q - 1) = 1)
    (hFd : F d = 1 + c) (hwd : w d = c)
    (hFe : F e = H) (hwe : w e = 0) :
    s (q * lowIndex q d (extensionLength p q) + e) = (0, 0) := by
  rw [hrec _ e he, hFe, hwe,
    sequence_lowState q d H c F w s hd hs hrec hFd hwd]
  exact extension_common_seed p q hp hq H c hH hpow

/-- Sequence-level absorption, conditional on the exact coefficient recurrence.
The digit functions may vary between digits, but not between prefixes. -/
theorem append_zero {p : ℕ} (H : K) (F w : ℕ → K) (s : ℕ → K × K)
    (hrec : ∀ m d, d < p → s (p * m + d) = transition H (F d) (w d) (s m))
    {q d : ℕ} (hq : s q = (0, 0)) (hd : d < p) :
    s (p * q + d) = (0, 0) := by
  rw [hrec q d hd, hq, transition_zero]

end SierpinskiFormal.DigitState

#print axioms SierpinskiFormal.DigitState.common_geometric_zero
#print axioms SierpinskiFormal.DigitState.extension_common_seed
#print axioms SierpinskiFormal.DigitState.finite_field_common_seed
#print axioms SierpinskiFormal.DigitState.sequence_extension_seed
#print axioms SierpinskiFormal.DigitState.word_absorbs
