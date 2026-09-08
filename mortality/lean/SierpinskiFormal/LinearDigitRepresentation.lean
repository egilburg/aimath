import SierpinskiFormal.ReachableSpanMortality
import SierpinskiFormal.ImmortalConeDensity
import Mathlib.Data.Nat.Digits.Lemmas

set_option autoImplicit false

/-!
# Linear digit recurrences with padded words

The recurrence itself implies that the zero-digit map fixes the initial
state. It need not be the identity endomorphism. All word lengths are kept,
including high zero digits, so actions on intermediate states remain exact.
-/

namespace IndependentZeroBlocks

/-- Every index below a radix power has a digit word of exactly the chosen
length, with high zero padding allowed. -/
theorem exists_fin_digit_word_of_lt_pow
    (b : ℕ) (hb : 2 ≤ b) (k j : ℕ) (hj : j < b ^ k) :
    ∃ w : List (Fin b), w.length = k ∧ Nat.ofDigits b (w.map Fin.val) = j := by
  induction k generalizing j with
  | zero =>
    have hj0 : j = 0 := by simpa using hj
    exact ⟨[], by simp, by simp [hj0]⟩
  | succ k ih =>
    have hbpos : 0 < b := by omega
    have hquot : j / b < b ^ k := by
      apply (Nat.div_lt_iff_lt_mul hbpos).mpr
      simpa [pow_succ] using hj
    obtain ⟨w, hwlen, hwval⟩ := ih (j / b) hquot
    let r : Fin b := ⟨j % b, Nat.mod_lt j hbpos⟩
    refine ⟨r :: w, by simp [hwlen], ?_⟩
    simp only [List.map_cons, Nat.ofDigits_cons, hwval]
    exact Nat.mod_add_div j b

section Semiring
variable {K V : Type*} [Semiring K] [AddCommMonoid V] [Module K V]

/-- A padded little-endian digit word acts on any state exactly by appending
that low word to the state's radix index. -/
theorem linearWord_apply_digitRecurrence
    (b : ℕ) (T : Fin b → Module.End K V) (u : ℕ → V)
    (hrec : ∀ n (r : Fin b), u (b * n + r.val) = T r (u n))
    (w : List (Fin b)) (n : ℕ) :
    linearWord T w (u n) =
      u (b ^ w.length * n + Nat.ofDigits b (w.map Fin.val)) := by
  induction w with
  | nil => simp
  | cons r w ih =>
    rw [linearWord_cons, Module.End.mul_apply, ih, ← hrec]
    congr 1
    simp only [List.length_cons, List.map_cons, Nat.ofDigits_cons, pow_succ]
    ring

theorem linearWord_apply_digitRecurrence_seed
    (b : ℕ) (T : Fin b → Module.End K V) (u : ℕ → V)
    (hrec : ∀ n (r : Fin b), u (b * n + r.val) = T r (u n))
    (w : List (Fin b)) :
    linearWord T w (u 0) = u (Nat.ofDigits b (w.map Fin.val)) := by
  simpa using linearWord_apply_digitRecurrence b T u hrec w 0

/-- The digit recurrence normalizes the initial state, without imposing an
identity condition on the entire zero-digit endomorphism. -/
theorem linearDigit_zero_generator_fixes_seed
    (b : ℕ) (hb : 2 ≤ b) (T : Fin b → Module.End K V) (u : ℕ → V)
    (hrec : ∀ n (r : Fin b), u (b * n + r.val) = T r (u n)) :
    T ⟨0, by omega⟩ (u 0) = u 0 := by
  simpa using (hrec 0 ⟨0, by omega⟩).symm

/-- Every radix state is an orbit state of its initial vector. -/
theorem linearDigit_state_mem_orbit
    (b : ℕ) (hb : 2 ≤ b) (T : Fin b → Module.End K V) (u : ℕ → V)
    (hrec : ∀ n (r : Fin b), u (b * n + r.val) = T r (u n)) (n : ℕ) :
    u n ∈ linearOrbit T (u 0) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n
      exact ⟨[], by simp⟩
    · have hlt : n / b < n := Nat.div_lt_self (by omega) (by omega)
      obtain ⟨w, hw⟩ := ih (n / b) hlt
      change linearWord T w (u 0) = u (n / b) at hw
      let r : Fin b := ⟨n % b, Nat.mod_lt n (by omega)⟩
      refine ⟨r :: w, ?_⟩
      change linearWord T (r :: w) (u 0) = u n
      rw [linearWord_cons, Module.End.mul_apply, hw, ← hrec]
      congr 1
      exact Nat.div_add_mod n b

/-- The orbit and the range of the digit recurrence are exactly equal. -/
theorem linearDigit_orbit_eq_range
    (b : ℕ) (hb : 2 ≤ b) (T : Fin b → Module.End K V) (u : ℕ → V)
    (hrec : ∀ n (r : Fin b), u (b * n + r.val) = T r (u n)) :
    linearOrbit T (u 0) = Set.range u := by
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨Nat.ofDigits b (w.map Fin.val),
      (linearWord_apply_digitRecurrence_seed b T u hrec w).symm⟩
  · rintro ⟨n, rfl⟩
    exact linearDigit_state_mem_orbit b hb T u hrec n

theorem linearDigit_state_mem_reachableSpan
    (b : ℕ) (hb : 2 ≤ b) (T : Fin b → Module.End K V) (u : ℕ → V)
    (hrec : ∀ n (r : Fin b), u (b * n + r.val) = T r (u n)) (n : ℕ) :
    u n ∈ linearReachableSpan T (u 0) :=
  Submodule.subset_span (linearDigit_state_mem_orbit b hb T u hrec n)

/-- Every low radix block is represented by a word of its precise padded
length, acting on the supplied high state. -/
theorem linearDigit_descendant_word
    (b : ℕ) (hb : 2 ≤ b) (T : Fin b → Module.End K V) (u : ℕ → V)
    (hrec : ∀ n (r : Fin b), u (b * n + r.val) = T r (u n))
    (n k j : ℕ) (hj : j < b ^ k) :
    ∃ w : List (Fin b), w.length = k ∧
      Nat.ofDigits b (w.map Fin.val) = j ∧
      linearWord T w (u n) = u (b ^ k * n + j) := by
  obtain ⟨w, hwlen, hwval⟩ := exists_fin_digit_word_of_lt_pow b hb k j hj
  refine ⟨w, hwlen, hwval, ?_⟩
  simpa [hwlen, hwval] using linearWord_apply_digitRecurrence b T u hrec w n

theorem linearDigit_zero_descendants
    (b : ℕ) (hb : 2 ≤ b) (T : Fin b → Module.End K V) (u : ℕ → V)
    (hrec : ∀ n (r : Fin b), u (b * n + r.val) = T r (u n))
    (n : ℕ) (hn : u n = 0) (k j : ℕ) (hj : j < b ^ k) :
    u (b ^ k * n + j) = 0 := by
  obtain ⟨w, _, _, hw⟩ := linearDigit_descendant_word b hb T u hrec n k j hj
  rw [← hw, hn, map_zero]

/-- An annihilating word can be inserted between arbitrary low and high
blocks, while retaining its padding and ordered action. -/
theorem linearDigit_word_zero_cylinder
    (b : ℕ) (hb : 2 ≤ b) (T : Fin b → Module.End K V) (u : ℕ → V)
    (hrec : ∀ n (r : Fin b), u (b * n + r.val) = T r (u n))
    (w : List (Fin b)) (hzero : ∀ n, linearWord T w (u n) = 0)
    (k q j : ℕ) (hj : j < b ^ k) :
    u (b ^ (k + w.length) * q + b ^ k * Nat.ofDigits b (w.map Fin.val) + j) = 0 := by
  have hi : b ^ (k + w.length) * q + b ^ k * Nat.ofDigits b (w.map Fin.val) + j =
      b ^ k * (b ^ w.length * q + Nat.ofDigits b (w.map Fin.val)) + j := by
    rw [pow_add]
    ring
  rw [hi]
  apply linearDigit_zero_descendants b hb T u hrec _ _ k j hj
  rw [← linearWord_apply_digitRecurrence b T u hrec w q]
  exact hzero q

theorem linearDigit_common_word_zero_cylinder
    (b : ℕ) (hb : 2 ≤ b) (T : Fin b → Module.End K V) (u : ℕ → V)
    (hrec : ∀ n (r : Fin b), u (b * n + r.val) = T r (u n))
    (w : List (Fin b))
    (hzero : ∀ x ∈ linearReachableSpan T (u 0), linearWord T w x = 0)
    (k q j : ℕ) (hj : j < b ^ k) :
    u (b ^ (k + w.length) * q + b ^ k * Nat.ofDigits b (w.map Fin.val) + j) = 0 := by
  apply linearDigit_word_zero_cylinder b hb T u hrec w _ k q j hj
  intro n
  exact hzero _ (linearDigit_state_mem_reachableSpan b hb T u hrec n)

/-- If every state has a zero radix descendant, every orbit state is
killable by a finite continuation word. -/
theorem linearDigit_pointwise_mortal_of_zero_descendants
    (b : ℕ) (hb : 2 ≤ b) (T : Fin b → Module.End K V) (u : ℕ → V)
    (hrec : ∀ n (r : Fin b), u (b * n + r.val) = T r (u n))
    (hzero : ∀ n, ∃ k j, j < b ^ k ∧ u (b ^ k * n + j) = 0) :
    ∀ v : List (Fin b), ∃ w : List (Fin b),
      linearWord T w (linearWord T v (u 0)) = 0 := by
  intro v
  obtain ⟨k, j, hj, hz⟩ := hzero (Nat.ofDigits b (v.map Fin.val))
  obtain ⟨w, _, _, hw⟩ := linearDigit_descendant_word b hb T u hrec
    (Nat.ofDigits b (v.map Fin.val)) k j hj
  refine ⟨w, ?_⟩
  rw [linearWord_apply_digitRecurrence_seed b T u hrec v, hw, hz]

/-- Density zero rules out an immortal supported cone, hence gives
pointwise orbit mortality without any finite-dimensional assumption. -/
theorem linearDigit_pointwise_mortal_of_zeroDensity
    (b : ℕ) (hb : 2 ≤ b) (T : Fin b → Module.End K V) (u : ℕ → V)
    (hrec : ∀ n (r : Fin b), u (b * n + r.val) = T r (u n))
    (hz : HasZeroPredicateDensity (fun n => u n ≠ 0)) :
    ∀ v : List (Fin b), ∃ w : List (Fin b),
      linearWord T w (linearWord T v (u 0)) = 0 := by
  apply linearDigit_pointwise_mortal_of_zero_descendants b hb T u hrec
  intro n
  obtain ⟨k, j, hj, hn⟩ := hz.exists_missing_radixDescendant b hb n
  exact ⟨k, j, hj, not_ne_iff.mp hn⟩

end Semiring
end IndependentZeroBlocks
