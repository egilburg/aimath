import SierpinskiFormal.ObservableNoetherian

set_option autoImplicit false
namespace IndependentZeroBlocks
open scoped BigOperators

/-- A word is invisible in every left and right context of the observed
linear representation. The empty word is allowed for the zero series. -/
def ObservedWordMortal
    {K V I : Type*} [CommSemiring K] [AddCommMonoid V] [Module K V]
    (T : I → Module.End K V) (l : Module.Dual K V) (v0 : V) : Prop :=
  ∃ w : List I, ∀ v z : List I, l (linearWord T (v ++ w ++ z) v0) = 0

section Model
variable {K V I : Type*} [CommSemiring K] [AddCommMonoid V] [Module K V]

/-- Vanishing of all generating observations persists under every word. -/
theorem observable_rows_zero_after_word
    (T : I → Module.End K V) (l : Module.Dual K V)
    (d : ℕ) (rows : Fin d → List I) (C : I → Matrix (Fin d) (Fin d) K)
    (hC : ∀ r i x, l (linearWord T (rows i) (T r x)) =
      ∑ j, C r i j * l (linearWord T (rows j) x))
    (x : V) (hx : ∀ i, l (linearWord T (rows i) x) = 0)
    (w : List I) : ∀ i, l (linearWord T (rows i) (linearWord T w x)) = 0 := by
  induction w with
  | nil => simpa using hx
  | cons r w ih =>
    intro i
    rw [linearWord_cons, Module.End.mul_apply, hC]
    simp [ih]

/-- Finitely many generating observations detect vanishing of every
possible future scalar output. -/
theorem observable_all_words_zero_of_rows_zero
    (T : I → Module.End K V) (l : Module.Dual K V)
    (d : ℕ) (rows : Fin d → List I) (a : Fin d → K)
    (C : I → Matrix (Fin d) (Fin d) K)
    (ha : ∀ x, l x = ∑ j, a j * l (linearWord T (rows j) x))
    (hC : ∀ r i x, l (linearWord T (rows i) (T r x)) =
      ∑ j, C r i j * l (linearWord T (rows j) x))
    (x : V) (hx : ∀ i, l (linearWord T (rows i) x) = 0)
    (w : List I) : l (linearWord T w x) = 0 := by
  rw [ha]
  simp [observable_rows_zero_after_word T l d rows C hC x hx w]

/-- The finite observable-state certificate is exactly the intrinsic
condition that one word vanish in every left and right context. -/
theorem observedWordMortal_iff_zero_row_fiber
    (b : ℕ) (hb : 2 ≤ b) (T : Fin b → Module.End K V) (u : ℕ → V)
    (hrec : ∀ n (r : Fin b), u (b * n + r.val) = T r (u n))
    (l : Module.Dual K V) (d : ℕ) (rows : Fin d → List (Fin b))
    (a : Fin d → K) (C : Fin b → Matrix (Fin d) (Fin d) K)
    (ha : ∀ x, l x = ∑ j, a j * l (linearWord T (rows j) x))
    (hC : ∀ r i x, l (linearWord T (rows i) (T r x)) =
      ∑ j, C r i j * l (linearWord T (rows j) x)) :
    ObservedWordMortal T l (u 0) ↔
      ∃ w : List (Fin b), ∀ n i,
        l (linearWord T (rows i) (linearWord T w (u n))) = 0 := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_⟩
    intro n i
    obtain ⟨z, hz⟩ := linearDigit_state_mem_orbit b hb T u hrec n
    change linearWord T z (u 0) = u n at hz
    rw [← hz]
    simpa only [linearWord_append, Module.End.mul_apply] using hw (rows i) z
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_⟩
    intro v z
    have hx : ∀ i, l (linearWord T (rows i)
        (linearWord T w (linearWord T z (u 0)))) = 0 := by
      rw [linearWord_apply_digitRecurrence_seed b T u hrec z]
      exact hw _
    have h := observable_all_words_zero_of_rows_zero T l d rows a C ha hC _ hx v
    simpa only [linearWord_append, Module.End.mul_apply] using h

end Model
end IndependentZeroBlocks
