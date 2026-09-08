import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

set_option autoImplicit false

/-!
# From pointwise orbit mortality to one reachable-span annihilator

Word multiplication is composition: a word appended on the left acts after
the original word. No finiteness assumption on the generator alphabet is
needed. Finite generation of the reachable span suffices; finite-dimensional
vector spaces are the principal application.
-/

namespace IndependentZeroBlocks

section Semiring
variable {K V ι : Type*} [Semiring K] [AddCommMonoid V] [Module K V]

def linearWord (T : ι → Module.End K V) (w : List ι) : Module.End K V :=
  (w.map T).prod

@[simp] theorem linearWord_nil (T : ι → Module.End K V) : linearWord T [] = 1 := by
  simp [linearWord]

@[simp] theorem linearWord_cons (T : ι → Module.End K V) (i : ι) (w : List ι) :
    linearWord T (i :: w) = T i * linearWord T w := by
  simp [linearWord]

theorem linearWord_append (T : ι → Module.End K V) (u w : List ι) :
    linearWord T (u ++ w) = linearWord T u * linearWord T w := by
  simp [linearWord]

def linearOrbit (T : ι → Module.End K V) (v0 : V) : Set V :=
  Set.range fun w : List ι => linearWord T w v0

def linearReachableSpan (T : ι → Module.End K V) (v0 : V) : Submodule K V :=
  Submodule.span K (linearOrbit T v0)

theorem linearWord_mem_linearReachableSpan (T : ι → Module.End K V)
    (v0 : V) (w : List ι) : linearWord T w v0 ∈ linearReachableSpan T v0 :=
  Submodule.subset_span ⟨w, rfl⟩

theorem seed_mem_linearReachableSpan (T : ι → Module.End K V) (v0 : V) :
    v0 ∈ linearReachableSpan T v0 := by
  simpa using linearWord_mem_linearReachableSpan T v0 []

/-- The reachable span is invariant under every word action. -/
theorem linearWord_maps_linearReachableSpan (T : ι → Module.End K V)
    (v0 : V) (w : List ι) (x : V) (hx : x ∈ linearReachableSpan T v0) :
    linearWord T w x ∈ linearReachableSpan T v0 := by
  change x ∈ Submodule.span K (linearOrbit T v0) at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, rfl⟩ := hx
    rw [← Module.End.mul_apply, ← linearWord_append]
    exact linearWord_mem_linearReachableSpan T v0 (w ++ u)
  | zero => simp
  | add x y hx hy ihx ihy =>
    rw [map_add]
    exact Submodule.add_mem _ ihx ihy
  | smul c x hx ih =>
    rw [map_smul]
    exact Submodule.smul_mem _ c ih

/-- Orbitwise mortality extends to every reachable linear combination,
including after an arbitrary preliminary word. This stronger invariant makes
successive killing compatible with addition. -/
theorem linearReachableSpan_stably_killable
    (T : ι → Module.End K V) (v0 : V)
    (hkill : ∀ u : List ι, ∃ w : List ι, linearWord T w (linearWord T u v0) = 0)
    (x : V) (hx : x ∈ linearReachableSpan T v0) (u : List ι) :
    ∃ w : List ι, linearWord T w (linearWord T u x) = 0 := by
  have hstable : ∀ x ∈ Submodule.span K (linearOrbit T v0),
      ∀ u : List ι, ∃ w : List ι, linearWord T w (linearWord T u x) = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, rfl⟩ := hx
      intro u
      obtain ⟨w, hw⟩ := hkill (u ++ v)
      exact ⟨w, by simpa [linearWord_append, Module.End.mul_apply] using hw⟩
    | zero =>
      intro u
      exact ⟨[], by simp⟩
    | add x y hx hy ihx ihy =>
      intro u
      obtain ⟨v, hv⟩ := ihx u
      obtain ⟨w, hw⟩ := ihy (v ++ u)
      refine ⟨w ++ v, ?_⟩
      simp only [linearWord_append, Module.End.mul_apply, map_add]
      rw [hv, map_zero, zero_add]
      simpa only [linearWord_append, Module.End.mul_apply] using hw
    | smul c x hx ih =>
      intro u
      obtain ⟨w, hw⟩ := ih u
      exact ⟨w, by simp only [map_smul, hw, smul_zero]⟩
  exact hstable x hx u

/-- A finite set of stably killable vectors has one common killing word. -/
theorem linearWord_exists_killing_finset
    (T : ι → Module.End K V) (s : Finset V)
    (hkill : ∀ x ∈ s, ∀ u : List ι,
      ∃ w : List ι, linearWord T w (linearWord T u x) = 0) :
    ∃ w : List ι, ∀ x ∈ s, linearWord T w x = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨[], by simp⟩
  | @insert x s hx ih =>
    obtain ⟨u, hu⟩ := ih (fun y hy => hkill y (Finset.mem_insert_of_mem hy))
    obtain ⟨w, hw⟩ := hkill x (Finset.mem_insert_self x s) u
    refine ⟨w ++ u, ?_⟩
    intro y hy
    rw [linearWord_append, Module.End.mul_apply]
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hw
    · rw [hu y hy, map_zero]

/-- Finite generation is the exact algebraic compactness used here. Killing
each reachable state separately yields one word killing the whole span. -/
theorem linearReachableSpan_common_word_of_pointwise_of_fg
    (T : ι → Module.End K V) (v0 : V)
    (hfg : (linearReachableSpan T v0).FG)
    (hkill : ∀ u : List ι, ∃ w : List ι, linearWord T w (linearWord T u v0) = 0) :
    ∃ w : List ι, ∀ x ∈ linearReachableSpan T v0, linearWord T w x = 0 := by
  classical
  obtain ⟨s, hs⟩ := hfg
  have hstable : ∀ x ∈ s, ∀ u : List ι,
      ∃ w : List ι, linearWord T w (linearWord T u x) = 0 := by
    intro x hx u
    apply linearReachableSpan_stably_killable T v0 hkill x _ u
    rw [← hs]
    exact Submodule.subset_span hx
  obtain ⟨w, hw⟩ := linearWord_exists_killing_finset T s hstable
  refine ⟨w, ?_⟩
  have hle : Submodule.span K (↑s : Set V) ≤ LinearMap.ker (linearWord T w) := by
    apply Submodule.span_le.mpr
    intro x hx
    exact hw x hx
  rw [hs] at hle
  exact fun x hx => hle hx

end Semiring

section Field
variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- The finite-dimensional reachable span has a common annihilating word
exactly when every orbit point can be killed by some word. -/
theorem linearReachableSpan_mortal_iff_pointwise
    (T : ι → Module.End K V) (v0 : V) :
    (∃ w : List ι, ∀ x ∈ linearReachableSpan T v0, linearWord T w x = 0) ↔
      ∀ u : List ι, ∃ w : List ι, linearWord T w (linearWord T u v0) = 0 := by
  constructor
  · rintro ⟨w, hw⟩ u
    exact ⟨w, hw _ (linearWord_mem_linearReachableSpan T v0 u)⟩
  · intro hkill
    apply linearReachableSpan_common_word_of_pointwise_of_fg T v0 _ hkill
    exact (Submodule.fg_iff_finiteDimensional _).mpr inferInstance

/-- A common word can equivalently be tested on the orbit itself. -/
theorem linearOrbit_pointwise_mortal_iff_common_word
    (T : ι → Module.End K V) (v0 : V) :
    (∀ u : List ι, ∃ w : List ι, linearWord T w (linearWord T u v0) = 0) ↔
      ∃ w : List ι, ∀ u : List ι, linearWord T w (linearWord T u v0) = 0 := by
  constructor
  · intro h
    obtain ⟨w, hw⟩ := (linearReachableSpan_mortal_iff_pointwise T v0).mpr h
    exact ⟨w, fun u => hw _ (linearWord_mem_linearReachableSpan T v0 u)⟩
  · rintro ⟨w, hw⟩ u
    exact ⟨w, hw u⟩

/-- Failure of a common annihilator supplies a reachable state that survives
every continuation word. Such a state gives full supported digit cones. -/
theorem linearReachableSpan_not_mortal_iff_immortal_orbit
    (T : ι → Module.End K V) (v0 : V) :
    (¬ ∃ w : List ι, ∀ x ∈ linearReachableSpan T v0, linearWord T w x = 0) ↔
      ∃ u : List ι, ∀ w : List ι, linearWord T w (linearWord T u v0) ≠ 0 := by
  rw [linearReachableSpan_mortal_iff_pointwise T v0]
  push_neg
  rfl

theorem linearReachableSpan_mortal_or_immortal
    (T : ι → Module.End K V) (v0 : V) :
    (∃ w : List ι, ∀ x ∈ linearReachableSpan T v0, linearWord T w x = 0) ∨
      ∃ u : List ι, ∀ w : List ι, linearWord T w (linearWord T u v0) ≠ 0 := by
  classical
  by_cases h : ∃ w : List ι, ∀ x ∈ linearReachableSpan T v0, linearWord T w x = 0
  · exact Or.inl h
  · exact Or.inr ((linearReachableSpan_not_mortal_iff_immortal_orbit T v0).mp h)

end Field
end IndependentZeroBlocks
