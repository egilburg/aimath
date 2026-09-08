import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.BigOperators.Group.List.Basic

set_option autoImplicit false

/-!
# Short spanning words for linear orbits

The ascending orbit spans stabilize before the ambient dimension. This is the linear witness lemma used by the quadratic observation.
-/

noncomputable section

open scoped BigOperators

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

section ShortOrbit

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The span of orbit vectors represented by words shorter than `n`. -/
def boundedLinearOrbitSpan (T : ι → Module.End K V) (v0 : V) (n : ℕ) :
    Submodule K V :=
  Submodule.span K (Set.range fun w : {w : List ι // w.length < n} =>
    linearWord T w.1 v0)

theorem boundedLinearOrbitSpan_mono (T : ι → Module.End K V) (v0 : V)
    {m n : ℕ} (hmn : m ≤ n) :
    boundedLinearOrbitSpan T v0 m ≤ boundedLinearOrbitSpan T v0 n := by
  apply Submodule.span_mono
  rintro x ⟨w, rfl⟩
  exact ⟨⟨w.1, w.2.trans_le hmn⟩, rfl⟩

theorem boundedLinearOrbitSpan_le_reachable (T : ι → Module.End K V)
    (v0 : V) (n : ℕ) :
    boundedLinearOrbitSpan T v0 n ≤ linearReachableSpan T v0 := by
  apply Submodule.span_le.mpr
  rintro x ⟨w, rfl⟩
  exact linearWord_mem_linearReachableSpan T v0 w.1

/-- Once two consecutive bounded orbit spans agree, that span is invariant
and therefore already equals the full reachable span. -/
theorem boundedLinearOrbitSpan_eq_reachable_of_succ_eq
    (T : ι → Module.End K V) (v0 : V) (n : ℕ)
    (hstable : boundedLinearOrbitSpan T v0 n =
      boundedLinearOrbitSpan T v0 (n + 1)) :
    boundedLinearOrbitSpan T v0 n = linearReachableSpan T v0 := by
  have hinvariant (r : ι) (x : V)
      (hx : x ∈ boundedLinearOrbitSpan T v0 n) :
      T r x ∈ boundedLinearOrbitSpan T v0 n := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨w, rfl⟩ := hx
        rw [← Module.End.mul_apply, ← linearWord_cons]
        rw [hstable]
        apply Submodule.subset_span
        exact ⟨⟨r :: w.1, by simpa using Nat.succ_le_succ w.2⟩, rfl⟩
    | zero => simp
    | add x y hx hy ihx ihy => simpa using Submodule.add_mem _ ihx ihy
    | smul c x hx ih => simpa using Submodule.smul_mem _ c ih
  apply le_antisymm (boundedLinearOrbitSpan_le_reachable T v0 n)
  apply Submodule.span_le.mpr
  rintro x ⟨w, rfl⟩
  induction w with
  | nil =>
      rw [hstable]
      apply Submodule.subset_span
      exact ⟨⟨[], by simp⟩, by simp⟩
  | cons r w ih =>
      change linearWord T (r :: w) v0 ∈ boundedLinearOrbitSpan T v0 n
      rw [linearWord_cons, Module.End.mul_apply]
      exact hinvariant r _ ih

/-- Words shorter than the ambient dimension span the whole reachable
space.  This includes the zero-dimensional case. -/
theorem boundedLinearOrbitSpan_finrank_eq_reachable [FiniteDimensional K V]
    (T : ι → Module.End K V) (v0 : V) :
    boundedLinearOrbitSpan T v0 (Module.finrank K V) =
      linearReachableSpan T v0 := by
  let d := Module.finrank K V
  by_contra hne
  have hstrict : ∀ n, n < d →
      boundedLinearOrbitSpan T v0 n < boundedLinearOrbitSpan T v0 (n + 1) := by
    intro n hn
    have hle := boundedLinearOrbitSpan_mono T v0 (Nat.le_succ n)
    exact lt_of_le_of_ne hle (fun heq => hne <| le_antisymm
      (boundedLinearOrbitSpan_le_reachable T v0 d) <| by
        rw [← boundedLinearOrbitSpan_eq_reachable_of_succ_eq T v0 n heq]
        exact boundedLinearOrbitSpan_mono T v0 hn.le)
  have hrank : ∀ n, n ≤ d →
      n ≤ Module.finrank K (boundedLinearOrbitSpan T v0 n) := by
    intro n hn
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih =>
        have hnlt : n < d := by omega
        exact (Nat.succ_le_succ (ih (by omega))).trans
          (Nat.succ_le_of_lt (Submodule.finrank_lt_finrank_of_lt (hstrict n hnlt)))
  have hproper : boundedLinearOrbitSpan T v0 d < linearReachableSpan T v0 :=
    lt_of_le_of_ne (boundedLinearOrbitSpan_le_reachable T v0 d) hne
  have hlt := Submodule.finrank_lt_finrank_of_lt hproper
  have hreach : Module.finrank K (linearReachableSpan T v0) ≤ d :=
    Submodule.finrank_le _
  exact (Nat.not_lt_of_ge (hrank d le_rfl)) (hlt.trans_le hreach)

end ShortOrbit

end FiniteMonoidMortality
