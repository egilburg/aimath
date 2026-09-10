import FiniteMonoidMortality.ReachableSpanMortality

set_option autoImplicit false

namespace FiniteMonoidMortality

section ShortOrbit

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

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

end ShortOrbit

section DetectingContexts

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

end DetectingContexts

end FiniteMonoidMortality
