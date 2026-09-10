import FiniteMonoidMortality.FiniteDimensionDetection
import FiniteMonoidMortality.ReachableSpanMortality
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option autoImplicit false

noncomputable section

namespace FiniteMonoidMortality

theorem exists_short_linearWord_not_mem
    {K E A : Type*} [Field K] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] (T : A → Module.End K E) (v : E)
    (S : Submodule K E) (hex : ∃ w : List A, linearWord T w v ∉ S) :
    ∃ w : List A, w.length ≤ Module.finrank K S ∧ linearWord T w v ∉ S := by
  by_contra h
  push Not at h
  let d := Module.finrank K S
  have hle : boundedLinearOrbitSpan T v (d + 1) ≤ S := by
    apply Submodule.span_le.mpr
    rintro x ⟨w, rfl⟩
    exact h w.1 (by have := w.2; omega)
  have hstrict (j : ℕ) (hj : j ≤ d) :
      boundedLinearOrbitSpan T v j < boundedLinearOrbitSpan T v (j + 1) := by
    apply lt_of_le_of_ne (boundedLinearOrbitSpan_mono T v (Nat.le_succ j))
    intro heq
    obtain ⟨w, hw⟩ := hex
    apply hw
    have hm := linearWord_mem_linearReachableSpan T v w
    rw [← boundedLinearOrbitSpan_eq_reachable_of_succ_eq T v j heq] at hm
    exact hle (boundedLinearOrbitSpan_mono T v (by omega : j ≤ d + 1) hm)
  have hg (j : ℕ) (hj : j ≤ d + 1) :
      j ≤ Module.finrank K (boundedLinearOrbitSpan T v j) := by
    induction j with
    | zero => omega
    | succ j ih =>
      have hs := Submodule.finrank_lt_finrank_of_lt (hstrict j (by omega))
      have hi := ih (by omega)
      omega
  have hi := hg (d + 1) le_rfl
  have hb := Submodule.finrank_mono hle
  omega

end FiniteMonoidMortality
