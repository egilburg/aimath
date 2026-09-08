import SierpinskiFormal.ReachableSpanMortality
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option autoImplicit false

/-!
# Dimension cutoff for uniform word nilpotence

The common kernels of all exact-length word products form an increasing chain.
A plateau is permanent. Thus eventual universal zero implies universal zero at
the dimension of the state space. The alphabet need not be finite.
-/

namespace IndependentZeroBlocks

variable {K V A : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Recursive common kernel; `mem_commonKernel_iff` gives its word semantics. -/
def commonKernel (T : A → Module.End K V) : ℕ → Submodule K V
  | 0 => ⊥
  | n + 1 => ⨅ a, (commonKernel T n).comap (T a)

@[simp] theorem commonKernel_zero (T : A → Module.End K V) :
    commonKernel T 0 = ⊥ := rfl

theorem commonKernel_succ (T : A → Module.End K V) (n : ℕ) :
    commonKernel T (n + 1) = ⨅ a, (commonKernel T n).comap (T a) := rfl

theorem commonKernel_le_succ (T : A → Module.End K V) (n : ℕ) :
    commonKernel T n ≤ commonKernel T (n + 1) := by
  induction n with
  | zero => exact bot_le
  | succ n ih =>
      exact iInf_mono fun a => Submodule.comap_mono ih

theorem commonKernel_mono (T : A → Module.End K V) :
    Monotone (commonKernel T) :=
  monotone_nat_of_le_succ (commonKernel_le_succ T)

theorem mem_commonKernel_iff (T : A → Module.End K V) (n : ℕ) (x : V) :
    x ∈ commonKernel T n ↔
      ∀ w : List A, w.length = n → linearWord T w x = 0 := by
  induction n generalizing x with
  | zero => simp [commonKernel, List.length_eq_zero_iff]
  | succ n ih =>
      simp only [commonKernel_succ, Submodule.mem_iInf, Submodule.mem_comap, ih]
      constructor
      · intro h w hw
        induction w using List.reverseRecOn with
        | nil => simp at hw
        | append_singleton w a _ =>
            have hlen : w.length = n := by simpa using hw
            simpa [linearWord_append, linearWord, Module.End.mul_apply] using h a w hlen
      · intro h a w hw
        have hz := h (w ++ [a]) (by simp [hw])
        simpa [linearWord_append, linearWord, Module.End.mul_apply] using hz

theorem commonKernel_top_iff (T : A → Module.End K V) (n : ℕ) :
    commonKernel T n = ⊤ ↔
      ∀ w : List A, w.length = n → linearWord T w = 0 := by
  constructor
  · intro h w hw
    ext x
    exact (mem_commonKernel_iff T n x).mp (by rw [h]; trivial) w hw
  · intro h
    apply top_unique
    intro x _
    apply (mem_commonKernel_iff T n x).mpr
    intro w hw
    simp [h w hw]

/-- At a plateau, every stage is contained in that fixed stage. -/
theorem commonKernel_le_of_plateau (T : A → Module.End K V) (n : ℕ)
    (h : commonKernel T n = commonKernel T (n + 1)) (m : ℕ) :
    commonKernel T m ≤ commonKernel T n := by
  induction m with
  | zero => exact bot_le
  | succ m ih =>
      calc
        commonKernel T (m + 1) ≤ commonKernel T (n + 1) :=
          iInf_mono fun a => Submodule.comap_mono ih
        _ = commonKernel T n := h.symm

theorem commonKernel_plateau (T : A → Module.End K V) (n : ℕ)
    (h : commonKernel T n = commonKernel T (n + 1)) {m : ℕ} (hm : n ≤ m) :
    commonKernel T m = commonKernel T n :=
  le_antisymm (commonKernel_le_of_plateau T n h m) (commonKernel_mono T hm)

/-- Eventual universal nilpotence occurs by the ambient dimension. -/
theorem uniformNilpotence_cutoff_finrank [FiniteDimensional K V]
    (T : A → Module.End K V)
    (heventual : ∃ N : ℕ, ∀ w : List A, w.length = N → linearWord T w = 0) :
    ∀ w : List A, w.length = Module.finrank K V → linearWord T w = 0 := by
  apply (commonKernel_top_iff T _).mp
  obtain ⟨N, hN⟩ := heventual
  have htop := (commonKernel_top_iff T N).mpr hN
  let d := Module.finrank K V
  by_contra hne
  have hstrict : ∀ n, n < d → commonKernel T n < commonKernel T (n + 1) := by
    intro n hn
    apply lt_of_le_of_ne (commonKernel_le_succ T n)
    intro heq
    have hNle := commonKernel_le_of_plateau T n heq N
    rw [htop] at hNle
    apply hne
    exact top_unique (hNle.trans (commonKernel_mono T hn.le))
  have hrank : ∀ n, n ≤ d → n ≤ Module.finrank K (commonKernel T n) := by
    intro n hn
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih =>
        exact (Nat.succ_le_succ (ih (by omega))).trans
          (Nat.succ_le_of_lt (Submodule.finrank_lt_finrank_of_lt (hstrict n (by omega))))
  have hproper : commonKernel T d < ⊤ := lt_of_le_of_ne le_top hne
  have hlt := Submodule.finrank_lt_finrank_of_lt hproper
  have hbound : Module.finrank K (⊤ : Submodule K V) ≤ d := Submodule.finrank_le _
  exact (Nat.not_lt_of_ge (hrank d le_rfl)) (hlt.trans_le hbound)

end IndependentZeroBlocks
