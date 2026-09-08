import SierpinskiFormal.ImmortalConeDensity
import SierpinskiFormal.UniformPowerClosure

set_option autoImplicit false

/-!
# Finite backward-window closure of a predicate

This file records that adjoining finitely many backward translates preserves
the density and support-geometry properties used by the matrix applications.
-/

namespace IndependentZeroBlocks

open Filter
open scoped Topology

/-- An index belongs to the backward `m`-window support when it is at most
`m-1` places to the right of an index satisfying `bad`. -/
def backwardWindowSupport (bad : ℕ → Prop) (m n : ℕ) : Prop :=
  ∃ t : ℕ, t < m ∧ ∃ k : ℕ, bad k ∧ n = k + t

/-- Equivalent subtraction form of membership in a backward window. -/
theorem backwardWindowSupport_iff_sub
    (bad : ℕ → Prop) (m n : ℕ) :
    backwardWindowSupport bad m n ↔
      ∃ t : ℕ, t < m ∧ t ≤ n ∧ bad (n - t) := by
  constructor
  · rintro ⟨t, ht, k, hk, rfl⟩
    exact ⟨t, ht, by omega, by simpa using hk⟩
  · rintro ⟨t, ht, htn, hbad⟩
    exact ⟨t, ht, n - t, hbad, (Nat.sub_add_cancel htn).symm⟩

/-- A nonempty backward window contains the original predicate. -/
theorem bad_imp_backwardWindowSupport
    {bad : ℕ → Prop} {m : ℕ} (hm : 1 ≤ m) {n : ℕ} (hn : bad n) :
    backwardWindowSupport bad m n := by
  exact ⟨0, hm, n, hn, by simp⟩

private theorem backwardWindowSupport_iff_fin
    (bad : ℕ → Prop) (m n : ℕ) :
    backwardWindowSupport bad m n ↔
      ∃ t : Fin m, ∃ k : ℕ, bad k ∧ n = t.1 + k := by
  constructor
  · rintro ⟨t, ht, k, hk, rfl⟩
    exact ⟨⟨t, ht⟩, k, hk, by simp [Nat.add_comm]⟩
  · rintro ⟨t, k, hk, rfl⟩
    exact ⟨t.1, t.2, k, hk, by simp [Nat.add_comm]⟩

private theorem predicateCount_mono_of_imp
    {bad₁ bad₂ : ℕ → Prop} (hsub : ∀ n, bad₁ n → bad₂ n) (N : ℕ) :
    predicateCount bad₁ N ≤ predicateCount bad₂ N := by
  classical
  unfold predicateCount
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
  exact ⟨hn.1, hsub n hn.2⟩

private theorem predicateCount_shift_le
    (bad : ℕ → Prop) (t N : ℕ) :
    predicateCount (fun n => ∃ k : ℕ, bad k ∧ n = t + k) N ≤
      predicateCount bad N := by
  classical
  let S := (Finset.range N).filter fun n => ∃ k : ℕ, bad k ∧ n = t + k
  let T := (Finset.range N).filter bad
  let f : ℕ → ℕ := fun n => n - t
  have hfmem : ∀ n ∈ S, f n ∈ T := by
    intro n hn
    obtain ⟨hnN, k, hk, hnk⟩ := Finset.mem_filter.mp hn
    have hnN' : n < N := Finset.mem_range.mp hnN
    have htk : t ≤ n := by omega
    have hf : f n = k := by dsimp [f]; omega
    rw [hf]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (lt_of_le_of_lt (by omega : k ≤ n) hnN'), hk⟩
  have hfinj : (S : Set ℕ).InjOn f := by
    intro n hn r hr hnr
    obtain ⟨_, k, _, hnk⟩ := Finset.mem_filter.mp hn
    obtain ⟨_, l, _, hrl⟩ := Finset.mem_filter.mp hr
    have htn : t ≤ n := by omega
    have htr : t ≤ r := by omega
    dsimp [f] at hnr
    omega
  have hcard := Finset.card_le_card_of_injOn f hfmem hfinj
  simpa [S, T, predicateCount] using hcard

/-- The count in a backward window is at most the window width times the
original prefix count, at the same cutoff. -/
theorem predicateCount_backwardWindowSupport_le
    (bad : ℕ → Prop) (m N : ℕ) :
    predicateCount (backwardWindowSupport bad m) N ≤
      m * predicateCount bad N := by
  let shifted : Fin m → ℕ → Prop := fun t n =>
    ∃ k : ℕ, bad k ∧ n = t.1 + k
  have heq : backwardWindowSupport bad m = fun n => ∃ t, shifted t n := by
    funext n
    apply propext
    exact backwardWindowSupport_iff_fin bad m n
  rw [heq]
  calc
    predicateCount (fun n => ∃ t, shifted t n) N ≤
        ∑ t : Fin m, predicateCount (shifted t) N :=
      predicateCount_exists_le shifted N
    _ ≤ ∑ _t : Fin m, predicateCount bad N := by
      apply Finset.sum_le_sum
      intro t _
      exact predicateCount_shift_le bad t.1 N
    _ = m * predicateCount bad N := by simp [Nat.mul_comm]

private theorem zeroPredicateDensity_of_count_le_mul
    {bad₁ bad₂ : ℕ → Prop} (c : ℝ) (_hc : 0 ≤ c)
    (hcount : ∀ N : ℕ,
      (predicateCount bad₁ N : ℝ) ≤ c * (predicateCount bad₂ N : ℝ))
    (hzero : HasZeroPredicateDensity bad₂) :
    HasZeroPredicateDensity bad₁ := by
  have hupper : Tendsto
      (fun N : ℕ => c * ((predicateCount bad₂ N : ℝ) / (N : ℝ)))
      atTop (𝓝 0) := by
    simpa using hzero.const_mul c
  apply squeeze_zero'
  · filter_upwards with N
    positivity
  · filter_upwards with N
    calc
      (predicateCount bad₁ N : ℝ) / (N : ℝ) ≤
          (c * (predicateCount bad₂ N : ℝ)) / (N : ℝ) :=
        div_le_div_of_nonneg_right (hcount N) (by positivity)
      _ = c * ((predicateCount bad₂ N : ℝ) / (N : ℝ)) := by ring
  · exact hupper

/-- A nonempty finite backward window has density zero exactly when the
original predicate does. -/
theorem hasZeroPredicateDensity_backwardWindowSupport_iff
    (bad : ℕ → Prop) {m : ℕ} (hm : 1 ≤ m) :
    HasZeroPredicateDensity (backwardWindowSupport bad m) ↔
      HasZeroPredicateDensity bad := by
  constructor
  · intro hwindow
    apply zeroPredicateDensity_of_count_le_mul 1 (by norm_num) ?_ hwindow
    intro N
    norm_num
    exact_mod_cast predicateCount_mono_of_imp
      (fun n hn => bad_imp_backwardWindowSupport hm hn) N
  · intro hbad
    apply zeroPredicateDensity_of_count_le_mul (m : ℝ) (by positivity) ?_ hbad
    intro N
    exact_mod_cast predicateCount_backwardWindowSupport_le bad m N

/-- A nonempty finite backward window has positive lower density exactly when
the original predicate does. -/
theorem hasPositiveLowerPredicateDensity_backwardWindowSupport_iff
    (bad : ℕ → Prop) {m : ℕ} (hm : 1 ≤ m) :
    HasPositiveLowerPredicateDensity (backwardWindowSupport bad m) ↔
      HasPositiveLowerPredicateDensity bad := by
  constructor
  · rintro ⟨c, hc, N₀, hwindow⟩
    have hmreal : (0 : ℝ) < (m : ℝ) := by positivity
    refine ⟨c / (m : ℝ), div_pos hc hmreal, N₀, ?_⟩
    intro N hN
    have hlower := hwindow N hN
    have hupper : (predicateCount (backwardWindowSupport bad m) N : ℝ) ≤
        (m : ℝ) * (predicateCount bad N : ℝ) := by
      exact_mod_cast predicateCount_backwardWindowSupport_le bad m N
    calc
      c / (m : ℝ) * (N : ℝ) = (c * (N : ℝ)) / (m : ℝ) := by ring
      _ ≤ (predicateCount bad N : ℝ) := by
        apply (div_le_iff₀ hmreal).2
        exact hlower.trans hupper |>.trans_eq (by ring)
  · rintro ⟨c, hc, N₀, hbad⟩
    refine ⟨c, hc, N₀, ?_⟩
    intro N hN
    exact (hbad N hN).trans (by
      exact_mod_cast predicateCount_mono_of_imp
        (fun n hn => bad_imp_backwardWindowSupport hm hn) N)

/-- A nonempty finite backward window has uniform relative holes exactly when
the original predicate does. -/
theorem hasUniformRelativeHoles_backwardWindowSupport_iff
    (bad : ℕ → Prop) {m : ℕ} (hm : 1 ≤ m) :
    HasUniformRelativeHoles (backwardWindowSupport bad m) ↔
      HasUniformRelativeHoles bad := by
  constructor
  · intro hwindow
    exact hwindow.mono (fun n hn => bad_imp_backwardWindowSupport hm hn)
  · intro hbad
    let shifted : Fin m → ℕ → Prop := fun t n =>
      ∃ k : ℕ, bad k ∧ n = t.1 + k
    have hshifted (t : Fin m) : HasUniformRelativeHoles (shifted t) := by
      simpa [shifted] using hbad.affineImage t.1 1 (by norm_num)
    have hunion := HasUniformRelativeHoles.finite_union shifted hshifted
    apply hunion.mono
    intro n hn
    rw [backwardWindowSupport_iff_fin bad m n] at hn
    exact hn

/-- A nonempty finite backward window has an eventual global power bound
exactly when the original predicate does. -/
theorem hasPowerPredicateBound_backwardWindowSupport_iff
    (bad : ℕ → Prop) (α : ℝ) {m : ℕ} (hm : 1 ≤ m) :
    HasPowerPredicateBound α (backwardWindowSupport bad m) ↔
      HasPowerPredicateBound α bad := by
  constructor
  · rintro ⟨C, hC, N₀, hwindow⟩
    refine ⟨C, hC, N₀, ?_⟩
    intro N hN
    have hsub : (predicateCount bad N : ℝ) ≤
        (predicateCount (backwardWindowSupport bad m) N : ℝ) := by
      exact_mod_cast predicateCount_mono_of_imp
        (fun n hn => bad_imp_backwardWindowSupport hm hn) N
    exact hsub.trans (hwindow N hN)
  · rintro ⟨C, hC, N₀, hbad⟩
    refine ⟨(m : ℝ) * C, mul_nonneg (by positivity) hC, N₀, ?_⟩
    intro N hN
    have hcount : (predicateCount (backwardWindowSupport bad m) N : ℝ) ≤
        (m : ℝ) * (predicateCount bad N : ℝ) := by
      exact_mod_cast predicateCount_backwardWindowSupport_le bad m N
    calc
      (predicateCount (backwardWindowSupport bad m) N : ℝ) ≤
          (m : ℝ) * (predicateCount bad N : ℝ) := hcount
      _ ≤ (m : ℝ) * (C * (N : ℝ) ^ α) :=
        mul_le_mul_of_nonneg_left (hbad N hN) (by positivity)
      _ = ((m : ℝ) * C) * (N : ℝ) ^ α := by ring

/-- A nonempty finite backward window has a uniform translated-interval power
bound exactly when the original predicate does. -/
theorem hasUniformPowerIntervalBound_backwardWindowSupport_iff
    (bad : ℕ → Prop) (α : ℝ) (hα : 0 ≤ α) {m : ℕ} (hm : 1 ≤ m) :
    HasUniformPowerIntervalBound α (backwardWindowSupport bad m) ↔
      HasUniformPowerIntervalBound α bad := by
  constructor
  · intro hwindow
    exact hwindow.mono (fun n hn => bad_imp_backwardWindowSupport hm hn)
  · intro hbad
    let shifted : Fin m → ℕ → Prop := fun t n =>
      ∃ k : ℕ, bad k ∧ n = t.1 + k
    have hshifted (t : Fin m) : HasUniformPowerIntervalBound α (shifted t) := by
      simpa [shifted] using hbad.affineImage hα t.1 1 (by norm_num)
    have hunion := HasUniformPowerIntervalBound.finite_union shifted hshifted
    apply hunion.mono
    intro n hn
    rw [backwardWindowSupport_iff_fin bad m n] at hn
    exact hn

end IndependentZeroBlocks
