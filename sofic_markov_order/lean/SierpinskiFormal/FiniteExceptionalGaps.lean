import SierpinskiFormal.SparseIntervalDefs

set_option autoImplicit false

namespace IndependentZeroBlocks

/-- Number of indices in `[a, a + M)` satisfying a predicate. -/
noncomputable def intervalPredicateCount (bad : ℕ → Prop) (a M : ℕ) : ℕ := by
  classical
  exact ((Finset.range M).filter fun j => bad (a + j)).card

/-- A local exceptional-point count is bounded by the count below the right endpoint. -/
theorem intervalPredicateCount_le_predicateCount
    (bad : ℕ → Prop) (a M : ℕ) :
    intervalPredicateCount bad a M ≤ predicateCount bad (a + M) := by
  classical
  let f : ℕ → ℕ := fun j => a + j
  have hf_inj : Set.InjOn f
      (↑((Finset.range M).filter fun j => bad (a + j)) : Set ℕ) := by
    intro x _ y _ hxy
    exact Nat.add_left_cancel hxy
  have hsubset :
      Finset.image f ((Finset.range M).filter fun j => bad (a + j)) ⊆
        (Finset.range (a + M)).filter bad := by
    intro n hn
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hn
    have hj' := Finset.mem_filter.mp hj
    have hendpoint : f j < a + M := by
      dsimp [f]
      exact Nat.add_lt_add_left (Finset.mem_range.mp hj'.1) a
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hendpoint, hj'.2⟩
  calc
    intervalPredicateCount bad a M =
        (((Finset.range M).filter fun j => bad (a + j))).card := by
      simp [intervalPredicateCount]
    _ = (Finset.image f
        ((Finset.range M).filter fun j => bad (a + j))).card :=
      (Finset.card_image_of_injOn hf_inj).symm
    _ ≤ ((Finset.range (a + M)).filter bad).card :=
      Finset.card_le_card hsubset
    _ = predicateCount bad (a + M) := by simp [predicateCount]

private lemma count_blocks_le_intervalPredicateCount
    {bad : ℕ → Prop} {a M L t : ℕ} (hL : 0 < L)
    (hfit : L * t ≤ M)
    (hblocks : ∀ k : ℕ, k < t →
      ∃ j : ℕ, j < L ∧ bad (a + (L * k + j))) :
    t ≤ intervalPredicateCount bad a M := by
  classical
  let w : ℕ → ℕ := fun k =>
    if hk : k < t then Classical.choose (hblocks k hk) else 0
  have hwL (k : ℕ) (hk : k < t) : w k < L := by
    simp only [w, dif_pos hk]
    exact (Classical.choose_spec (hblocks k hk)).1
  have hwbad (k : ℕ) (hk : k < t) :
      bad (a + (L * k + w k)) := by
    simp only [w, dif_pos hk]
    exact (Classical.choose_spec (hblocks k hk)).2
  let f : ℕ → ℕ := fun k => L * k + w k
  have hf_lt (k : ℕ) (hk : k < t) : f k < M := by
    have hk' : k + 1 ≤ t := Nat.succ_le_iff.mpr hk
    have hblock_end : L * (k + 1) ≤ L * t := Nat.mul_le_mul_left L hk'
    calc
      f k = L * k + w k := rfl
      _ < L * (k + 1) := by
        rw [Nat.mul_add]
        simpa using Nat.add_lt_add_left (hwL k hk) (L * k)
      _ ≤ L * t := hblock_end
      _ ≤ M := hfit
  have hf_bad (k : ℕ) (hk : k < t) : bad (a + f k) := by
    simpa [f] using hwbad k hk
  have hf_inj : Set.InjOn f (↑(Finset.range t) : Set ℕ) := by
    intro x hx y hy hxy
    have hx' : x < t := Finset.mem_range.mp hx
    have hy' : y < t := Finset.mem_range.mp hy
    have hdiv := congrArg (fun n : ℕ => n / L) hxy
    simpa [f, Nat.mul_add_div hL, Nat.div_eq_of_lt (hwL x hx'),
      Nat.div_eq_of_lt (hwL y hy')] using hdiv
  have hsubset : Finset.image f (Finset.range t) ⊆
      (Finset.range M).filter fun j => bad (a + j) := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    have hk' : k < t := Finset.mem_range.mp hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hf_lt k hk'), hf_bad k hk'⟩
  calc
    t = (Finset.range t).card := by simp
    _ = (Finset.image f (Finset.range t)).card :=
      (Finset.card_image_of_injOn hf_inj).symm
    _ ≤ ((Finset.range M).filter fun j => bad (a + j)).card :=
      Finset.card_le_card hsubset
    _ = intervalPredicateCount bad a M := by simp [intervalPredicateCount]

/-- If at most `s` bad points lie in `[a, a + M)`, it contains a clean interval
of length `M / (s + 1)`. -/
theorem exists_clean_subinterval_of_count_le
    (bad : ℕ → Prop) (a M s : ℕ)
    (hcount : intervalPredicateCount bad a M ≤ s) :
    ∃ n : ℕ, a ≤ n ∧ n + M / (s + 1) ≤ a + M ∧
      ∀ j : ℕ, j < M / (s + 1) → ¬bad (n + j) := by
  classical
  let L := M / (s + 1)
  by_cases hLzero : L = 0
  · refine ⟨a, le_rfl, ?_, ?_⟩
    · simp [L, hLzero]
    · intro j hj
      simp [L, hLzero] at hj
  have hL : 0 < L := Nat.pos_of_ne_zero hLzero
  have hfit : L * (s + 1) ≤ M := by
    dsimp [L]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self M (s + 1)
  by_cases hclean : ∃ k : ℕ, k < s + 1 ∧
      ∀ j : ℕ, j < L → ¬bad (a + (L * k + j))
  · obtain ⟨k, hk, hkclean⟩ := hclean
    refine ⟨a + L * k, Nat.le_add_right a _, ?_, ?_⟩
    · have hk' : k + 1 ≤ s + 1 := Nat.succ_le_iff.mpr hk
      change a + L * k + L ≤ a + M
      calc
        a + L * k + L = a + L * (k + 1) := by
          simp [Nat.mul_add, Nat.add_assoc]
        _ ≤ a + L * (s + 1) :=
          Nat.add_le_add_left (Nat.mul_le_mul_left L hk') a
        _ ≤ a + M := Nat.add_le_add_left hfit a
    · intro j hj
      simpa only [Nat.add_assoc] using hkclean j hj
  · have hblocks : ∀ k : ℕ, k < s + 1 →
        ∃ j : ℕ, j < L ∧ bad (a + (L * k + j)) := by
      intro k hk
      by_cases hex : ∃ j : ℕ, j < L ∧ bad (a + (L * k + j))
      · exact hex
      · exfalso
        apply hclean
        refine ⟨k, hk, ?_⟩
        intro j hj hjbad
        exact hex ⟨j, hj, hjbad⟩
    have hlower : s + 1 ≤ intervalPredicateCount bad a M :=
      count_blocks_le_intervalPredicateCount hL hfit hblocks
    omega

/-- Every finite interval has a clean subinterval whose length is controlled by
the total number of bad points below its right endpoint. -/
theorem exists_clean_subinterval (bad : ℕ → Prop) (a M : ℕ) :
    ∃ n : ℕ, a ≤ n ∧
      n + M / (predicateCount bad (a + M) + 1) ≤ a + M ∧
      ∀ j : ℕ, j < M / (predicateCount bad (a + M) + 1) → ¬bad (n + j) := by
  apply exists_clean_subinterval_of_count_le bad a M (predicateCount bad (a + M))
  exact intervalPredicateCount_le_predicateCount bad a M

/-- Real-valued form of the finite clean-gap bound, with the loss from taking
the integer floor made explicit. -/
theorem exists_clean_subinterval_real_bound (bad : ℕ → Prop) (a M : ℕ) :
    ∃ n L : ℕ, a ≤ n ∧ n + L ≤ a + M ∧
      (M : ℝ) / ((predicateCount bad (a + M) : ℝ) + 1) - 1 < (L : ℝ) ∧
      ∀ j : ℕ, j < L → ¬bad (n + j) := by
  let d := predicateCount bad (a + M) + 1
  let L := M / d
  obtain ⟨n, hnleft, hnright, hnclean⟩ := exists_clean_subinterval bad a M
  have hd : 0 < d := by simp [d]
  have hnat : M < (L + 1) * d := by
    exact (Nat.div_lt_iff_lt_mul hd).mp (by simp [L])
  have hdreal : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hdiv : (M : ℝ) / (d : ℝ) < (L : ℝ) + 1 := by
    apply (div_lt_iff₀ hdreal).2
    exact_mod_cast hnat
  refine ⟨n, L, hnleft, ?_, ?_, ?_⟩
  · simpa [L, d] using hnright
  · simpa [d] using (show (M : ℝ) / (d : ℝ) - 1 < (L : ℝ) by linarith)
  · simpa [L, d] using hnclean

end IndependentZeroBlocks
