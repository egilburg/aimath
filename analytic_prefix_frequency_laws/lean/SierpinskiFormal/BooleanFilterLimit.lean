import SierpinskiFormal.BooleanDoubleLimitClosure

set_option autoImplicit false

namespace IndependentZeroBlocks

open Filter Topology

/-- A proper-filter limit of the rows of a Boolean kernel agrees eventually
with the filter limit of their pointwise sequential limit. This is a
tailored filter form of the double-limit argument: all limits supplied to
the double-limit property are produced explicitly by a diagonal choice. -/
theorem eventually_rowFilterValue_eq_of_pointwise_eventually
    {X Y : Type*} (B : X → Y → Bool)
    (hB : HasBooleanDoubleLimitProperty B)
    (x : ℕ → X) (g : Y → Bool)
    (F : Filter Y) [F.NeBot]
    (hpointwise : ∀ y, ∀ᶠ n in atTop, B (x n) y = g y)
    (h : ℕ → Bool)
    (hrow : ∀ n, ∀ᶠ y in F, B (x n) y = h n)
    (c : Bool) (hg : ∀ᶠ y in F, g y = c) :
    ∀ᶠ n in atTop, h n = c := by
  classical
  by_contra hnot
  have hfrequent : ∃ᶠ n in atTop, h n ≠ c := by
    simpa only [not_eventually] using hnot
  obtain ⟨p, hpTop, hpWrong⟩ :=
    subseq_forall_of_frequently (x := id) (p := fun n ↦ h n ≠ c)
      (l := atTop) tendsto_id hfrequent
  have hpNot (n : ℕ) : h (p n) = Bool.not c := by
    have hn := hpWrong n
    cases hc : c <;> cases hh : h (p n) <;> simp_all
  have hchoice (j : ℕ) : ∃ y : Y,
      g y = c ∧ ∀ i ∈ Finset.range (j + 1), B (x (p i)) y = Bool.not c := by
    have hfinite : ∀ᶠ y in F,
        ∀ i ∈ Finset.range (j + 1), B (x (p i)) y = Bool.not c := by
      rw [Finset.eventually_all]
      intro i hi
      filter_upwards [hrow (p i)] with y hy
      rw [hy, hpNot i]
    exact (hg.and hfinite).exists
  choose y hy using hchoice
  have hrows (i : ℕ) : Tendsto
      (fun j ↦ boolIndicator (B (x (p i)) (y j))) atTop
      (nhds (boolIndicator (Bool.not c))) := by
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [eventually_ge_atTop i] with j hij
    rw [(hy j).2 i (Finset.mem_range.mpr (Nat.lt_succ_of_le hij))]
  have hcolumns (j : ℕ) : Tendsto
      (fun i ↦ boolIndicator (B (x (p i)) (y j))) atTop
      (nhds (boolIndicator c)) := by
    apply tendsto_nhds_of_eventually_eq
    have hpPointwise : ∀ᶠ i in atTop, B (x (p i)) (y j) = g (y j) :=
      hpTop.eventually (hpointwise (y j))
    filter_upwards [hpPointwise] with i hi
    rw [hi, (hy j).1]
  have heq : boolIndicator (Bool.not c) = boolIndicator c := by
    apply hB (x ∘ p) y
      (fun _ ↦ boolIndicator (Bool.not c)) (fun _ ↦ boolIndicator c)
      (boolIndicator (Bool.not c)) (boolIndicator c)
    · simpa [Function.comp_def] using hrows
    · simpa [Function.comp_def] using hcolumns
    · exact tendsto_const_nhds
    · exact tendsto_const_nhds
  have hcEq : Bool.not c = c := boolIndicator_injective heq
  cases c <;> simp at hcEq

/-- Every Boolean-valued function is constant almost everywhere along an
ultrafilter. -/
theorem exists_ultrafilter_eventual_bool
    {Y : Type*} (U : Ultrafilter Y) (g : Y → Bool) :
    ∃ c : Bool, ∀ᶠ y in (U : Filter Y), g y = c := by
  rcases U.em (fun y ↦ g y = true) with htrue | hfalse
  · exact ⟨true, htrue⟩
  · refine ⟨false, hfalse.mono ?_⟩
    intro y hy
    cases hgy : g y <;> simp_all

/-- Along an ultrafilter, the row values and the pointwise limit value exist
automatically, and the row values eventually equal the latter. -/
theorem exists_ultrafilter_rowValues_eventually_eq
    {X Y : Type*} (B : X → Y → Bool)
    (hB : HasBooleanDoubleLimitProperty B)
    (x : ℕ → X) (g : Y → Bool)
    (hpointwise : ∀ y, ∀ᶠ n in atTop, B (x n) y = g y)
    (U : Ultrafilter Y) :
    ∃ h : ℕ → Bool, ∃ c : Bool,
      (∀ n, ∀ᶠ y in (U : Filter Y), B (x n) y = h n) ∧
      (∀ᶠ y in (U : Filter Y), g y = c) ∧
      (∀ᶠ n in atTop, h n = c) := by
  choose h hh using fun n ↦ exists_ultrafilter_eventual_bool U (B (x n))
  obtain ⟨c, hc⟩ := exists_ultrafilter_eventual_bool U g
  refine ⟨h, c, hh, hc, ?_⟩
  exact eventually_rowFilterValue_eq_of_pointwise_eventually
    B hB x g (U : Filter Y) hpointwise h hh c hc

end IndependentZeroBlocks
