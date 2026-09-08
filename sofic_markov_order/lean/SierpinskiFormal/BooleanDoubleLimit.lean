import SierpinskiFormal.NoetherianStaircase

set_option autoImplicit false

namespace IndependentZeroBlocks

open Filter Topology

/-- A convergent real sequence with values in `{0, 1}` is eventually equal
to its limit. -/
theorem eventually_eq_limit_of_zero_one
    (u : ℕ → ℝ) (a : ℝ)
    (hu : ∀ n, u n = 0 ∨ u n = 1)
    (ha : Tendsto u atTop (nhds a)) :
    ∀ᶠ n in atTop, u n = a := by
  have ha01 : a ∈ ({0, 1} : Set ℝ) := by
    apply (Set.toFinite ({0, 1} : Set ℝ)).isClosed.mem_of_tendsto ha
    exact Filter.Eventually.of_forall fun n ↦ by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hu n
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha01
  rcases ha01 with rfl | rfl
  · obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp ha) 1 zero_lt_one
    filter_upwards [eventually_ge_atTop N] with n hn
    rcases hu n with hzero | hone
    · exact hzero
    · specialize hN n hn
      rw [hone] at hN
      norm_num [Real.dist_eq] at hN
  · obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp ha) 1 zero_lt_one
    filter_upwards [eventually_ge_atTop N] with n hn
    rcases hu n with hzero | hone
    · specialize hN n hn
      rw [hzero] at hN
      norm_num [Real.dist_eq] at hN
    · exact hone

/-- Alternating indices used to extract a staircase from incompatible
row and column limits. -/
private def alternatingIndices
    (rowCut columnCut : ℕ → ℕ) (rowStart columnStart : ℕ) :
    ℕ → ℕ × ℕ
  | 0 =>
      let y := columnStart
      (max rowStart (columnCut y), y)
  | n + 1 =>
      let previous := alternatingIndices rowCut columnCut rowStart columnStart n
      let y := max (previous.2 + 1) (rowCut previous.1)
      (max (previous.1 + 1) (columnCut y), y)

private theorem alternatingIndices_fst_le_succ
    (rowCut columnCut : ℕ → ℕ) (rowStart columnStart n : ℕ) :
    (alternatingIndices rowCut columnCut rowStart columnStart n).1 ≤
      (alternatingIndices rowCut columnCut rowStart columnStart (n + 1)).1 := by
  simp [alternatingIndices]

private theorem alternatingIndices_snd_le_succ
    (rowCut columnCut : ℕ → ℕ) (rowStart columnStart n : ℕ) :
    (alternatingIndices rowCut columnCut rowStart columnStart n).2 ≤
      (alternatingIndices rowCut columnCut rowStart columnStart (n + 1)).2 := by
  simp [alternatingIndices]

private theorem alternatingIndices_fst_monotone
    (rowCut columnCut : ℕ → ℕ) (rowStart columnStart : ℕ) :
    Monotone (fun n ↦ (alternatingIndices rowCut columnCut rowStart columnStart n).1) := by
  apply monotone_nat_of_le_succ
  exact alternatingIndices_fst_le_succ rowCut columnCut rowStart columnStart

private theorem alternatingIndices_snd_monotone
    (rowCut columnCut : ℕ → ℕ) (rowStart columnStart : ℕ) :
    Monotone (fun n ↦ (alternatingIndices rowCut columnCut rowStart columnStart n).2) := by
  apply monotone_nat_of_le_succ
  exact alternatingIndices_snd_le_succ rowCut columnCut rowStart columnStart

private theorem rowCut_le_alternatingIndices_snd
    (rowCut columnCut : ℕ → ℕ) (rowStart columnStart i j : ℕ)
    (hij : i < j) :
    rowCut (alternatingIndices rowCut columnCut rowStart columnStart i).1 ≤
      (alternatingIndices rowCut columnCut rowStart columnStart j).2 := by
  have hstep :
      rowCut (alternatingIndices rowCut columnCut rowStart columnStart i).1 ≤
        (alternatingIndices rowCut columnCut rowStart columnStart (i + 1)).2 := by
    simp [alternatingIndices]
  exact hstep.trans (alternatingIndices_snd_monotone
    rowCut columnCut rowStart columnStart (Nat.succ_le_iff.mpr hij))

private theorem columnCut_le_alternatingIndices_fst_self
    (rowCut columnCut : ℕ → ℕ) (rowStart columnStart n : ℕ) :
    columnCut (alternatingIndices rowCut columnCut rowStart columnStart n).2 ≤
      (alternatingIndices rowCut columnCut rowStart columnStart n).1 := by
  cases n with
  | zero => simp [alternatingIndices]
  | succ n => simp [alternatingIndices]

private theorem columnCut_le_alternatingIndices_fst
    (rowCut columnCut : ℕ → ℕ) (rowStart columnStart i j : ℕ)
    (hij : i ≤ j) :
    columnCut (alternatingIndices rowCut columnCut rowStart columnStart i).2 ≤
      (alternatingIndices rowCut columnCut rowStart columnStart j).1 := by
  exact (columnCut_le_alternatingIndices_fst_self
    rowCut columnCut rowStart columnStart i).trans
      (alternatingIndices_fst_monotone
        rowCut columnCut rowStart columnStart hij)

private theorem rowStart_le_alternatingIndices_fst
    (rowCut columnCut : ℕ → ℕ) (rowStart columnStart n : ℕ) :
    rowStart ≤ (alternatingIndices rowCut columnCut rowStart columnStart n).1 := by
  exact (by simp [alternatingIndices] :
    rowStart ≤ (alternatingIndices rowCut columnCut rowStart columnStart 0).1).trans
      (alternatingIndices_fst_monotone rowCut columnCut rowStart columnStart
        (Nat.zero_le n))

private theorem columnStart_le_alternatingIndices_snd
    (rowCut columnCut : ℕ → ℕ) (rowStart columnStart n : ℕ) :
    columnStart ≤ (alternatingIndices rowCut columnCut rowStart columnStart n).2 := by
  exact (by simp [alternatingIndices] :
    columnStart ≤ (alternatingIndices rowCut columnCut rowStart columnStart 0).2).trans
      (alternatingIndices_snd_monotone rowCut columnCut rowStart columnStart
        (Nat.zero_le n))

/-- A zero-one matrix whose row and column iterated limits both exist but
differ contains one of the two infinite strict staircases. -/
theorem zero_one_matrix_staircase_of_distinct_iterated_limits
    (f : ℕ → ℕ → ℝ)
    (hzeroOne : ∀ i j, f i j = 0 ∨ f i j = 1)
    (rowLimit columnLimit : ℕ → ℝ) (rowOuter columnOuter : ℝ)
    (hrow : ∀ i, Tendsto (f i) atTop (nhds (rowLimit i)))
    (hcolumn : ∀ j, Tendsto (fun i ↦ f i j) atTop (nhds (columnLimit j)))
    (hrowOuter : Tendsto rowLimit atTop (nhds rowOuter))
    (hcolumnOuter : Tendsto columnLimit atTop (nhds columnOuter))
    (hne : rowOuter ≠ columnOuter) :
    (∃ x y : ℕ → ℕ,
      (∀ i j, i < j → f (x i) (y j) = 0) ∧
      (∀ i j, j ≤ i → f (x i) (y j) = 1)) ∨
    (∃ x y : ℕ → ℕ,
      (∀ i j, i < j → f (x j) (y i) = 0) ∧
      (∀ i j, j ≤ i → f (x j) (y i) = 1)) := by
  have hrowValue (i : ℕ) : rowLimit i = 0 ∨ rowLimit i = 1 := by
    have he := eventually_eq_limit_of_zero_one (f i) (rowLimit i)
      (hzeroOne i) (hrow i)
    obtain ⟨j, hj⟩ := he.exists
    rw [← hj]
    exact hzeroOne i j
  have hcolumnValue (j : ℕ) : columnLimit j = 0 ∨ columnLimit j = 1 := by
    have he := eventually_eq_limit_of_zero_one (fun i ↦ f i j) (columnLimit j)
      (fun i ↦ hzeroOne i j) (hcolumn j)
    obtain ⟨i, hi⟩ := he.exists
    rw [← hi]
    exact hzeroOne i j
  have hrowOuterEventually := eventually_eq_limit_of_zero_one
    rowLimit rowOuter hrowValue hrowOuter
  have hcolumnOuterEventually := eventually_eq_limit_of_zero_one
    columnLimit columnOuter hcolumnValue hcolumnOuter
  have hrowOuterValue : rowOuter = 0 ∨ rowOuter = 1 := by
    obtain ⟨i, hi⟩ := hrowOuterEventually.exists
    rw [← hi]
    exact hrowValue i
  have hcolumnOuterValue : columnOuter = 0 ∨ columnOuter = 1 := by
    obtain ⟨j, hj⟩ := hcolumnOuterEventually.exists
    rw [← hj]
    exact hcolumnValue j
  obtain ⟨rowStart, hrowStart⟩ := eventually_atTop.mp hrowOuterEventually
  obtain ⟨columnStart, hcolumnStart⟩ := eventually_atTop.mp hcolumnOuterEventually
  choose rowCut hrowCut using fun i ↦ eventually_atTop.mp
    (eventually_eq_limit_of_zero_one (f i) (rowLimit i) (hzeroOne i) (hrow i))
  choose columnCut hcolumnCut using fun j ↦ eventually_atTop.mp
    (eventually_eq_limit_of_zero_one (fun i ↦ f i j) (columnLimit j)
      (fun i ↦ hzeroOne i j) (hcolumn j))
  rcases hrowOuterValue with hro | hro <;>
    rcases hcolumnOuterValue with hco | hco
  · exact False.elim (hne (hro.trans hco.symm))
  · left
    let p := alternatingIndices rowCut columnCut rowStart columnStart
    let x : ℕ → ℕ := fun n ↦ (p n).1
    let y : ℕ → ℕ := fun n ↦ (p n).2
    refine ⟨x, y, ?_, ?_⟩
    · intro i j hij
      rw [hrowCut (x i) (y j) (by
        exact rowCut_le_alternatingIndices_snd
          rowCut columnCut rowStart columnStart i j hij)]
      rw [hrowStart (x i) (by
        exact rowStart_le_alternatingIndices_fst
          rowCut columnCut rowStart columnStart i)]
      exact hro
    · intro i j hji
      change f (x i) (y j) = 1
      rw [hcolumnCut (y j) (x i) (by
        exact columnCut_le_alternatingIndices_fst
          rowCut columnCut rowStart columnStart j i hji)]
      rw [hcolumnStart (y j) (by
        exact columnStart_le_alternatingIndices_snd
          rowCut columnCut rowStart columnStart j)]
      exact hco
  · right
    let p := alternatingIndices columnCut rowCut columnStart rowStart
    let y : ℕ → ℕ := fun n ↦ (p n).1
    let x : ℕ → ℕ := fun n ↦ (p n).2
    refine ⟨x, y, ?_, ?_⟩
    · intro i j hij
      change f (x j) (y i) = 0
      rw [hcolumnCut (y i) (x j) (by
        exact rowCut_le_alternatingIndices_snd
          columnCut rowCut columnStart rowStart i j hij)]
      rw [hcolumnStart (y i) (by
        exact rowStart_le_alternatingIndices_fst
          columnCut rowCut columnStart rowStart i)]
      exact hco
    · intro i j hji
      rw [hrowCut (x j) (y i) (by
        exact columnCut_le_alternatingIndices_fst
          columnCut rowCut columnStart rowStart j i hji)]
      rw [hrowStart (x j) (by
        exact columnStart_le_alternatingIndices_snd
          columnCut rowCut columnStart rowStart j)]
      exact hro
  · exact False.elim (hne (hro.trans hco.symm))

/-- If both zero/nonzero staircase orientations are forbidden, every pair
of existing iterated limits of a zero-one matrix agree. -/
theorem zero_one_double_limit_of_no_staircases
    (f : ℕ → ℕ → ℝ)
    (hzeroOne : ∀ i j, f i j = 0 ∨ f i j = 1)
    (hnoUpper : ∀ x y : ℕ → ℕ,
      (∀ i j, i < j → f (x i) (y j) = 0) →
      (∀ i, f (x i) (y i) ≠ 0) → False)
    (hnoLower : ∀ x y : ℕ → ℕ,
      (∀ i j, i < j → f (x j) (y i) = 0) →
      (∀ i, f (x i) (y i) ≠ 0) → False)
    (rowLimit columnLimit : ℕ → ℝ) (rowOuter columnOuter : ℝ)
    (hrow : ∀ i, Tendsto (f i) atTop (nhds (rowLimit i)))
    (hcolumn : ∀ j, Tendsto (fun i ↦ f i j) atTop (nhds (columnLimit j)))
    (hrowOuter : Tendsto rowLimit atTop (nhds rowOuter))
    (hcolumnOuter : Tendsto columnLimit atTop (nhds columnOuter)) :
    rowOuter = columnOuter := by
  classical
  by_contra hne
  rcases zero_one_matrix_staircase_of_distinct_iterated_limits f hzeroOne
      rowLimit columnLimit rowOuter columnOuter hrow hcolumn hrowOuter
      hcolumnOuter hne with hupper | hlower
  · obtain ⟨x, y, hzero, hone⟩ := hupper
    exact hnoUpper x y hzero (fun i hi ↦ by simpa [hi] using hone i i le_rfl)
  · obtain ⟨x, y, hzero, hone⟩ := hlower
    exact hnoLower x y hzero (fun i hi ↦ by simpa [hi] using hone i i le_rfl)

/-- The real-valued indicator that a scalar is nonzero. -/
noncomputable def nonzeroIndicator {K : Type*} [Zero K] (z : K) : ℝ :=
  by
    classical
    exact if z = 0 then 0 else 1

@[simp] theorem nonzeroIndicator_eq_zero_iff
    {K : Type*} [Zero K] (z : K) :
    nonzeroIndicator z = 0 ↔ z = 0 := by
  classical
  simp [nonzeroIndicator]

@[simp] theorem nonzeroIndicator_eq_one_iff
    {K : Type*} [Zero K] (z : K) :
    nonzeroIndicator z = 1 ↔ z ≠ 0 := by
  classical
  simp [nonzeroIndicator]

theorem nonzeroIndicator_zero_one
    {K : Type*} [Zero K] (z : K) :
    nonzeroIndicator z = 0 ∨ nonzeroIndicator z = 1 := by
  classical
  by_cases hz : z = 0 <;> simp [nonzeroIndicator, hz]

/-- The real support indicator of a finite matrix-word coefficient over an
arbitrary commutative ring satisfies the sequential double-limit property.
This is the concrete Boolean conclusion of the two Noetherian staircase
obstructions; it does not assert the topological WAP criterion. -/
theorem commRing_matrixWords_nonzeroIndicator_double_limit
    {K ι : Type*} [CommRing K] [Fintype ι]
    {b : ℕ} (M : Fin b → Matrix ι ι K) (u a : ι → K)
    (x y : ℕ → List (Fin b))
    (rowLimit columnLimit : ℕ → ℝ) (rowOuter columnOuter : ℝ)
    (hrow : ∀ i, Tendsto
      (fun j ↦ nonzeroIndicator
        (coordinateRowDual a
          (linearWord (fun r ↦ Matrix.mulVecLin (M r)) (x i ++ y j) u)))
      atTop (nhds (rowLimit i)))
    (hcolumn : ∀ j, Tendsto
      (fun i ↦ nonzeroIndicator
        (coordinateRowDual a
          (linearWord (fun r ↦ Matrix.mulVecLin (M r)) (x i ++ y j) u)))
      atTop (nhds (columnLimit j)))
    (hrowOuter : Tendsto rowLimit atTop (nhds rowOuter))
    (hcolumnOuter : Tendsto columnLimit atTop (nhds columnOuter)) :
    rowOuter = columnOuter := by
  classical
  let coefficient : ℕ → ℕ → K := fun i j ↦
    coordinateRowDual a
      (linearWord (fun r ↦ Matrix.mulVecLin (M r)) (x i ++ y j) u)
  let f : ℕ → ℕ → ℝ := fun i j ↦ nonzeroIndicator (coefficient i j)
  refine zero_one_double_limit_of_no_staircases f
      (fun i j ↦ nonzeroIndicator_zero_one (coefficient i j)) ?_ ?_
      rowLimit columnLimit rowOuter columnOuter ?_ ?_ hrowOuter hcolumnOuter
  · intro xIndex yIndex hzero hdiag
    apply commRing_matrixWords_no_upper_evaluation_staircase M u a
      (fun i ↦ x (xIndex i)) (fun j ↦ y (yIndex j))
    · intro i j hij
      exact (nonzeroIndicator_eq_zero_iff _).mp (hzero i j hij)
    · intro i hi
      exact hdiag i ((nonzeroIndicator_eq_zero_iff _).mpr hi)
  · intro xIndex yIndex hzero hdiag
    apply commRing_matrixWords_no_lower_evaluation_staircase M u a
      (fun i ↦ x (xIndex i)) (fun j ↦ y (yIndex j))
    · intro i j hij
      exact (nonzeroIndicator_eq_zero_iff _).mp (hzero i j hij)
    · intro i hi
      exact hdiag i ((nonzeroIndicator_eq_zero_iff _).mpr hi)
  · simpa [f, coefficient] using hrow
  · simpa [f, coefficient] using hcolumn

end IndependentZeroBlocks
