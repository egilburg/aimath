import SierpinskiFormal.PowerIntervalDefs

set_option autoImplicit false

namespace IndependentZeroBlocks

open scoped BigOperators

/-- Counting a finite union never exceeds the sum of its individual counts. -/
theorem predicateCount_exists_le
    {ι : Type*} [Fintype ι] (bad : ι → ℕ → Prop) (N : ℕ) :
    predicateCount (fun n => ∃ i, bad i n) N ≤ ∑ i, predicateCount (bad i) N := by
  classical
  have hsubset : (Finset.range N).filter (fun n => ∃ i, bad i n) ⊆
      Finset.univ.biUnion (fun i : ι => (Finset.range N).filter (bad i)) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnN, i, hi⟩ := hn
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_filter, Finset.mem_range]
    exact ⟨i, hnN, hi⟩
  have hc := (Finset.card_le_card hsubset).trans (Finset.card_biUnion_le)
  unfold predicateCount
  convert! hc using 1
  apply congrArg Finset.card
  ext n
  simp

/-- A finite union preserves a common power exponent. Constants add and the
cutoff can be chosen uniformly over the finite family. -/
theorem HasPowerPredicateBound.finite_union
    {ι : Type*} [Fintype ι] {α : ℝ} (bad : ι → ℕ → Prop)
    (h : ∀ i, HasPowerPredicateBound α (bad i)) :
    HasPowerPredicateBound α (fun n => ∃ i, bad i n) := by
  classical
  choose C hC N₀ hN using h
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC i),
    Finset.univ.sup N₀, ?_⟩
  intro N hNN
  calc
    (predicateCount (fun n => ∃ i, bad i n) N : ℝ) ≤
        ((∑ i, predicateCount (bad i) N : ℕ) : ℝ) :=
      Nat.cast_le.mpr (predicateCount_exists_le bad N)
    _ = ∑ i, (predicateCount (bad i) N : ℝ) := by simp
    _ ≤ ∑ i, C i * (N : ℝ) ^ α := by
      apply Finset.sum_le_sum
      intro i _
      exact hN i N ((Finset.le_sup (Finset.mem_univ i)).trans hNN)
    _ = (∑ i, C i) * (N : ℝ) ^ α := (Finset.sum_mul _ _ _).symm

/-- Changing to a larger good predicate preserves all power-length intervals. -/
theorem HasPowerIntervals.mono
    {ρ : ℝ} {Z W : ℕ → Prop} (hZ : HasPowerIntervals ρ Z)
    (hZW : ∀ n, Z n → W n) : HasPowerIntervals ρ W := by
  obtain ⟨c, hc, hinterval⟩ := hZ
  refine ⟨c, hc, ?_⟩
  intro start
  obtain ⟨a, M, ha, hM, hsize, hZ⟩ := hinterval start
  exact ⟨a, M, ha, hM, hsize, fun j hj => hZW _ (hZ j hj)⟩

/-- A power bound on coefficient support is exactly a predicate count bound. -/
theorem powerPredicateBound_support_iff
    {K : Type*} [Semiring K] (F : PowerSeries K) (α : ℝ) :
    HasPowerPredicateBound α (fun n => PowerSeries.coeff n F ≠ 0) ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (supportCount F N : ℝ) ≤ C * (N : ℝ) ^ α := by
  classical
  have heq (N : ℕ) : predicateCount (fun n => PowerSeries.coeff n F ≠ 0) N =
      supportCount F N := by
    unfold predicateCount supportCount
    congr
  simp only [HasPowerPredicateBound, heq]

end IndependentZeroBlocks
