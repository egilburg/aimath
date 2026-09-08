import SierpinskiFormal.SparseIntervalDefs
import SierpinskiFormal.SeedFamilies

set_option autoImplicit false

namespace IndependentZeroBlocks

open Filter
open scoped Topology BigOperators
open SierpinskiFormal

/-- The union of the supports of a finite family has density zero when each
individual support has density zero. -/
theorem zeroPredicateDensity_family_support
    {K ι : Type*} [Semiring K] [Fintype ι]
    (T : ι → PowerSeries K)
    (hT : ∀ i, HasZeroSupportDensity (T i)) :
    HasZeroPredicateDensity
      (fun n => ∃ i, PowerSeries.coeff n (T i) ≠ 0) := by
  classical
  have hcount : ∀ N : ℕ,
      predicateCount (fun n => ∃ i, PowerSeries.coeff n (T i) ≠ 0) N ≤
        ∑ i : ι, supportCount (T i) N := by
    intro N
    have hsubset :
        (Finset.range N).filter
            (fun n => ∃ i, PowerSeries.coeff n (T i) ≠ 0) ⊆
          Finset.univ.biUnion (fun i : ι =>
            (Finset.range N).filter
              (fun n => PowerSeries.coeff n (T i) ≠ 0)) := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_range] at hn
      obtain ⟨hnN, i, hi⟩ := hn
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
        Finset.mem_filter, Finset.mem_range]
      exact ⟨i, hnN, hi⟩
    have hc := (Finset.card_le_card hsubset).trans
      (Finset.card_biUnion_le (s := Finset.univ)
        (t := fun i : ι => (Finset.range N).filter
          (fun n => PowerSeries.coeff n (T i) ≠ 0)))
    unfold predicateCount supportCount
    convert! hc using 1
    apply congrArg Finset.card
    ext n
    simp
  have hupper : Tendsto
      (fun N : ℕ => ∑ i : ι,
        (supportCount (T i) N : ℝ) / (N : ℝ)) atTop (𝓝 0) := by
    simpa using tendsto_finset_sum Finset.univ
      (fun i _ => hT i)
  apply squeeze_zero'
  · filter_upwards with N
    positivity
  · filter_upwards with N
    calc
      (predicateCount
          (fun n => ∃ i, PowerSeries.coeff n (T i) ≠ 0) N : ℝ) /
          (N : ℝ) ≤
          ((∑ i : ι, supportCount (T i) N : ℕ) : ℝ) / (N : ℝ) :=
        div_le_div_of_nonneg_right (Nat.cast_le.2 (hcount N)) (by positivity)
      _ = ∑ i : ι, (supportCount (T i) N : ℝ) / (N : ℝ) := by
        push_cast
        simp only [div_eq_mul_inv, Finset.sum_mul]
  · exact hupper

/-- A finite family with common seed blocks has arbitrarily late simultaneous
zero intervals whose lengths are a fixed positive fraction of their right
endpoints. -/
theorem proportionalIntervals_of_seed_family
    {K ι : Type*} [Semiring K] [Fintype ι]
    {q seed : ℕ} (T : ι → PowerSeries K)
    (hT : ∀ i, HasSeedBlocks q seed (T i))
    (hq : 2 ≤ q) (hseed : 1 ≤ seed) :
    HasProportionalIntervals
      (fun n => ∀ i, PowerSeries.coeff n (T i) = 0) := by
  obtain ⟨h, depth, hblocks⟩ := exists_common_seedBlock_data T hT
  refine ⟨1 / (2 * (seed + 1 : ℝ)), by positivity, ?_⟩
  intro start
  let E := start + 2 * h + depth + 1
  have hEpow : E < q ^ E := exponent_lt_base_pow q E hq
  have hEpow' : start + 2 * h + depth + 1 < q ^ E := hEpow
  have hhpow : 2 * h ≤ q ^ E := by
    omega
  have hh : h ≤ q ^ E := by omega
  have hstartpow : start ≤ q ^ E := by
    omega
  have hpowmul : q ^ E ≤ seed * q ^ E :=
    Nat.le_mul_of_pos_left _ hseed
  refine ⟨seed * q ^ E + h, q ^ E - h, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · have hright : seed * q ^ E + h + (q ^ E - h) =
        (seed + 1) * q ^ E := by
      simp only [Nat.add_mul, one_mul, Nat.add_assoc,
        Nat.add_sub_of_le hh]
    have hseedR : (0 : ℝ) < seed + 1 := by positivity
    have hhpowR : (2 : ℝ) * h ≤ q ^ E := by exact_mod_cast hhpow
    have hc :
        1 / (2 * (seed + 1 : ℝ)) *
            (((seed + 1) * q ^ E : ℕ) : ℝ) = (q ^ E : ℕ) / 2 := by
      push_cast
      field_simp
    have hlen : ((q ^ E : ℕ) : ℝ) / 2 ≤ ((q ^ E - h : ℕ) : ℝ) := by
      rw [Nat.cast_sub hh]
      push_cast
      nlinarith
    rw [hright]
    exact hc.le.trans hlen
  · intro j hj i
    have hjpow : h + j < q ^ E := by omega
    rw [Nat.add_assoc]
    exact hblocks i E (by dsimp [E]; omega) (h + j) (by omega) hjpow

end IndependentZeroBlocks
