import SierpinskiFormal.UniformRelativeHoles
import SierpinskiFormal.FiniteExceptionalGaps
import SierpinskiFormal.PowerDensityBridge
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Log

set_option autoImplicit false

namespace IndependentZeroBlocks

open Filter
open scoped Topology BigOperators

/-- A local predicate count cannot exceed the length of its interval. -/
theorem intervalPredicateCount_le_length (bad : ℕ → Prop) (a L : ℕ) :
    intervalPredicateCount bad a L ≤ L := by
  classical
  unfold intervalPredicateCount
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range L)

/-- Local predicate counts split at an interval endpoint. -/
theorem intervalPredicateCount_add (bad : ℕ → Prop) (a L M : ℕ) :
    intervalPredicateCount bad a (L + M) =
      intervalPredicateCount bad a L + intervalPredicateCount bad (a + L) M := by
  classical
  simp only [intervalPredicateCount, Finset.card_filter, Finset.sum_range_add,
    Nat.add_assoc]

/-- Local predicate counts are monotone in the interval length. -/
theorem intervalPredicateCount_mono_right (bad : ℕ → Prop) (a : ℕ)
    {L M : ℕ} (hLM : L ≤ M) :
    intervalPredicateCount bad a L ≤ intervalPredicateCount bad a M := by
  obtain ⟨D, rfl⟩ := Nat.exists_eq_add_of_le hLM
  rw [intervalPredicateCount_add]
  exact Nat.le_add_right _ _

/-- Local predicate counts split into equally sized consecutive blocks. -/
theorem intervalPredicateCount_mul (bad : ℕ → Prop) (a B L : ℕ) :
    intervalPredicateCount bad a (B * L) =
      ∑ i ∈ Finset.range B, intervalPredicateCount bad (a + i * L) L := by
  induction B with
  | zero => simp [intervalPredicateCount]
  | succ B ih =>
      rw [Nat.succ_mul, intervalPredicateCount_add, ih, Finset.sum_range_succ]

/-- An interval of length at least two block widths contains a full block of
the grid based at the ambient interval's left endpoint. -/
private theorem exists_grid_block_inside
    {a n M B L : ℕ} (hL : 0 < L) (hn : a ≤ n)
    (hend : n + M ≤ a + B * L) (hM : 2 * L ≤ M) :
    ∃ i : ℕ, i < B ∧ n ≤ a + i * L ∧ a + (i + 1) * L ≤ n + M := by
  let d := n - a
  let i := d / L + 1
  have hna : a + d = n := Nat.add_sub_of_le hn
  have hdlt : d < i * L := by
    simpa [i, Nat.mul_comm] using Nat.lt_mul_div_succ d hL
  have hstart : n ≤ a + i * L := by omega
  have hiend : a + (i + 1) * L ≤ n + M := by
    have hdivmul : d / L * L ≤ d := Nat.div_mul_le_self d L
    dsimp [i]
    rw [Nat.add_mul, Nat.one_mul, Nat.add_mul, Nat.one_mul]
    omega
  have hiB : i < B := by
    by_contra hnot
    have hBi : B ≤ i := Nat.le_of_not_gt (show ¬i < B from hnot)
    have hambient : a + B * L ≤ a + i * L := by
      exact Nat.add_le_add_left (Nat.mul_le_mul_right L hBi) a
    have hstrict : a + i * L < a + (i + 1) * L := by
      simpa [Nat.add_mul] using
        Nat.add_lt_add_left hL (a + i * L)
    exact (not_lt_of_ge (hend.trans hambient)) (hstrict.trans_le hiend)
  exact ⟨i, hiB, hstart, hiend⟩

/-- A clean interval makes its local predicate count vanish. -/
private theorem intervalPredicateCount_eq_zero_of_clean
    {bad : ℕ → Prop} {a L : ℕ}
    (hclean : ∀ j : ℕ, j < L → ¬bad (a + j)) :
    intervalPredicateCount bad a L = 0 := by
  classical
  unfold intervalPredicateCount
  simp only [Finset.card_eq_zero, Finset.filter_eq_empty_iff, Finset.mem_range]
  exact fun j hj => hclean j hj

/-- Iterating one missing child in every radix block gives a uniform local
counting estimate at all radix powers. -/
private theorem intervalPredicateCount_radix_pow_le
    {bad : ℕ → Prop} {c : ℝ} {L0 : ℕ}
    (hholes : ∀ a L : ℕ, L0 ≤ L →
      ∃ n M : ℕ, a ≤ n ∧ n + M ≤ a + L ∧
        c * (L : ℝ) ≤ (M : ℝ) ∧
        ∀ j : ℕ, j < M → ¬bad (n + j))
    {B s : ℕ} (hB : 2 ≤ B) (hs : 0 < s) (hL0s : L0 ≤ s)
    (hcB : (2 : ℝ) ≤ c * (B : ℝ)) :
    ∀ e a : ℕ,
      intervalPredicateCount bad a (s * B ^ e) ≤ s * (B - 1) ^ e := by
  intro e
  induction e with
  | zero =>
      intro a
      simpa using intervalPredicateCount_le_length bad a s
  | succ e ih =>
      intro a
      let L := s * B ^ e
      have hLpos : 0 < L := by dsimp [L]; positivity
      have hL0parent : L0 ≤ B * L := by
        have hsL : s ≤ L := by
          dsimp [L]
          simpa using Nat.le_mul_of_pos_right s (pow_pos (by omega : 0 < B) e)
        exact hL0s.trans (hsL.trans (Nat.le_mul_of_pos_left L (by omega)))
      obtain ⟨n, M, hn, hend, hsize, hclean⟩ := hholes a (B * L) hL0parent
      have hM : 2 * L ≤ M := by
        have hLR : (0 : ℝ) ≤ (L : ℝ) := by positivity
        have htwo : (2 : ℝ) * (L : ℝ) ≤ c * ((B * L : ℕ) : ℝ) := by
          push_cast
          nlinarith [mul_nonneg (sub_nonneg.mpr hcB) hLR]
        exact_mod_cast htwo.trans hsize
      obtain ⟨i, hiB, hnblock, hblockend⟩ :=
        exists_grid_block_inside hLpos hn hend hM
      have hchildclean : ∀ j : ℕ, j < L → ¬bad (a + i * L + j) := by
        intro j hj
        have hnpoint : n ≤ a + i * L + j :=
          hnblock.trans (Nat.le_add_right (a + i * L) j)
        have hchildend : a + i * L + j < a + (i + 1) * L := by
          rw [Nat.add_mul, Nat.one_mul]
          omega
        have hpointend : a + i * L + j < n + M :=
          hchildend.trans_le hblockend
        have hoff : a + i * L + j - n < M := by omega
        have hrepr : n + (a + i * L + j - n) = a + i * L + j :=
          Nat.add_sub_of_le hnpoint
        have ht := hclean _ hoff
        rw [hrepr] at ht
        exact ht
      have hzero : intervalPredicateCount bad (a + i * L) L = 0 :=
        intervalPredicateCount_eq_zero_of_clean hchildclean
      have hiMem : i ∈ Finset.range B := Finset.mem_range.mpr hiB
      have hparent : s * B ^ (e + 1) = B * L := by
        dsimp [L]
        rw [pow_succ]
        ring
      rw [hparent, intervalPredicateCount_mul]
      rw [← Finset.sum_erase_add _ _ hiMem, hzero, add_zero]
      calc
        (∑ x ∈ (Finset.range B).erase i,
            intervalPredicateCount bad (a + x * L) L) ≤
            ∑ _x ∈ (Finset.range B).erase i, s * (B - 1) ^ e := by
          apply Finset.sum_le_sum
          intro x _hx
          simpa [L] using ih (a + x * L)
        _ = (B - 1) * (s * (B - 1) ^ e) := by
          simp [Finset.card_erase_of_mem hiMem]
        _ = s * (B - 1) ^ (e + 1) := by
          rw [pow_succ]
          ring

/-- Uniform relative holes force a uniform translated-interval power bound,
with an exponent in `[0,1)`.  This is stronger than a prefix counting bound. -/
theorem HasUniformRelativeHoles.exists_uniform_interval_power_bound
    {bad : ℕ → Prop} (hbad : HasUniformRelativeHoles bad) :
    ∃ α : ℝ, 0 ≤ α ∧ α < 1 ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ a N : ℕ, 1 ≤ N →
        (intervalPredicateCount bad a N : ℝ) ≤ C * (N : ℝ) ^ α := by
  obtain ⟨c, hc, L0, hholes⟩ := hbad
  obtain ⟨B, hBlarge⟩ :
      ∃ B : ℕ, max (2 : ℝ) (2 / c) < (B : ℝ) := exists_nat_gt _
  have hB : 2 ≤ B := by
    exact_mod_cast (show (2 : ℝ) ≤ (B : ℝ) from
      (le_max_left (2 : ℝ) (2 / c)).trans hBlarge.le)
  have hBpos : (0 : ℝ) < (B : ℝ) := by positivity
  have hlogB : 0 < Real.log (B : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < B by omega))
  let q := B - 1
  have hq : 1 ≤ q := by dsimp [q]; omega
  have hqpos : (0 : ℝ) < (q : ℝ) := by positivity
  have hqB : q < B := by dsimp [q]; omega
  have hlogq_nonneg : 0 ≤ Real.log (q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hq)
  have hlogq_lt : Real.log (q : ℝ) < Real.log (B : ℝ) :=
    Real.strictMonoOn_log hqpos hBpos (by exact_mod_cast hqB)
  let α := Real.log (q : ℝ) / Real.log (B : ℝ)
  have hαnonneg : 0 ≤ α := div_nonneg hlogq_nonneg hlogB.le
  have hαlt : α < 1 := by
    dsimp [α]
    rw [div_lt_one hlogB]
    exact hlogq_lt
  have hcB : (2 : ℝ) ≤ c * (B : ℝ) := by
    have hdiv : 2 / c < (B : ℝ) :=
      (le_max_right (2 : ℝ) (2 / c)).trans_lt hBlarge
    simpa [mul_comm] using ((div_lt_iff₀ hc).mp hdiv).le
  let s := max L0 1
  have hs : 0 < s := by dsimp [s]; omega
  have hL0s : L0 ≤ s := le_max_left _ _
  have hradix (e a : ℕ) :
      intervalPredicateCount bad a (s * B ^ e) ≤ s * q ^ e := by
    simpa [q] using
      intervalPredicateCount_radix_pow_le hholes hB hs hL0s hcB e a
  have hrpow_identity (e : ℕ) :
      (((B ^ e : ℕ) : ℝ) ^ α) = ((q ^ e : ℕ) : ℝ) := by
    rw [show ((B ^ e : ℕ) : ℝ) = (B : ℝ) ^ e by norm_num]
    rw [Real.rpow_def_of_pos (pow_pos hBpos e)]
    rw [Real.log_pow]
    have hlogBne : Real.log (B : ℝ) ≠ 0 := ne_of_gt hlogB
    have hexp :
        Real.exp ((e : ℝ) * Real.log (B : ℝ) * α) =
          Real.exp (Real.log ((q : ℝ) ^ e)) := by
      congr 1
      rw [Real.log_pow]
      dsimp [α]
      field_simp
    rw [hexp, Real.exp_log (pow_pos hqpos e)]
    norm_num
  refine ⟨α, hαnonneg, hαlt, (s * q : ℕ), by positivity, ?_⟩
  intro a N hN
  let e := Nat.log B N
  have hNne : N ≠ 0 := by omega
  have hpowN : B ^ e ≤ N := Nat.pow_log_le_self B hNne
  have hNnext : N ≤ B ^ (e + 1) :=
    Nat.le_of_lt (Nat.lt_pow_succ_log_self (by omega) N)
  have hNscaled : N ≤ s * B ^ (e + 1) := by
    exact hNnext.trans (Nat.le_mul_of_pos_left _ hs)
  have hcountNat :
      intervalPredicateCount bad a N ≤ s * q ^ (e + 1) :=
    (intervalPredicateCount_mono_right bad a hNscaled).trans (hradix (e + 1) a)
  have hpowReal : (((B ^ e : ℕ) : ℝ) ^ α) ≤ (N : ℝ) ^ α :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hpowN) hαnonneg
  have hqpow : ((q ^ e : ℕ) : ℝ) ≤ (N : ℝ) ^ α := by
    rw [← hrpow_identity]
    exact hpowReal
  calc
    (intervalPredicateCount bad a N : ℝ) ≤ (s * q ^ (e + 1) : ℕ) :=
      Nat.cast_le.mpr hcountNat
    _ = ((s * q : ℕ) : ℝ) * ((q ^ e : ℕ) : ℝ) := by
      push_cast
      rw [pow_succ]
      ring
    _ ≤ ((s * q : ℕ) : ℝ) * (N : ℝ) ^ α :=
      mul_le_mul_of_nonneg_left hqpow (by positivity)

/-- Uniform relative holes imply a sublinear power bound for the prefix
counting function. -/
theorem HasUniformRelativeHoles.exists_powerPredicateBound
    {bad : ℕ → Prop} (hbad : HasUniformRelativeHoles bad) :
    ∃ α : ℝ, 0 ≤ α ∧ α < 1 ∧ HasPowerPredicateBound α bad := by
  obtain ⟨α, hα, hαlt, C, hC, hinterval⟩ :=
    hbad.exists_uniform_interval_power_bound
  refine ⟨α, hα, hαlt, C, hC, 1, ?_⟩
  intro N hN
  have hcount := hinterval 0 N hN
  have heq : predicateCount bad N = intervalPredicateCount bad 0 N := by
    classical
    unfold predicateCount intervalPredicateCount
    congr 1
    ext j
    simp
  simpa [heq] using hcount

/-- A predicate with uniform relative holes has ordinary natural density
zero. -/
theorem HasUniformRelativeHoles.toZeroPredicateDensity
    {bad : ℕ → Prop} (hbad : HasUniformRelativeHoles bad) :
    HasZeroPredicateDensity bad := by
  obtain ⟨α, _hα, hαlt, hpower⟩ := hbad.exists_powerPredicateBound
  exact hpower.toZeroPredicateDensity hαlt

end IndependentZeroBlocks
