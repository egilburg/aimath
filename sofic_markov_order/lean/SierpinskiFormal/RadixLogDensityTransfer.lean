import SierpinskiFormal.LogDensityNormalization
import SierpinskiFormal.CesaroSqueeze
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

set_option autoImplicit false

/-!
# Conditional fixed-context transfer to logarithmic density

This module isolates the arithmetic part of the fixed-context shell argument.
Its final result assumes existence of every fixed-context Cesàro mean; it does
not assert that analytic input unconditionally.
-/

namespace IndependentZeroBlocks

open Filter
open scoped Topology BigOperators

/-- Cesàro mean of a real sequence. -/
noncomputable def realCesaroMean (f : ℕ → ℝ) (N : ℕ) : ℝ :=
  (∑ n ∈ Finset.range N, f n) / (N : ℝ)

/-- Supported proportion in the fixed context block
`[q b^r, (q+1)b^r)`. -/
noncomputable def radixContextProportion
    (S : ℕ → Prop) (b q r : ℕ) : ℝ :=
  (intervalPredicateCount S (q * b ^ r) (b ^ r) : ℝ) / (b ^ r : ℕ)

/-- Supported proportion in a block `[qL,(q+1)L)`. -/
noncomputable def contextBlockProportion
    (S : ℕ → Prop) (q L : ℕ) : ℝ :=
  (intervalPredicateCount S (q * L) L : ℝ) / (L : ℝ)

/-- Standard harmonic mass of the `m`th radix shell. -/
noncomputable def predicateRadixShellMass
    (S : ℕ → Prop) (b m : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico (b ^ m) (b ^ (m + 1)), predicateIndicator S n / (n : ℝ)

/-- Average harmonic mass of the first `M` radix shells. -/
noncomputable def predicateRadixShellCesaro
    (S : ℕ → Prop) (b M : ℕ) : ℝ :=
  realCesaroMean (predicateRadixShellMass S b) M

/-- Cesàro average after discarding the first `k` radix shells. -/
noncomputable def shiftedRadixShellCesaro
    (S : ℕ → Prop) (b k N : ℕ) : ℝ :=
  realCesaroMean (fun r => predicateRadixShellMass S b (k + r)) N

/-- Explicit analytic hypothesis used by the fixed-context transfer: every
fixed context has a convergent Cesàro mean as its low-word length grows. -/
def HasAllFixedContextCesaroMeans
    (S : ℕ → Prop) (b : ℕ) : Prop :=
  ∀ q : ℕ, 1 ≤ q → ∃ a : ℝ,
    Tendsto (realCesaroMean (radixContextProportion S b q)) atTop (𝓝 a)

/-- Lower fixed-context bracket for the shell with low-word length `r`. -/
noncomputable def radixShellLowerBracket
    (S : ℕ → Prop) (b k r : ℕ) : ℝ :=
  ∑ q ∈ Finset.Ico (b ^ k) (b ^ (k + 1)),
    radixContextProportion S b q r / (q + 1 : ℕ)

/-- Upper fixed-context bracket for the shell with low-word length `r`. -/
noncomputable def radixShellUpperBracket
    (S : ℕ → Prop) (b k r : ℕ) : ℝ :=
  ∑ q ∈ Finset.Ico (b ^ k) (b ^ (k + 1)),
    radixContextProportion S b q r / (q : ℕ)

/-- A finite interval splits into consecutive blocks of a fixed length. -/
theorem sum_Ico_mul_eq_sum_blocks
    {α : Type*} [AddCommMonoid α] (f : ℕ → α) (a z L : ℕ) (haz : a ≤ z) :
    ∑ n ∈ Finset.Ico (a * L) (z * L), f n =
      ∑ q ∈ Finset.Ico a z, ∑ t ∈ Finset.range L, f (q * L + t) := by
  induction z, haz using Nat.le_induction with
  | base => simp
  | succ z haz ih =>
      rw [Finset.sum_Ico_succ_top haz]
      rw [← ih]
      have hsplit := Finset.sum_Ico_consecutive f
        (Nat.mul_le_mul_right L haz)
        (Nat.mul_le_mul_right L (Nat.le_succ z))
      rw [Nat.succ_mul] at hsplit
      rw [Nat.succ_mul]
      calc
        _ = (∑ n ∈ Finset.Ico (a * L) (z * L), f n) +
            ∑ n ∈ Finset.Ico (z * L) (z * L + L), f n := hsplit.symm
        _ = _ := by
          congr 1
          simpa [Nat.add_comm] using
            (Finset.sum_Ico_add f 0 L (z * L)).symm

/-- Cast of a local predicate count as a sum of indicators. -/
theorem intervalPredicateCount_cast_eq_sum_indicator
    (S : ℕ → Prop) (a L : ℕ) :
    (intervalPredicateCount S a L : ℝ) =
      ∑ t ∈ Finset.range L, predicateIndicator S (a + t) := by
  classical
  unfold intervalPredicateCount predicateIndicator
  simp

/-- Harmonic mass of one context block is bracketed by its supported
proportion divided by the two adjacent context indices. -/
theorem contextBlock_harmonic_bracket
    (S : ℕ → Prop) {q L : ℕ} (hq : 1 ≤ q) (hL : 0 < L) :
    contextBlockProportion S q L / (q + 1 : ℕ) ≤
      ∑ t ∈ Finset.range L,
        predicateIndicator S (q * L + t) / ((q * L + t : ℕ) : ℝ) ∧
    (∑ t ∈ Finset.range L,
        predicateIndicator S (q * L + t) / ((q * L + t : ℕ) : ℝ)) ≤
      contextBlockProportion S q L / q := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hqL : (0 : ℝ) < ((q * L : ℕ) : ℝ) := by positivity
  have hq1L : (0 : ℝ) < (((q + 1) * L : ℕ) : ℝ) := by positivity
  have hcount := intervalPredicateCount_cast_eq_sum_indicator S (q * L) L
  constructor
  · calc
      contextBlockProportion S q L / (q + 1 : ℕ) =
          ∑ t ∈ Finset.range L,
            predicateIndicator S (q * L + t) / (((q + 1) * L : ℕ) : ℝ) := by
        rw [contextBlockProportion, hcount]
        simp only [div_eq_mul_inv, ← Finset.sum_mul]
        field_simp
        push_cast
        ring
      _ ≤ ∑ t ∈ Finset.range L,
          predicateIndicator S (q * L + t) / ((q * L + t : ℕ) : ℝ) := by
        apply Finset.sum_le_sum
        intro t ht
        have htL : t < L := Finset.mem_range.mp ht
        have hden : q * L + t ≤ (q + 1) * L := by nlinarith
        exact div_le_div_of_nonneg_left (predicateIndicator_nonneg S (q * L + t))
          (by positivity) (by exact_mod_cast hden)
  · calc
      (∑ t ∈ Finset.range L,
          predicateIndicator S (q * L + t) / ((q * L + t : ℕ) : ℝ)) ≤
          ∑ t ∈ Finset.range L,
            predicateIndicator S (q * L + t) / ((q * L : ℕ) : ℝ) := by
        apply Finset.sum_le_sum
        intro t ht
        exact div_le_div_of_nonneg_left (predicateIndicator_nonneg S (q * L + t))
          hqL (by exact_mod_cast (Nat.le_add_right (q * L) t))
      _ = contextBlockProportion S q L / q := by
        rw [contextBlockProportion, hcount]
        simp only [div_eq_mul_inv, ← Finset.sum_mul]
        field_simp
        push_cast
        ring

theorem contextBlockProportion_nonneg (S : ℕ → Prop) (q L : ℕ) :
    0 ≤ contextBlockProportion S q L := by
  unfold contextBlockProportion
  positivity

theorem contextBlockProportion_le_one
    (S : ℕ → Prop) (q : ℕ) {L : ℕ} (hL : 0 < L) :
    contextBlockProportion S q L ≤ 1 := by
  have hc : intervalPredicateCount S (q * L) L ≤ L := by
    classical
    unfold intervalPredicateCount
    simpa using Finset.card_filter_le (Finset.range L) (fun t => S (q * L + t))
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  unfold contextBlockProportion
  apply (div_le_iff₀ hLr).2
  simpa using (show (intervalPredicateCount S (q * L) L : ℝ) ≤ L by
    exact_mod_cast hc)

/-- Fixed-context lower and upper brackets for each complete radix shell. -/
theorem predicateRadixShellMass_bracket
    (S : ℕ → Prop) (b : ℕ) (hb : 2 ≤ b) (k r : ℕ) :
    radixShellLowerBracket S b k r ≤ predicateRadixShellMass S b (k + r) ∧
      predicateRadixShellMass S b (k + r) ≤ radixShellUpperBracket S b k r := by
  have hpow : 0 < b ^ r := pow_pos (by omega) r
  have hq : 1 ≤ b ^ k := one_le_pow₀ (by omega)
  have hblocks := sum_Ico_mul_eq_sum_blocks
    (fun n => predicateIndicator S n / (n : ℝ))
    (b ^ k) (b ^ (k + 1)) (b ^ r) (Nat.pow_le_pow_right (by omega) (by omega))
  have hm : b ^ (k + r) = b ^ k * b ^ r := by rw [pow_add]
  have hm1 : b ^ (k + r + 1) = b ^ (k + 1) * b ^ r := by
    rw [show k + r + 1 = (k + 1) + r by omega, pow_add]
  rw [← hm, ← hm1] at hblocks
  unfold predicateRadixShellMass
  rw [hblocks]
  constructor
  · unfold radixShellLowerBracket
    apply Finset.sum_le_sum
    intro q hqmem
    have hq' : 1 ≤ q := hq.trans (Finset.mem_Ico.mp hqmem).1
    simpa [radixContextProportion, contextBlockProportion] using
      (contextBlock_harmonic_bracket S hq' hpow).1
  · unfold radixShellUpperBracket
    apply Finset.sum_le_sum
    intro q hqmem
    have hq' : 1 ≤ q := hq.trans (Finset.mem_Ico.mp hqmem).1
    simpa [radixContextProportion, contextBlockProportion] using
      (contextBlock_harmonic_bracket S hq' hpow).2

theorem sum_standardLogWeightDifference_Ico
    {a z : ℕ} (ha : 1 ≤ a) (haz : a ≤ z) :
    ∑ q ∈ Finset.Ico a z, standardLogWeightDifference q =
      1 / (a : ℝ) - 1 / (z : ℝ) := by
  have hsplit := Finset.sum_Ico_consecutive standardLogWeightDifference ha haz
  rw [sum_standardLogWeightDifference a ha,
    sum_standardLogWeightDifference z (ha.trans haz)] at hsplit
  linarith

/-- The pointwise bracket width is at most `b⁻ᵏ`. -/
theorem radixShellBracket_width
    (S : ℕ → Prop) (b : ℕ) (hb : 2 ≤ b) (k r : ℕ) :
    radixShellUpperBracket S b k r - radixShellLowerBracket S b k r ≤
      1 / ((b ^ k : ℕ) : ℝ) := by
  have hpowr : 0 < b ^ r := pow_pos (by omega) r
  have hpowk : 1 ≤ b ^ k := one_le_pow₀ (by omega)
  have hp (q : ℕ) : radixContextProportion S b q r ≤ 1 := by
    simpa [radixContextProportion, contextBlockProportion] using
      contextBlockProportion_le_one S q hpowr
  rw [radixShellUpperBracket, radixShellLowerBracket, ← Finset.sum_sub_distrib]
  calc
    _ = ∑ q ∈ Finset.Ico (b ^ k) (b ^ (k + 1)),
        radixContextProportion S b q r * standardLogWeightDifference q := by
      apply Finset.sum_congr rfl
      intro q hq
      unfold standardLogWeightDifference
      push_cast
      ring
    _ ≤ ∑ q ∈ Finset.Ico (b ^ k) (b ^ (k + 1)),
        standardLogWeightDifference q := by
      apply Finset.sum_le_sum
      intro q hq
      have hq1 : 1 ≤ q := hpowk.trans (Finset.mem_Ico.mp hq).1
      exact mul_le_of_le_one_left (standardLogWeightDifference_nonneg hq1) (hp q)
    _ = 1 / ((b ^ k : ℕ) : ℝ) - 1 / ((b ^ (k + 1) : ℕ) : ℝ) := by
      exact sum_standardLogWeightDifference_Ico hpowk
        (Nat.pow_le_pow_right (by omega) (by omega))
    _ ≤ 1 / ((b ^ k : ℕ) : ℝ) := by
      exact sub_le_self _ (one_div_nonneg.mpr (Nat.cast_nonneg _))

theorem realCesaroMean_finset_sum
    {ι : Type*} (s : Finset ι) (f : ι → ℕ → ℝ) (N : ℕ) :
    realCesaroMean (fun r => ∑ i ∈ s, f i r) N =
      ∑ i ∈ s, realCesaroMean (f i) N := by
  classical
  unfold realCesaroMean
  rw [Finset.sum_comm]
  simp only [div_eq_mul_inv, ← Finset.sum_mul]

theorem realCesaroMean_div_const (f : ℕ → ℝ) (c : ℝ) (N : ℕ) :
    realCesaroMean (fun r => f r / c) N = realCesaroMean f N / c := by
  unfold realCesaroMean
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  ring

theorem fixedContext_lowerBracket_cesaro_exists
    (S : ℕ → Prop) (b : ℕ) (hb : 2 ≤ b)
    (hcontext : HasAllFixedContextCesaroMeans S b) (k : ℕ) :
    ∃ l : ℝ, Tendsto (realCesaroMean (radixShellLowerBracket S b k))
      atTop (𝓝 l) := by
  classical
  choose a ha using fun q : ℕ => hcontext (q + 1) (by omega)
  have ha (q : ℕ) (hq : q ∈ Finset.Ico (b ^ k) (b ^ (k + 1))) :
      Tendsto (realCesaroMean (radixContextProportion S b q)) atTop
        (𝓝 (a (q - 1))) := by
    simpa [Nat.sub_add_cancel ((one_le_pow₀ (by omega)).trans
      (Finset.mem_Ico.mp hq).1)] using ha (q - 1)
  refine ⟨∑ q ∈ Finset.Ico (b ^ k) (b ^ (k + 1)),
    a (q - 1) / (q + 1 : ℕ), ?_⟩
  have ht := tendsto_finset_sum (Finset.Ico (b ^ k) (b ^ (k + 1)))
    (fun q hq => (ha q hq).div_const ((q + 1 : ℕ) : ℝ))
  apply ht.congr'
  filter_upwards with N
  convert! (realCesaroMean_finset_sum (Finset.Ico (b ^ k) (b ^ (k + 1)))
    (fun q r => radixContextProportion S b q r / (q + 1 : ℕ)) N).symm using 1
  apply Finset.sum_congr rfl
  intro q hq
  exact (realCesaroMean_div_const (radixContextProportion S b q) (q + 1 : ℕ) N).symm

theorem fixedContext_upperBracket_cesaro_exists
    (S : ℕ → Prop) (b : ℕ) (hb : 2 ≤ b)
    (hcontext : HasAllFixedContextCesaroMeans S b) (k : ℕ) :
    ∃ u : ℝ, Tendsto (realCesaroMean (radixShellUpperBracket S b k))
      atTop (𝓝 u) := by
  classical
  choose a ha using fun q : ℕ => hcontext (q + 1) (by omega)
  have ha (q : ℕ) (hq : q ∈ Finset.Ico (b ^ k) (b ^ (k + 1))) :
      Tendsto (realCesaroMean (radixContextProportion S b q)) atTop
        (𝓝 (a (q - 1))) := by
    simpa [Nat.sub_add_cancel ((one_le_pow₀ (by omega)).trans
      (Finset.mem_Ico.mp hq).1)] using ha (q - 1)
  refine ⟨∑ q ∈ Finset.Ico (b ^ k) (b ^ (k + 1)),
    a (q - 1) / (q : ℕ), ?_⟩
  have ht := tendsto_finset_sum (Finset.Ico (b ^ k) (b ^ (k + 1)))
    (fun q hq => (ha q hq).div_const (q : ℝ))
  apply ht.congr'
  filter_upwards with N
  convert! (realCesaroMean_finset_sum (Finset.Ico (b ^ k) (b ^ (k + 1)))
    (fun q r => radixContextProportion S b q r / (q : ℕ)) N).symm using 1
  apply Finset.sum_congr rfl
  intro q hq
  exact (realCesaroMean_div_const (radixContextProportion S b q) q N).symm

theorem predicateRadixShellMass_nonneg
    (S : ℕ → Prop) (b m : ℕ) : 0 ≤ predicateRadixShellMass S b m := by
  unfold predicateRadixShellMass
  apply Finset.sum_nonneg
  intro n hn
  exact div_nonneg (predicateIndicator_nonneg S n) (Nat.cast_nonneg n)

/-- A crude uniform bound for complete shell mass. -/
theorem predicateRadixShellMass_le_base
    (S : ℕ → Prop) (b : ℕ) (hb : 2 ≤ b) (m : ℕ) :
    predicateRadixShellMass S b m ≤ b := by
  have hpow : (0 : ℝ) < (b ^ m : ℕ) := by positivity
  unfold predicateRadixShellMass
  calc
    _ ≤ ∑ _n ∈ Finset.Ico (b ^ m) (b ^ (m + 1)),
        (1 : ℝ) / (b ^ m : ℕ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnlow : b ^ m ≤ n := (Finset.mem_Ico.mp hn).1
      exact (div_le_div_of_nonneg_left (predicateIndicator_nonneg S n)
        hpow (by exact_mod_cast hnlow)).trans
        (div_le_div_of_nonneg_right (predicateIndicator_le_one S n) hpow.le)
    _ = ((b ^ (m + 1) - b ^ m : ℕ) : ℝ) / (b ^ m : ℕ) := by
      simp
      exact (div_eq_mul_inv _ _).symm
    _ ≤ ((b ^ (m + 1) : ℕ) : ℝ) / (b ^ m : ℕ) := by
      gcongr
      exact_mod_cast Nat.sub_le _ _
    _ = b := by
      rw [pow_succ]
      push_cast
      field_simp

theorem sum_range_shellMass_le
    (S : ℕ → Prop) (b : ℕ) (hb : 2 ≤ b) (a k : ℕ) :
    ∑ r ∈ Finset.range k, predicateRadixShellMass S b (a + r) ≤ k * b := by
  calc
    _ ≤ ∑ _r ∈ Finset.range k, (b : ℝ) := by
      apply Finset.sum_le_sum
      intro r hr
      exact predicateRadixShellMass_le_base S b hb (a + r)
    _ = k * b := by simp

theorem shifted_shell_sum_sub_sum_eq
    (S : ℕ → Prop) (b k N : ℕ) :
    (∑ r ∈ Finset.range N, predicateRadixShellMass S b (k + r)) -
        ∑ r ∈ Finset.range N, predicateRadixShellMass S b r =
      (∑ r ∈ Finset.range k, predicateRadixShellMass S b (N + r)) -
        ∑ r ∈ Finset.range k, predicateRadixShellMass S b r := by
  have h1 := Finset.sum_range_add (predicateRadixShellMass S b) k N
  have h2 := Finset.sum_range_add (predicateRadixShellMass S b) N k
  rw [Nat.add_comm k N] at h1
  linarith

theorem abs_shifted_shell_sum_sub_le
    (S : ℕ → Prop) (b : ℕ) (hb : 2 ≤ b) (k N : ℕ) :
    |(∑ r ∈ Finset.range N, predicateRadixShellMass S b (k + r)) -
        ∑ r ∈ Finset.range N, predicateRadixShellMass S b r| ≤
      2 * k * b := by
  rw [shifted_shell_sum_sub_sum_eq]
  rw [abs_le]
  have htail0 : 0 ≤ ∑ r ∈ Finset.range k,
      predicateRadixShellMass S b (N + r) :=
    Finset.sum_nonneg (fun r _ => predicateRadixShellMass_nonneg S b (N + r))
  have hpref0 : 0 ≤ ∑ r ∈ Finset.range k,
      predicateRadixShellMass S b r :=
    Finset.sum_nonneg (fun r _ => predicateRadixShellMass_nonneg S b r)
  have htail := sum_range_shellMass_le S b hb N k
  have hpref := sum_range_shellMass_le S b hb 0 k
  constructor <;> norm_num at * <;> linarith

theorem abs_shiftedRadixShellCesaro_sub_le
    (S : ℕ → Prop) (b : ℕ) (hb : 2 ≤ b) (k N : ℕ) :
    |shiftedRadixShellCesaro S b k N - predicateRadixShellCesaro S b N| ≤
      (2 * k * b : ℕ) / (N : ℝ) := by
  by_cases hN : N = 0
  · subst N
    simp [shiftedRadixShellCesaro, predicateRadixShellCesaro, realCesaroMean]
  · have hNr : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
    unfold shiftedRadixShellCesaro predicateRadixShellCesaro realCesaroMean
    rw [← sub_div, abs_div, abs_of_pos hNr]
    apply div_le_div_of_nonneg_right _ hNr.le
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      (abs_shifted_shell_sum_sub_le S b hb k N)

theorem shiftedRadixShellCesaro_sub_tendsto_zero
    (S : ℕ → Prop) (b : ℕ) (hb : 2 ≤ b) (k : ℕ) :
    Tendsto (fun N => shiftedRadixShellCesaro S b k N -
      predicateRadixShellCesaro S b N) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hupper : Tendsto (fun N : ℕ => ((2 * k * b : ℕ) : ℝ) / (N : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ N : ℕ in atTop,
      ((2 * k * b : ℕ) : ℝ) / (N : ℝ) < ε :=
    hupper.eventually (Iio_mem_nhds hε)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 hevent
  refine ⟨N₀, fun N hN => ?_⟩
  rw [Real.dist_eq, sub_zero]
  exact (abs_shiftedRadixShellCesaro_sub_le S b hb k N).trans_lt (hN₀ N hN)

theorem realCesaroMean_mono {f g : ℕ → ℝ}
    (hfg : ∀ n, f n ≤ g n) (N : ℕ) :
    realCesaroMean f N ≤ realCesaroMean g N := by
  unfold realCesaroMean
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum (fun n hn => hfg n)) (Nat.cast_nonneg N)

theorem radixBracket_cesaro_bounds
    (S : ℕ → Prop) (b : ℕ) (hb : 2 ≤ b) (k N : ℕ) :
    realCesaroMean (radixShellLowerBracket S b k) N ≤
      shiftedRadixShellCesaro S b k N ∧
    shiftedRadixShellCesaro S b k N ≤
      realCesaroMean (radixShellUpperBracket S b k) N := by
  exact ⟨realCesaroMean_mono
      (fun r => (predicateRadixShellMass_bracket S b hb k r).1) N,
    realCesaroMean_mono
      (fun r => (predicateRadixShellMass_bracket S b hb k r).2) N⟩

theorem radixBracket_cesaro_gap_le
    (S : ℕ → Prop) (b : ℕ) (hb : 2 ≤ b) (k : ℕ) {N : ℕ} (hN : 0 < N) :
    realCesaroMean (radixShellUpperBracket S b k) N -
        realCesaroMean (radixShellLowerBracket S b k) N ≤
      1 / ((b ^ k : ℕ) : ℝ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  unfold realCesaroMean
  rw [← sub_div, ← Finset.sum_sub_distrib]
  apply (div_le_iff₀ hNr).2
  calc
    _ ≤ ∑ _r ∈ Finset.range N, (1 / ((b ^ k : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro r hr
      exact radixShellBracket_width S b hb k r
    _ = (1 / ((b ^ k : ℕ) : ℝ)) * N := by simp [mul_comm]

/-- The fixed-context Cesàro hypothesis forces convergence of the Cesàro
mean of complete radix-shell harmonic masses. -/
theorem fixedContext_radixShellCesaro_exists
    (S : ℕ → Prop) (b : ℕ) (hb : 2 ≤ b)
    (hcontext : HasAllFixedContextCesaroMeans S b) :
    ∃ a : ℝ, Tendsto (predicateRadixShellCesaro S b) atTop (𝓝 a) := by
  apply SierpinskiFormal.exists_tendsto_of_arbitrarily_tight_eventual_bounds
  intro ε hε
  have hpowtop : Tendsto (fun k : ℕ => ((b : ℝ) ^ k)) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast hb)
  have hwidth : Tendsto (fun k : ℕ => (1 : ℝ) / ((b : ℝ) ^ k))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hpowtop
  have hsmall : ∀ᶠ k : ℕ in atTop, (1 : ℝ) / ((b : ℝ) ^ k) < ε :=
    hwidth.eventually (Iio_mem_nhds hε)
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.1 hsmall
  obtain ⟨l, hl⟩ := fixedContext_lowerBracket_cesaro_exists S b hb hcontext k
  obtain ⟨u, hu⟩ := fixedContext_upperBracket_cesaro_exists S b hb hcontext k
  let err : ℕ → ℝ := fun N =>
    |shiftedRadixShellCesaro S b k N - predicateRadixShellCesaro S b N|
  have herr : Tendsto err atTop (𝓝 0) := by
    have hz := shiftedRadixShellCesaro_sub_tendsto_zero S b hb k
    simpa [err] using hz.abs
  let g : ℕ → ℝ := fun N => realCesaroMean (radixShellLowerBracket S b k) N - err N
  let h : ℕ → ℝ := fun N => realCesaroMean (radixShellUpperBracket S b k) N + err N
  refine ⟨g, h, l, u, ?_, ?_, ?_, ?_⟩
  · simpa [g] using hl.sub herr
  · simpa [h] using hu.add herr
  · have hgap : u - l ≤ 1 / (((b : ℝ) ^ k)) := by
      apply le_of_tendsto (hu.sub hl)
      filter_upwards [eventually_ge_atTop 1] with N hN
      simpa only [Nat.cast_pow] using
        radixBracket_cesaro_gap_le S b hb k (by omega : 0 < N)
    exact hgap.trans_lt (by simpa only [Nat.cast_pow] using hk k (le_refl k))
  · filter_upwards with N
    have hbracket := radixBracket_cesaro_bounds S b hb k N
    have habs := abs_le.mp (le_rfl :
      |shiftedRadixShellCesaro S b k N - predicateRadixShellCesaro S b N| ≤
        |shiftedRadixShellCesaro S b k N - predicateRadixShellCesaro S b N|)
    dsimp [g, h, err]
    constructor <;> linarith

/-- Standard harmonic mass below a radix endpoint is the sum of the complete
shell masses before that endpoint. -/
theorem standardLogWeight_pow_eq_sum_shells
    (S : ℕ → Prop) (b M : ℕ) (hb : 1 ≤ b) :
    predicateStandardLogWeight S (b ^ M) =
      ∑ m ∈ Finset.range M, predicateRadixShellMass S b m := by
  induction M with
  | zero => simp [predicateStandardLogWeight]
  | succ M ih =>
      rw [Finset.sum_range_succ, ← ih]
      unfold predicateStandardLogWeight predicateRadixShellMass
      rw [show M + 1 = M.succ by omega]
      exact (Finset.sum_Ico_consecutive
        (fun n => predicateIndicator S n / (n : ℝ))
        (one_le_pow₀ hb)
        (Nat.pow_le_pow_right (by omega) (Nat.le_succ M))).symm

theorem standardLogDensityRatio_pow_eq
    (S : ℕ → Prop) (b : ℕ) (hb : 2 ≤ b) {M : ℕ} (hM : 0 < M) :
    predicateStandardLogDensityRatio S (b ^ M) =
      predicateRadixShellCesaro S b M / Real.log (b : ℝ) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hlogb : Real.log (b : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hb))
  rw [predicateStandardLogDensityRatio, standardLogWeight_pow_eq_sum_shells S b M (by omega),
    predicateRadixShellCesaro, realCesaroMean]
  rw [Nat.cast_pow, Real.log_pow]
  field_simp

/-- Conditional logarithmic-density convergence along exact radix
endpoints. -/
theorem fixedContext_standardLogDensity_pow_tendsto
    (S : ℕ → Prop) (b : ℕ) (hb : 2 ≤ b)
    (hcontext : HasAllFixedContextCesaroMeans S b) :
    ∃ delta : ℝ, Tendsto
      (fun M => predicateStandardLogDensityRatio S (b ^ M))
      atTop (𝓝 delta) := by
  obtain ⟨a, ha⟩ := fixedContext_radixShellCesaro_exists S b hb hcontext
  refine ⟨a / Real.log (b : ℝ), ?_⟩
  have hdiv := ha.div_const (Real.log (b : ℝ))
  apply hdiv.congr'
  filter_upwards [eventually_ge_atTop 1] with M hM
  exact (standardLogDensityRatio_pow_eq S b hb (by omega)).symm

theorem predicateStandardLogWeight_nonneg (S : ℕ → Prop) (N : ℕ) :
    0 ≤ predicateStandardLogWeight S N := by
  unfold predicateStandardLogWeight
  apply Finset.sum_nonneg
  intro n hn
  exact div_nonneg (predicateIndicator_nonneg S n) (Nat.cast_nonneg n)

theorem predicateStandardLogWeight_mono
    (S : ℕ → Prop) {M N : ℕ} (hMN : M ≤ N) :
    predicateStandardLogWeight S M ≤ predicateStandardLogWeight S N := by
  unfold predicateStandardLogWeight
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    simp only [Finset.mem_Ico] at hn ⊢
    exact ⟨hn.1, hn.2.trans_le hMN⟩
  · intro n hnN hnM
    exact div_nonneg (predicateIndicator_nonneg S n) (Nat.cast_nonneg n)

theorem natLog_tendsto_atTop (b : ℕ) (hb : 2 ≤ b) :
    Tendsto (Nat.log b) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro k
  filter_upwards [eventually_ge_atTop (b ^ k)] with N hN
  exact Nat.le_log_of_pow_le (by omega) hN

theorem natCast_div_succ_tendsto_one :
    Tendsto (fun m : ℕ => (m : ℝ) / (m + 1 : ℕ)) atTop (𝓝 1) := by
  have hzero : Tendsto (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add
      tendsto_const_nhds)
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have heq : ∀ᶠ m : ℕ in atTop,
      1 - 1 / ((m : ℝ) + 1) = (m : ℝ) / (m + 1 : ℕ) := by
    filter_upwards with m
    push_cast
    field_simp
    ring
  simpa using (hone.sub hzero).congr' heq

theorem succ_div_natCast_tendsto_one :
    Tendsto (fun m : ℕ => ((m + 1 : ℕ) : ℝ) / (m : ℝ)) atTop (𝓝 1) := by
  have hzero : Tendsto (fun m : ℕ => (1 : ℝ) / (m : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have heq : ∀ᶠ m : ℕ in atTop,
      1 + 1 / (m : ℝ) = ((m + 1 : ℕ) : ℝ) / (m : ℝ) := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    push_cast
    field_simp
  simpa using (hone.add hzero).congr' heq

/-- Conditional fixed-context shell transfer: convergence of every fixed
context Cesàro mean implies existence of the standard logarithmic density
on all natural cutoffs. -/
theorem hasPredicateStandardLogDensity_of_allFixedContextCesaro
    (S : ℕ → Prop) (b : ℕ) (hb : 2 ≤ b)
    (hcontext : HasAllFixedContextCesaroMeans S b) :
    ∃ delta : ℝ, HasPredicateStandardLogDensity S delta := by
  obtain ⟨delta, hend⟩ := fixedContext_standardLogDensity_pow_tendsto
    S b hb hcontext
  have hlogNat := natLog_tendsto_atTop b hb
  let lower : ℕ → ℝ := fun N =>
    predicateStandardLogDensityRatio S (b ^ Nat.log b N) *
      ((Nat.log b N : ℝ) / ((Nat.log b N + 1 : ℕ) : ℝ))
  let upper : ℕ → ℝ := fun N =>
    predicateStandardLogDensityRatio S (b ^ (Nat.log b N + 1)) *
      (((Nat.log b N + 1 : ℕ) : ℝ) / (Nat.log b N : ℝ))
  have hlower : Tendsto lower atTop (𝓝 delta) := by
    have hmain := hend.comp hlogNat
    have hfactor := natCast_div_succ_tendsto_one.comp hlogNat
    simpa [lower] using hmain.mul hfactor
  have hlogSucc : Tendsto (fun N => Nat.log b N + 1) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro K
    filter_upwards [hlogNat.eventually_ge_atTop K] with N hNK
    omega
  have hupper : Tendsto upper atTop (𝓝 delta) := by
    have hmain := hend.comp hlogSucc
    have hfactor := succ_div_natCast_tendsto_one.comp hlogNat
    simpa [upper] using hmain.mul hfactor
  refine ⟨delta, tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper ?_ ?_⟩
  · filter_upwards [eventually_ge_atTop b] with N hN
    let m := Nat.log b N
    have hNpos : N ≠ 0 := by omega
    have hm : 1 ≤ m := by
      dsimp [m]
      exact Nat.le_log_of_pow_le (by omega) (by simpa using hN)
    have hpown : b ^ m ≤ N := Nat.pow_log_le_self b hNpos
    have hnext : N < b ^ (m + 1) := Nat.lt_pow_succ_log_self (by omega) N
    have hA0 := predicateStandardLogWeight_mono S hpown
    have hA0nonneg := predicateStandardLogWeight_nonneg S (b ^ m)
    have hlogb : 0 < Real.log (b : ℝ) := Real.log_pos (by exact_mod_cast hb)
    have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hlog1 : Real.log (N : ℝ) ≤ Real.log ((b ^ (m + 1) : ℕ) : ℝ) :=
      Real.strictMonoOn_log.monotoneOn (show (0 : ℝ) < N by positivity)
        (show (0 : ℝ) < (b ^ (m + 1) : ℕ) by positivity)
        (by exact_mod_cast hnext.le)
    have heq : lower N =
        predicateStandardLogWeight S (b ^ m) /
          Real.log ((b ^ (m + 1) : ℕ) : ℝ) := by
      dsimp only [lower]
      rw [show Nat.log b N = m by rfl]
      unfold predicateStandardLogDensityRatio
      rw [Nat.cast_pow, Real.log_pow, Nat.cast_pow, Real.log_pow]
      push_cast
      have hm0 : (m : ℝ) ≠ 0 := by positivity
      field_simp [hm0, ne_of_gt hlogb]
    rw [heq]
    calc
      predicateStandardLogWeight S (b ^ m) /
          Real.log ((b ^ (m + 1) : ℕ) : ℝ) ≤
          predicateStandardLogWeight S (b ^ m) / Real.log (N : ℝ) :=
        div_le_div_of_nonneg_left hA0nonneg hlogN hlog1
      _ ≤ predicateStandardLogWeight S N / Real.log (N : ℝ) :=
        div_le_div_of_nonneg_right hA0 hlogN.le
      _ = predicateStandardLogDensityRatio S N := by
        rfl
  · filter_upwards [eventually_ge_atTop b] with N hN
    let m := Nat.log b N
    have hNpos : N ≠ 0 := by omega
    have hm : 1 ≤ m := by
      dsimp [m]
      exact Nat.le_log_of_pow_le (by omega) (by simpa using hN)
    have hpown : b ^ m ≤ N := Nat.pow_log_le_self b hNpos
    have hnext : N < b ^ (m + 1) := Nat.lt_pow_succ_log_self (by omega) N
    have hA1 := predicateStandardLogWeight_mono S hnext.le
    have hA1nonneg := predicateStandardLogWeight_nonneg S (b ^ (m + 1))
    have hlogb : 0 < Real.log (b : ℝ) := Real.log_pos (by exact_mod_cast hb)
    have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hlog0 : Real.log ((b ^ m : ℕ) : ℝ) ≤ Real.log (N : ℝ) :=
      Real.strictMonoOn_log.monotoneOn
        (show (0 : ℝ) < (b ^ m : ℕ) by positivity)
        (show (0 : ℝ) < N by positivity)
        (by exact_mod_cast hpown)
    have heq : upper N =
        predicateStandardLogWeight S (b ^ (m + 1)) /
          Real.log ((b ^ m : ℕ) : ℝ) := by
      dsimp [upper, m]
      unfold predicateStandardLogDensityRatio
      rw [Nat.cast_pow, Real.log_pow, Nat.cast_pow, Real.log_pow]
      push_cast
      field_simp
    rw [heq]
    calc
      predicateStandardLogDensityRatio S N =
          predicateStandardLogWeight S N / Real.log (N : ℝ) := rfl
      _ ≤ predicateStandardLogWeight S (b ^ (m + 1)) / Real.log (N : ℝ) :=
        div_le_div_of_nonneg_right hA1 hlogN.le
      _ ≤ predicateStandardLogWeight S (b ^ (m + 1)) /
          Real.log ((b ^ m : ℕ) : ℝ) :=
        div_le_div_of_nonneg_left hA1nonneg (by
          rw [Nat.cast_pow, Real.log_pow]
          positivity) hlog0

/-- The same conditional existence theorem in the shifted-harmonic
convention. -/
theorem hasPredicateLogDensity_of_allFixedContextCesaro
    (S : ℕ → Prop) (b : ℕ) (hb : 2 ≤ b)
    (hcontext : HasAllFixedContextCesaroMeans S b) :
    ∃ delta : ℝ, HasPredicateLogDensity S delta := by
  obtain ⟨delta, hstandard⟩ :=
    hasPredicateStandardLogDensity_of_allFixedContextCesaro S b hb hcontext
  exact ⟨delta, (hasPredicateLogDensity_iff_standard S delta).mpr hstandard⟩

end IndependentZeroBlocks
