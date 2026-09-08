import SierpinskiFormal.RadixLogDensityTransfer

set_option autoImplicit false

/-!
# A common fixed-context mean determines the logarithmic-density value

The arithmetic transfer in `RadixLogDensityTransfer` gives existence when
each fixed radix context has some Cesàro limit.  Here the limits are assumed
to have one common value, and the shell comparison identifies the resulting
standard logarithmic density with that value.
-/

namespace IndependentZeroBlocks

open Filter
open scoped Topology BigOperators

theorem radixContextProportion_true (b q r : ℕ) (hb : 1 ≤ b) :
    radixContextProportion (fun _ => True) b q r = 1 := by
  classical
  simp [radixContextProportion, intervalPredicateCount]
  omega

theorem realCesaroMean_nonneg {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (N : ℕ) :
    0 ≤ realCesaroMean f N := by
  unfold realCesaroMean
  exact div_nonneg (Finset.sum_nonneg (fun n _ => hf n)) (Nat.cast_nonneg N)

theorem realCesaroMean_le_one {f : ℕ → ℝ} (hf : ∀ n, f n ≤ 1)
    {N : ℕ} (hN : 0 < N) : realCesaroMean f N ≤ 1 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  unfold realCesaroMean
  apply (div_le_iff₀ hNr).2
  calc
    (∑ n ∈ Finset.range N, f n) ≤ ∑ _n ∈ Finset.range N, (1 : ℝ) := by
      exact Finset.sum_le_sum (fun n _ => hf n)
    _ = (N : ℝ) := by simp
    _ ≤ 1 * (N : ℝ) := by simp

theorem commonContextValue_mem_Icc
    (S : ℕ → Prop) (b : ℕ) (hb : 2 ≤ b) (δ : ℝ)
    (hcontext : ∀ q : ℕ, 1 ≤ q →
      Tendsto (realCesaroMean (radixContextProportion S b q)) atTop (𝓝 δ)) :
    δ ∈ Set.Icc (0 : ℝ) 1 := by
  have hq := hcontext 1 (by omega)
  constructor
  · apply ge_of_tendsto hq
    exact Filter.Eventually.of_forall (fun N =>
      realCesaroMean_nonneg
        (fun r => by
          unfold radixContextProportion
          positivity) N)
  · apply le_of_tendsto hq
    filter_upwards [eventually_ge_atTop 1] with N hN
    apply realCesaroMean_le_one
    · intro r
      simpa [radixContextProportion, contextBlockProportion] using
        contextBlockProportion_le_one S 1 (pow_pos (by omega : 0 < b) r)
    · omega

theorem commonContext_lowerBracket_tendsto
    (S : ℕ → Prop) (b : ℕ) (hb : 2 ≤ b) (δ : ℝ)
    (hcontext : ∀ q : ℕ, 1 ≤ q →
      Tendsto (realCesaroMean (radixContextProportion S b q)) atTop (𝓝 δ))
    (k : ℕ) :
    Tendsto (realCesaroMean (radixShellLowerBracket S b k)) atTop
      (𝓝 (δ * radixShellLowerBracket (fun _ => True) b k 0)) := by
  classical
  have hq (q : ℕ) (hqmem : q ∈ Finset.Ico (b ^ k) (b ^ (k + 1))) :
      Tendsto (realCesaroMean (radixContextProportion S b q)) atTop (𝓝 δ) :=
    hcontext q ((one_le_pow₀ (by omega)).trans (Finset.mem_Ico.mp hqmem).1)
  have ht := tendsto_finset_sum (Finset.Ico (b ^ k) (b ^ (k + 1)))
    (fun q hqmem => (hq q hqmem).div_const ((q + 1 : ℕ) : ℝ))
  have ht' : Tendsto (fun N => ∑ q ∈ Finset.Ico (b ^ k) (b ^ (k + 1)),
      realCesaroMean (radixContextProportion S b q) N / (q + 1 : ℕ))
      atTop (𝓝 (∑ q ∈ Finset.Ico (b ^ k) (b ^ (k + 1)),
        δ / (q + 1 : ℕ))) := ht
  have hlimit : (∑ q ∈ Finset.Ico (b ^ k) (b ^ (k + 1)),
      δ / (q + 1 : ℕ)) =
      δ * radixShellLowerBracket (fun _ => True) b k 0 := by
    unfold radixShellLowerBracket
    simp_rw [radixContextProportion_true b _ 0 (by omega)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hqmem
    push_cast
    ring
  rw [← hlimit]
  apply ht'.congr'
  filter_upwards with N
  convert! (realCesaroMean_finset_sum (Finset.Ico (b ^ k) (b ^ (k + 1)))
    (fun q r => radixContextProportion S b q r / (q + 1 : ℕ)) N).symm using 1
  apply Finset.sum_congr rfl
  intro q hq
  exact (realCesaroMean_div_const (radixContextProportion S b q) (q + 1 : ℕ) N).symm

theorem commonContext_upperBracket_tendsto
    (S : ℕ → Prop) (b : ℕ) (hb : 2 ≤ b) (δ : ℝ)
    (hcontext : ∀ q : ℕ, 1 ≤ q →
      Tendsto (realCesaroMean (radixContextProportion S b q)) atTop (𝓝 δ))
    (k : ℕ) :
    Tendsto (realCesaroMean (radixShellUpperBracket S b k)) atTop
      (𝓝 (δ * radixShellUpperBracket (fun _ => True) b k 0)) := by
  classical
  have hq (q : ℕ) (hqmem : q ∈ Finset.Ico (b ^ k) (b ^ (k + 1))) :
      Tendsto (realCesaroMean (radixContextProportion S b q)) atTop (𝓝 δ) :=
    hcontext q ((one_le_pow₀ (by omega)).trans (Finset.mem_Ico.mp hqmem).1)
  have ht := tendsto_finset_sum (Finset.Ico (b ^ k) (b ^ (k + 1)))
    (fun q hqmem => (hq q hqmem).div_const (q : ℝ))
  have ht' : Tendsto (fun N => ∑ q ∈ Finset.Ico (b ^ k) (b ^ (k + 1)),
      realCesaroMean (radixContextProportion S b q) N / (q : ℝ))
      atTop (𝓝 (∑ q ∈ Finset.Ico (b ^ k) (b ^ (k + 1)),
        δ / (q : ℝ))) := ht
  have hlimit : (∑ q ∈ Finset.Ico (b ^ k) (b ^ (k + 1)),
      δ / (q : ℝ)) =
      δ * radixShellUpperBracket (fun _ => True) b k 0 := by
    unfold radixShellUpperBracket
    simp_rw [radixContextProportion_true b _ 0 (by omega)]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hqmem
    ring
  rw [← hlimit]
  apply ht'.congr'
  filter_upwards with N
  convert! (realCesaroMean_finset_sum (Finset.Ico (b ^ k) (b ^ (k + 1)))
    (fun q r => radixContextProportion S b q r / (q : ℕ)) N).symm using 1
  apply Finset.sum_congr rfl
  intro q hq
  exact (realCesaroMean_div_const (radixContextProportion S b q) q N).symm

theorem realCesaroMean_one_eq_one {N : ℕ} (hN : 0 < N) :
    realCesaroMean (fun _ : ℕ => (1 : ℝ)) N = 1 := by
  unfold realCesaroMean
  simp
  exact Nat.ne_of_gt hN

theorem true_fixedContext_tendsto_one (b : ℕ) (hb : 2 ≤ b) (q : ℕ) :
    Tendsto (realCesaroMean
      (radixContextProportion (fun _ => True) b q)) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [show realCesaroMean (radixContextProportion (fun _ => True) b q) N =
      realCesaroMean (fun _ : ℕ => (1 : ℝ)) N by
    congr 1
    funext r
    exact radixContextProportion_true b q r (by omega)]
  exact (realCesaroMean_one_eq_one (Nat.zero_lt_of_lt hN)).symm

theorem true_hasPredicateLogDensity_one :
    HasPredicateLogDensity (fun _ => True) 1 := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hnorm := logarithmicNormalizer_pos (by omega : 0 < N)
  have hw : predicateLogWeight (fun _ => True) N = logarithmicNormalizer N := by
    classical
    unfold predicateLogWeight logarithmicNormalizer predicateIndicator
    simp
  rw [predicateLogDensityRatio, hw]
  exact (div_self hnorm.ne').symm

theorem true_radixShellCesaro_tendsto_log
    (b : ℕ) (hb : 2 ≤ b) :
    Tendsto (predicateRadixShellCesaro (fun _ => True) b) atTop
      (𝓝 (Real.log (b : ℝ))) := by
  have hstandard : HasPredicateStandardLogDensity (fun _ => True) 1 :=
    (hasPredicateLogDensity_iff_standard (fun _ => True) 1).mp
      true_hasPredicateLogDensity_one
  have hpowtop : Tendsto (fun M : ℕ => b ^ M) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by omega : 1 < b)
  have hend := hstandard.comp hpowtop
  have hdiv : Tendsto
      (fun M => predicateRadixShellCesaro (fun _ => True) b M /
        Real.log (b : ℝ)) atTop (𝓝 1) := by
    apply hend.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with M hM
    simpa only [Function.comp_apply] using
      standardLogDensityRatio_pow_eq (fun _ => True) b hb
        (Nat.zero_lt_of_lt hM)
  have hmul := hdiv.mul_const (Real.log (b : ℝ))
  have hlog : Real.log (b : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hb))
  have heq : ∀ᶠ M : ℕ in atTop,
      predicateRadixShellCesaro (fun _ => True) b M /
          Real.log (b : ℝ) * Real.log (b : ℝ) =
        predicateRadixShellCesaro (fun _ => True) b M :=
    Filter.Eventually.of_forall (fun M => div_mul_cancel₀ _ hlog)
  simpa only [one_mul] using hmul.congr' heq

theorem shiftedRadixShellCesaro_tendsto_of_tendsto
    (S : ℕ → Prop) (b : ℕ) (hb : 2 ≤ b) (k : ℕ) {a : ℝ}
    (ha : Tendsto (predicateRadixShellCesaro S b) atTop (𝓝 a)) :
    Tendsto (shiftedRadixShellCesaro S b k) atTop (𝓝 a) := by
  have hz := shiftedRadixShellCesaro_sub_tendsto_zero S b hb k
  have hadd := ha.add hz
  have heq : ∀ᶠ N : ℕ in atTop,
      predicateRadixShellCesaro S b N +
          (shiftedRadixShellCesaro S b k N - predicateRadixShellCesaro S b N) =
        shiftedRadixShellCesaro S b k N := by
    filter_upwards with N
    ring
  simpa only [add_zero] using hadd.congr' heq

/-- If every positive fixed radix context has the same Cesàro limit `δ`, then
the standard logarithmic density exists and equals exactly `δ`. -/
theorem hasPredicateStandardLogDensity_of_commonFixedContextCesaro
    (S : ℕ → Prop) (b : ℕ) (hb : 2 ≤ b) (δ : ℝ)
    (hcontext : ∀ q : ℕ, 1 ≤ q →
      Tendsto (realCesaroMean (radixContextProportion S b q)) atTop (𝓝 δ)) :
    HasPredicateStandardLogDensity S δ := by
  have hall : HasAllFixedContextCesaroMeans S b := fun q hq =>
    ⟨δ, hcontext q hq⟩
  obtain ⟨D, hD⟩ := hasPredicateStandardLogDensity_of_allFixedContextCesaro
    S b hb hall
  obtain ⟨a, ha⟩ := fixedContext_radixShellCesaro_exists S b hb hall
  have hδ := commonContextValue_mem_Icc S b hb δ hcontext
  have hwidth : Tendsto (fun k : ℕ => (1 : ℝ) / ((b : ℝ) ^ k))
      atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast hb))
  have haeq : a = δ * Real.log (b : ℝ) := by
    have habs (k : ℕ) : |a - δ * Real.log (b : ℝ)| ≤
        1 / ((b : ℝ) ^ k) := by
      let L := radixShellLowerBracket (fun _ => True) b k 0
      let U := radixShellUpperBracket (fun _ => True) b k 0
      have hshiftS := shiftedRadixShellCesaro_tendsto_of_tendsto S b hb k ha
      have hlS := commonContext_lowerBracket_tendsto S b hb δ hcontext k
      have huS := commonContext_upperBracket_tendsto S b hb δ hcontext k
      have hLa : δ * L ≤ a := by
        have hh := ge_of_tendsto (hshiftS.sub hlS) (by
          filter_upwards with N
          exact sub_nonneg.mpr (radixBracket_cesaro_bounds S b hb k N).1)
        change 0 ≤ a - δ * L at hh
        exact sub_nonneg.mp hh
      have haU : a ≤ δ * U := by
        have hh := ge_of_tendsto (huS.sub hshiftS) (by
          filter_upwards with N
          exact sub_nonneg.mpr (radixBracket_cesaro_bounds S b hb k N).2)
        change 0 ≤ δ * U - a at hh
        exact sub_nonneg.mp hh
      have htrue := true_radixShellCesaro_tendsto_log b hb
      have hshiftTrue := shiftedRadixShellCesaro_tendsto_of_tendsto
        (fun _ => True) b hb k htrue
      have hlTrue := commonContext_lowerBracket_tendsto (fun _ => True) b hb 1
        (fun q _ => true_fixedContext_tendsto_one b hb q) k
      have huTrue := commonContext_upperBracket_tendsto (fun _ => True) b hb 1
        (fun q _ => true_fixedContext_tendsto_one b hb q) k
      have hLlog : L ≤ Real.log (b : ℝ) := by
        have hh := ge_of_tendsto (hshiftTrue.sub hlTrue) (by
          filter_upwards with N
          exact sub_nonneg.mpr
            (radixBracket_cesaro_bounds (fun _ => True) b hb k N).1)
        have hh' : 0 ≤ Real.log (b : ℝ) - L := by
          simpa only [one_mul] using hh
        exact sub_nonneg.mp hh'
      have hlogU : Real.log (b : ℝ) ≤ U := by
        have hh := ge_of_tendsto (huTrue.sub hshiftTrue) (by
          filter_upwards with N
          exact sub_nonneg.mpr
            (radixBracket_cesaro_bounds (fun _ => True) b hb k N).2)
        have hh' : 0 ≤ U - Real.log (b : ℝ) := by
          simpa only [one_mul] using hh
        exact sub_nonneg.mp hh'
      have hgap : U - L ≤ 1 / (((b ^ k : ℕ) : ℝ)) := by
        simpa [L, U] using radixShellBracket_width (fun _ => True) b hb k 0
      rw [abs_le]
      constructor
      · have hgap0 : 0 ≤ U - L := by linarith
        have hmul : δ * (U - L) ≤ U - L := by
          simpa using mul_le_mul_of_nonneg_right hδ.2 hgap0
        have hcast : (((b ^ k : ℕ) : ℝ)) = (b : ℝ) ^ k := by norm_num
        rw [hcast] at hgap
        have hδlogU : δ * Real.log (b : ℝ) ≤ δ * U :=
          mul_le_mul_of_nonneg_left hlogU hδ.1
        calc
          -(1 / (b : ℝ) ^ k) ≤ -(U - L) := neg_le_neg hgap
          _ ≤ -(δ * (U - L)) := neg_le_neg hmul
          _ = δ * L - δ * U := by ring
          _ ≤ a - δ * Real.log (b : ℝ) := sub_le_sub hLa hδlogU
      · have hgap0 : 0 ≤ U - L := by linarith
        have hmul : δ * (U - L) ≤ U - L := by
          simpa using mul_le_mul_of_nonneg_right hδ.2 hgap0
        have hcast : (((b ^ k : ℕ) : ℝ)) = (b : ℝ) ^ k := by norm_num
        rw [hcast] at hgap
        have hδLlog : δ * L ≤ δ * Real.log (b : ℝ) :=
          mul_le_mul_of_nonneg_left hLlog hδ.1
        calc
          a - δ * Real.log (b : ℝ) ≤ δ * U - δ * L :=
            sub_le_sub haU hδLlog
          _ = δ * (U - L) := by ring
          _ ≤ U - L := hmul
          _ ≤ 1 / (b : ℝ) ^ k := hgap
    have habs0 : |a - δ * Real.log (b : ℝ)| ≤ 0 :=
      ge_of_tendsto hwidth (Filter.Eventually.of_forall habs)
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm habs0 (abs_nonneg _)))
  have hpowtop : Tendsto (fun M : ℕ => b ^ M) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by omega : 1 < b)
  have hendpoint := hD.comp hpowtop
  have hdiv : Tendsto
      (fun M => predicateRadixShellCesaro S b M / Real.log (b : ℝ))
      atTop (𝓝 D) := by
    apply hendpoint.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with M hM
    simpa only [Function.comp_apply] using
      standardLogDensityRatio_pow_eq S b hb (Nat.zero_lt_of_lt hM)
  have hlog : Real.log (b : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hb))
  have haD : Tendsto (predicateRadixShellCesaro S b) atTop
      (𝓝 (D * Real.log (b : ℝ))) := by
    have hmul := hdiv.mul_const (Real.log (b : ℝ))
    apply hmul.congr'
    exact Filter.Eventually.of_forall (fun M => div_mul_cancel₀ _ hlog)
  have : D = δ := by
    have heq := tendsto_nhds_unique ha haD
    rw [haeq] at heq
    apply (mul_right_cancel₀ hlog)
    simpa [mul_comm] using heq.symm
  simpa [this] using hD

end IndependentZeroBlocks
