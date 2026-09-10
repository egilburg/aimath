import SierpinskiFormal.RadixLogDensityTransfer
import Mathlib.Analysis.Normed.Ring.InfiniteSum

set_option autoImplicit false

/-!
# Cesàro-to-Abel transfer for bounded real sequences

This is the scalar summability bridge used after a discounted group-state
calculation.  It is independent of the operator-valued Abel construction.
-/

noncomputable section

open Filter Set
open scoped Topology BigOperators

namespace IndependentZeroBlocks

/-- The normalized Abel mean of a real sequence. -/
def realNormalizedAbelMean (c : ℕ → ℝ) (s : ℝ) : ℝ :=
  (1 - s) * ∑' n : ℕ, s ^ n * c n

/-- The order-two Abel kernel which averages the positive-index Cesàro
means. -/
def cesaroAbelKernel (s : ℝ) (n : ℕ) : ℝ :=
  (n + 1 : ℕ) * (1 - s) ^ 2 * s ^ n

theorem cesaroAbelKernel_nonneg {s : ℝ} (hs0 : 0 ≤ s) (n : ℕ) :
    0 ≤ cesaroAbelKernel s n := by
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
    (pow_nonneg hs0 _)

theorem hasSum_cesaroAbelKernel {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    HasSum (cesaroAbelKernel s) 1 := by
  have habs : ‖s‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hs0]
    exact hs1
  have h :=
    (hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1 habs).mul_left
      ((1 - s) ^ 2)
  convert! h using 1
  · funext n
    simp [cesaroAbelKernel, mul_assoc, mul_left_comm, mul_comm]
  · field_simp [ne_of_gt (sub_pos.mpr hs1)]

theorem summable_cesaroAbelKernel {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    Summable (cesaroAbelKernel s) :=
  (hasSum_cesaroAbelKernel hs0 hs1).summable

theorem tsum_cesaroAbelKernel {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    ∑' n : ℕ, cesaroAbelKernel s n = 1 :=
  (hasSum_cesaroAbelKernel hs0 hs1).tsum_eq

/-- The order-two Abel kernels form a regular summation method on bounded
convergent real sequences.  The explicit bound keeps this lemma useful
without invoking a separate boundedness extraction API. -/
theorem tendsto_cesaroAbelKernel_sum
    (b : ℕ → ℝ) (L B : ℝ) (hB : ∀ n, |b n - L| ≤ B)
    (hb : Tendsto b atTop (𝓝 L)) :
    Tendsto (fun s : ℝ => ∑' n : ℕ, cesaroAbelKernel s n * b n)
      (𝓝[<] (1 : ℝ)) (𝓝 L) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hb) (ε / 2) (half_pos hε)
  let C : ℝ := ∑ n ∈ Finset.range N, (n + 1 : ℕ) * |b n - L|
  have hC0 : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨min 1 (ε / (2 * (C + 1))), ?_, ?_⟩
  · positivity
  intro s hs1 hdist
  have hdist' : |s - 1| < min 1 (ε / (2 * (C + 1))) := by
    simpa [Real.dist_eq] using hdist
  have hspos : 0 < s := by
    have : |s - 1| < 1 := lt_of_lt_of_le hdist' (min_le_left _ _)
    rw [abs_of_nonpos (sub_nonpos.mpr hs1.le)] at this
    linarith
  have hs0 : 0 ≤ s := hspos.le
  have hsub : 0 < 1 - s := sub_pos.mpr hs1
  have hsub_lt : 1 - s < ε / (2 * (C + 1)) := by
    have := lt_of_lt_of_le hdist' (min_le_right _ _)
    rw [abs_of_nonpos (sub_nonpos.mpr hs1.le)] at this
    linarith
  have hker0 : ∀ n, 0 ≤ cesaroAbelKernel s n :=
    cesaroAbelKernel_nonneg hs0
  have hksum := summable_cesaroAbelKernel hs0 hs1
  have hmain : Summable (fun n : ℕ => cesaroAbelKernel s n * (b n - L)) := by
    have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
    refine Summable.of_norm_bounded (hksum.mul_left B) ?_
    intro n
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hker0 n),
      abs_of_nonneg hB0]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left (hB n) (hker0 n)
  have hkb : Summable (fun n : ℕ => cesaroAbelKernel s n * b n) := by
    convert hmain.add (hksum.mul_right L) using 1
    funext n
    ring
  have hrewrite :
      (∑' n : ℕ, cesaroAbelKernel s n * b n) - L =
        ∑' n : ℕ, cesaroAbelKernel s n * (b n - L) := by
    calc
      _ = (∑' n : ℕ, cesaroAbelKernel s n * b n) -
          ∑' n : ℕ, cesaroAbelKernel s n * L := by
            rw [tsum_mul_right, tsum_cesaroAbelKernel hs0 hs1, one_mul]
      _ = ∑' n : ℕ,
          (cesaroAbelKernel s n * b n - cesaroAbelKernel s n * L) := by
            rw [hkb.tsum_sub (hksum.mul_right L)]
      _ = _ := by
        apply tsum_congr
        intro n
        ring
  rw [Real.dist_eq, hrewrite]
  let head : ℕ → ℝ := fun n =>
    if n < N then (1 - s) ^ 2 * ((n + 1 : ℕ) * |b n - L|) else 0
  have hhead : Summable head := by
    apply summable_of_ne_finset_zero (s := Finset.range N)
    intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    simp [head, hn]
  let majorant : ℕ → ℝ := fun n => head n + (ε / 2) * cesaroAbelKernel s n
  have hmajorant : Summable majorant := hhead.add (hksum.mul_left (ε / 2))
  have hpoint : ∀ n,
      ‖cesaroAbelKernel s n * (b n - L)‖ ≤ majorant n := by
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hker0 n)]
    by_cases hn : n < N
    · have hpow : s ^ n ≤ 1 := pow_le_one₀ hs0 hs1.le
      have hle : cesaroAbelKernel s n * |b n - L| ≤ head n := by
        rw [show head n = (1 - s) ^ 2 * ((n + 1 : ℕ) * |b n - L|) by simp [head, hn]]
        rw [cesaroAbelKernel]
        calc
          (n + 1 : ℕ) * (1 - s) ^ 2 * s ^ n * |b n - L|
              ≤ (n + 1 : ℕ) * (1 - s) ^ 2 * 1 * |b n - L| := by
                gcongr
          _ = (1 - s) ^ 2 * ((n + 1 : ℕ) * |b n - L|) := by ring
      have hextra : 0 ≤ (ε / 2) * cesaroAbelKernel s n :=
        mul_nonneg (half_pos hε).le (hker0 n)
      exact hle.trans (le_add_of_nonneg_right hextra)
    · have hnN : N ≤ n := Nat.le_of_not_gt hn
      have htail : |b n - L| < ε / 2 := by
        simpa [Real.dist_eq] using hN n hnN
      have hle : cesaroAbelKernel s n * |b n - L| ≤
          (ε / 2) * cesaroAbelKernel s n := by
        nlinarith [hker0 n]
      simpa [majorant, head, hn] using hle
  have hnormsum : Summable (fun n : ℕ =>
      ‖cesaroAbelKernel s n * (b n - L)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpoint hmajorant
  calc
    |∑' n : ℕ, cesaroAbelKernel s n * (b n - L)|
        = ‖∑' n : ℕ, cesaroAbelKernel s n * (b n - L)‖ := by
            rw [Real.norm_eq_abs]
    _ ≤ ∑' n : ℕ, ‖cesaroAbelKernel s n * (b n - L)‖ :=
      norm_tsum_le_tsum_norm hnormsum
    _ ≤ ∑' n : ℕ, majorant n :=
      hnormsum.tsum_le_tsum hpoint hmajorant
    _ = (1 - s) ^ 2 * C + ε / 2 := by
      dsimp only [majorant]
      rw [hhead.tsum_add (hksum.mul_left (ε / 2)), tsum_mul_left,
        tsum_cesaroAbelKernel hs0 hs1, mul_one]
      rw [tsum_eq_sum (s := Finset.range N)]
      · dsimp only [head, C]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        rw [if_pos (Finset.mem_range.mp hn)]
      · intro n hn
        simp only [Finset.mem_range, not_lt] at hn
        simp [head, hn]
    _ < ε := by
      have hsub_le_one : 1 - s ≤ 1 := by linarith
      have hden : 0 < 2 * (C + 1) := by positivity
      have hprod : (1 - s) * (2 * (C + 1)) < ε :=
        (lt_div_iff₀ hden).mp hsub_lt
      have hhead_lt : (1 - s) ^ 2 * C < ε / 2 := by
        nlinarith [mul_nonneg hsub.le hC0,
          mul_le_mul_of_nonneg_right hsub_le_one (mul_nonneg hsub.le hC0)]
      linarith

/-- Cauchy's product formula identifies the normalized Abel mean with the
order-two Abel average of the positive-index Cesàro means. -/
theorem realNormalizedAbelMean_eq_kernel_cesaro
    (c : ℕ → ℝ) (C s : ℝ) (hC : ∀ n, |c n| ≤ C)
    (hs0 : 0 ≤ s) (hs1 : s < 1) :
    realNormalizedAbelMean c s =
      ∑' n : ℕ, cesaroAbelKernel s n * realCesaroMean c (n + 1) := by
  have habs : |s| < 1 := by simpa [abs_of_nonneg hs0] using hs1
  have hgeom : Summable (fun n : ℕ => |s| ^ n) := by
    exact summable_geometric_of_norm_lt_one
      (x := (|s| : ℝ)) (by simpa [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg s)] using habs)
  have hgNorm : Summable (fun n : ℕ => ‖s ^ n‖) := by
    simpa [Real.norm_eq_abs, abs_pow] using hgeom
  have hfNorm : Summable (fun n : ℕ => ‖s ^ n * c n‖) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ?_ (hgeom.mul_left C)
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_left (hC n) (pow_nonneg (abs_nonneg s) n)
  have hcauchy :=
    tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hfNorm hgNorm
  have hinner : ∀ n : ℕ,
      (∑ k ∈ Finset.range (n + 1), (s ^ k * c k) * s ^ (n - k)) =
        s ^ n * ∑ k ∈ Finset.range (n + 1), c k := by
    intro n
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    calc
      (s ^ k * c k) * s ^ (n - k) = c k * (s ^ k * s ^ (n - k)) := by ring
      _ = c k * s ^ n := by rw [← pow_add, Nat.add_sub_of_le hkn]
      _ = s ^ n * c k := by ring
  have hcauchy' :
      (∑' n : ℕ, s ^ n * c n) * (1 - s)⁻¹ =
        ∑' n : ℕ, s ^ n * ∑ k ∈ Finset.range (n + 1), c k := by
    rw [← tsum_geometric_of_norm_lt_one (show ‖s‖ < 1 by simpa [Real.norm_eq_abs] using habs)]
    rw [hcauchy]
    apply tsum_congr
    exact hinner
  rw [realNormalizedAbelMean]
  rw [show (∑' n : ℕ, cesaroAbelKernel s n * realCesaroMean c (n + 1)) =
      (1 - s) ^ 2 *
        ∑' n : ℕ, s ^ n * ∑ k ∈ Finset.range (n + 1), c k by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [cesaroAbelKernel, realCesaroMean]
    have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp]
  rw [← hcauchy']
  have hne : 1 - s ≠ 0 := ne_of_gt (sub_pos.mpr hs1)
  field_simp

theorem abs_realCesaroMean_succ_le
    (c : ℕ → ℝ) (C : ℝ) (hC : ∀ n, |c n| ≤ C) (n : ℕ) :
    |realCesaroMean c (n + 1)| ≤ C := by
  rw [realCesaroMean, abs_div]
  have hdenabs : |(((n + 1 : ℕ) : ℝ))| = (n + 1 : ℕ) :=
    abs_of_nonneg (Nat.cast_nonneg (n + 1))
  rw [hdenabs]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n + 1 : ℕ))).2
  calc
    |∑ k ∈ Finset.range (n + 1), c k|
        ≤ ∑ k ∈ Finset.range (n + 1), |c k| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range (n + 1), C := by
      gcongr with k hk
      exact hC k
    _ = C * (n + 1 : ℕ) := by
      simp [mul_comm]

/-- Hardy's Cesàro-to-Abel implication for bounded real sequences, in the
normalization used by the discounted word calculations. -/
theorem tendsto_realNormalizedAbelMean_of_tendsto_realCesaroMean
    (c : ℕ → ℝ) (C L : ℝ) (hC : ∀ n, |c n| ≤ C)
    (hCesaro : Tendsto (realCesaroMean c) atTop (𝓝 L)) :
    Tendsto (realNormalizedAbelMean c) (𝓝[<] (1 : ℝ)) (𝓝 L) := by
  let b : ℕ → ℝ := fun n => realCesaroMean c (n + 1)
  have hb : Tendsto b atTop (𝓝 L) := by
    exact hCesaro.comp (tendsto_add_atTop_nat 1)
  have hbBound : ∀ n, |b n - L| ≤ C + |L| := by
    intro n
    calc
      |b n - L| ≤ |b n| + |L| := abs_sub _ _
      _ ≤ C + |L| := by
        change |realCesaroMean c (n + 1)| + |L| ≤ C + |L|
        exact add_le_add (abs_realCesaroMean_succ_le c C hC n) le_rfl
  have hkernel := tendsto_cesaroAbelKernel_sum b L (C + |L|) hbBound hb
  apply hkernel.congr'
  filter_upwards
    [((eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono inf_le_left),
      self_mem_nhdsWithin] with s hs0 hs1
  exact (realNormalizedAbelMean_eq_kernel_cesaro c C s hC hs0.le hs1).symm

end IndependentZeroBlocks
