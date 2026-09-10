import SierpinskiFormal.StationaryL1Skew

/-!
# From pathwise stationary word limits to Bochner mean convergence

A uniform pointwise bound upgrades almost-everywhere convergence of the
stationary word Cesaro representatives to norm convergence of the actual
Bochner `L¹` skew averages.
-/

noncomputable section

open Filter Finset Function Set MeasureTheory Topology
open scoped ENNReal Topology BigOperators

namespace IndependentZeroBlocks

variable {Ω A : Type*} [MeasurableSpace Ω]
  [TopologicalSpace A] [DiscreteTopology A]
  [Fintype A] [DecidableEq A] [MeasurableSpace A]
  [MeasurableSingletonClass A]
  {μ : Measure Ω} [IsFiniteMeasure μ]

/-- Almost-everywhere existence of pointwise limits for a stationary word
Cesaro sequence yields a Bochner `L¹` limit of the actual skew Birkhoff
averages.  The chosen representative of the limit retains the original
almost-everywhere pointwise convergence. -/
theorem exists_stationaryWordSkewL1_mean_limit_of_ae_exists_limit
    (letter : Ω → A) (hletter : Measurable letter)
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (q : BoundedWordFunction A)
    (hlim : ∀ᵐ x ∂μ, ∃ y : BoundedWordFunction A,
      Tendsto (fun N ↦ stationaryWordCesaro letter T q N x) atTop (𝓝 y)) :
    ∃ a : Lp (BoundedWordFunction A) 1 μ,
      Tendsto
        (fun N ↦ birkhoffAverage ℝ
          (stationaryWordSkewL1CLM letter hletter T hT)
          (id : Lp (BoundedWordFunction A) 1 μ →
            Lp (BoundedWordFunction A) 1 μ)
          N (Lp.const 1 μ q))
        atTop (𝓝 a) ∧
      ∀ᵐ x ∂μ, Tendsto
        (fun N ↦ stationaryWordCesaro letter T q N x) atTop (𝓝 (a x)) := by
  classical
  let limit : Ω → BoundedWordFunction A := fun x ↦
    if hx : ∃ y : BoundedWordFunction A,
        Tendsto (fun N ↦ stationaryWordCesaro letter T q N x) atTop (𝓝 y)
    then Classical.choose hx else 0
  have hpoint : ∀ᵐ x ∂μ, Tendsto
      (fun N ↦ stationaryWordCesaro letter T q N x) atTop (𝓝 (limit x)) := by
    filter_upwards [hlim] with x hx
    simp only [limit, dif_pos hx]
    exact Classical.choose_spec hx
  have hlimit_meas : AEStronglyMeasurable limit μ :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun N ↦ stationaryWordCesaro_aestronglyMeasurable
        letter hletter T hT q N) hpoint
  have hlimit_bound : ∀ᵐ x ∂μ, ‖limit x‖ ≤ ‖q‖ := by
    filter_upwards [hpoint] with x hx
    exact le_of_tendsto hx.norm (Filter.Eventually.of_forall fun N ↦
      norm_stationaryWordCesaro_le letter T q N x)
  have hlimit_mem : MemLp limit 1 μ := by
    exact (memLp_const q).of_le hlimit_meas hlimit_bound
  let a : Lp (BoundedWordFunction A) 1 μ := hlimit_mem.toLp limit
  have ha_coe : (fun x ↦ a x) =ᵐ[μ] limit := by
    exact MemLp.coeFn_toLp _
  have hpoint_a : ∀ᵐ x ∂μ, Tendsto
      (fun N ↦ stationaryWordCesaro letter T q N x) atTop (𝓝 (a x)) := by
    filter_upwards [hpoint, ha_coe] with x hx hax
    simpa [hax] using hx
  let avg : ℕ → Lp (BoundedWordFunction A) 1 μ := fun N ↦
    birkhoffAverage ℝ (stationaryWordSkewL1CLM letter hletter T hT)
      (id : Lp (BoundedWordFunction A) 1 μ →
        Lp (BoundedWordFunction A) 1 μ) N (Lp.const 1 μ q)
  have havg_coe (N : ℕ) : (fun x ↦ avg N x) =ᵐ[μ]
      stationaryWordCesaro letter T q N := by
    simpa only [avg] using
      birkhoffAverage_stationaryWordSkewL1CLM_const_coeFn
        letter hletter T hT q N
  have hdiff_meas (N : ℕ) : AEStronglyMeasurable
      (fun x ↦ ‖stationaryWordCesaro letter T q N x - limit x‖) μ :=
    ((stationaryWordCesaro_aestronglyMeasurable
      letter hletter T hT q N).sub hlimit_meas).norm
  have hdom : ∀ N, ∀ᵐ x ∂μ,
      ‖(fun x ↦ ‖stationaryWordCesaro letter T q N x - limit x‖) x‖ ≤
        (2 * ‖q‖ : ℝ) := by
    intro N
    filter_upwards [hlimit_bound] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    calc
      ‖stationaryWordCesaro letter T q N x - limit x‖ ≤
          ‖stationaryWordCesaro letter T q N x‖ + ‖limit x‖ := norm_sub_le _ _
      _ ≤ ‖q‖ + ‖q‖ := add_le_add
        (norm_stationaryWordCesaro_le letter T q N x) hx
      _ = 2 * ‖q‖ := by ring
  have hzero : ∀ᵐ x ∂μ, Tendsto
      (fun N ↦ ‖stationaryWordCesaro letter T q N x - limit x‖)
      atTop (𝓝 0) := by
    filter_upwards [hpoint] with x hx
    have hc : Tendsto (fun _ : ℕ ↦ limit x) atTop (𝓝 (limit x)) :=
      tendsto_const_nhds
    simpa using (hx.sub hc).norm
  have hint : Tendsto
      (fun N ↦ ∫ x, ‖stationaryWordCesaro letter T q N x - limit x‖ ∂μ)
      atTop (𝓝 0) := by
    simpa using tendsto_integral_of_dominated_convergence
      (fun _ : Ω ↦ 2 * ‖q‖) hdiff_meas (integrable_const _) hdom hzero
  have hnorm (N : ℕ) : ‖avg N - a‖ =
      ∫ x, ‖stationaryWordCesaro letter T q N x - limit x‖ ∂μ := by
    rw [L1.norm_eq_integral_norm]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (avg N) a, havg_coe N, ha_coe] with x hsub hav hla
    rw [hsub]
    change ‖avg N x - a x‖ = _
    rw [hav, hla]
  refine ⟨a, ?_, hpoint_a⟩
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [avg, hnorm] using hint

end IndependentZeroBlocks
