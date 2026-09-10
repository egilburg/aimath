import SierpinskiFormal.InitialMarkerGap
import SierpinskiFormal.IIDConditionalFrequency
import SierpinskiFormal.CountableBoundaryLaw

/-! # Actual IID limits and their atomic law from reset continuation means -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter MeasureTheory Set Topology
open scoped BigOperators
namespace IndependentZeroBlocks

variable {A : Type*} [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype A] [DecidableEq A] [Nonempty A]
  [TopologicalSpace A] [DiscreteTopology A] [BorelSpace A]

theorem exists_all_context_annealed_means (P : FiniteProbabilityWeights A)
    (q : List A → Bool)
    (hDLP : HasBooleanDoubleLimitProperty (fun w z ↦ q (z ++ w))) :
    ∃ H : List A → ℝ, ∀ w, Tendsto (realCesaroMean (fun j ↦
      weightedWordExtensionAverage P.weight (booleanWordIndicator q) j w))
      atTop (𝓝 (H w)) := by
  obtain ⟨H, hH⟩ := exists_tendsto_boolean_weighted_word_mean
    P.weight P.nonneg P.sum_eq_one q hDLP
  refine ⟨H, fun w ↦ ?_⟩
  change Tendsto (fun N ↦ (∑ j ∈ Finset.range N,
    weightedWordExtensionAverage P.weight (booleanWordIndicator q) j w) / (N : ℝ))
    atTop (𝓝 (H w))
  have h := ((BoundedContinuousFunction.evalCLM ℝ w).continuous.tendsto H).comp hH
  simpa [Function.comp_def, BoundedContinuousFunction.evalCLM_apply,
    birkhoffAverage, birkhoffSum, realCesaroMean, div_eq_mul_inv,
    mul_comm, BoundedContinuousFunction.smul_apply, BoundedContinuousFunction.sum_apply,
    iterate_weightedLetterAverage_apply] using h

/-- The finite-prefix conditional expectations eventually equal the branch
of the actual first gap. Levy upward convergence then identifies the actual
pathwise limit. Neither the first-gap identity nor conditional determinism is
assumed. -/
theorem iid_frequency_limit_eq_initialGap
    (P : FiniteProbabilityWeights A) (e : A) (he : 0 < P.weight e)
    (q : List A → Bool) (L : (ℕ → A) → ℝ) (H : List A → ℝ)
    (D : GapWords e → ℝ)
    (hLi : Integrable L P.iidMeasure)
    (hL : ∀ᵐ ω ∂P.iidMeasure, Tendsto
      (fun N ↦ stationaryBooleanFrequency digitHead digitShift q N ω) atTop (𝓝 (L ω)))
    (hH : ∀ w, Tendsto (realCesaroMean (fun j ↦
      weightedWordExtensionAverage P.weight (booleanWordIndicator q) j w))
      atTop (𝓝 (H w)))
    (hreset : ∀ (u : GapWords e) (t : List A), H (u.1 ++ [e] ++ t) = D u) :
    L =ᵐ[P.iidMeasure] fun ω ↦ D (initialMarkerGap e ω) := by
  let L' := hLi.aestronglyMeasurable.mk L
  have hmk : L =ᵐ[P.iidMeasure] L' := hLi.aestronglyMeasurable.ae_eq_mk
  have hLi' : Integrable L' P.iidMeasure := hLi.congr hmk
  have hLm' : StronglyMeasurable[⨆ n, prefixFiltration (A := A) n] L' := by
    rw [iSup_prefixFiltration]
    exact hLi.aestronglyMeasurable.stronglyMeasurable_mk
  have hL' : ∀ᵐ ω ∂P.iidMeasure, Tendsto
      (fun N ↦ stationaryBooleanFrequency digitHead digitShift q N ω) atTop (𝓝 (L' ω)) := by
    filter_upwards [hL, hmk] with ω hω hmω
    rwa [← hmω]
  have hc : ∀ᵐ ω ∂P.iidMeasure, ∀ n,
      (P.iidMeasure[L' | prefixFiltration n]) ω =
        H (stationaryPrefix digitHead digitShift (n + 1) ω) :=
    ae_all_iff.mpr fun n ↦ condExp_iid_frequency_limit P q L' H hL' hH n
  filter_upwards [hLi'.tendsto_ae_condExp hLm', hc, ae_hasMarker P e he, hmk]
    with ω hl hcω hh hmω
  have hb : ∀ᶠ n in atTop, H (stationaryPrefix digitHead digitShift (n + 1) ω) =
      D (initialMarkerGap e ω) := by
    filter_upwards [eventually_prefix_after_initialMarker e ω hh] with n hn
    obtain ⟨t, ht⟩ := hn
    rw [ht, hreset]
  have hb' : Tendsto (fun n ↦ H (stationaryPrefix digitHead digitShift (n + 1) ω))
      atTop (𝓝 (D (initialMarkerGap e ω))) :=
    tendsto_const_nhds.congr' (hb.mono fun _ hn ↦ hn.symm)
  exact hmω.trans (tendsto_nhds_unique (hl.congr hcω) hb')

/-- A stable Boolean event with reset continuation means has the explicit
first-gap limit, in both almost-sure and L1 senses, and the corresponding
countable Dirac mixture. -/
theorem iid_reset_atomic_law
    (P : FiniteProbabilityWeights A) (e : A) (he : 0 < P.weight e)
    (q : List A → Bool)
    (hDLP : HasBooleanDoubleLimitProperty (fun w z ↦ q (z ++ w)))
    (D : GapWords e → ℝ)
    (hreset : ∀ (u : GapWords e) (t : List A),
      Tendsto (realCesaroMean (fun j ↦ weightedWordExtensionAverage P.weight
        (booleanWordIndicator q) j (u.1 ++ [e] ++ t))) atTop (𝓝 (D u))) :
    (∀ᵐ ω ∂P.iidMeasure, Tendsto
      (fun N ↦ stationaryBooleanFrequency digitHead digitShift q N ω)
      atTop (𝓝 (D (initialMarkerGap e ω)))) ∧
    Tendsto (fun N ↦ ∫ ω, ‖stationaryBooleanFrequency digitHead digitShift q N ω -
      D (initialMarkerGap e ω)‖ ∂P.iidMeasure) atTop (𝓝 0) ∧
    P.iidMeasure.map (fun ω ↦ D (initialMarkerGap e ω)) =
      Measure.sum (fun u : GapWords e ↦
        ENNReal.ofReal (P.weight e * wordWeight P.weight u.1) • Measure.dirac (D u)) := by
  obtain ⟨L, hLi, _, hL, hL1, _⟩ := exists_stationaryBooleanFrequency_limit
    digitHead measurable_digitHead digitShift P.measurePreserving_digitShift_iidMeasure q hDLP
  obtain ⟨H, hH⟩ := exists_all_context_annealed_means P q hDLP
  have hbranch : ∀ (u : GapWords e) (t : List A), H (u.1 ++ [e] ++ t) = D u :=
    fun u t ↦ tendsto_nhds_unique (hH _) (hreset u t)
  have heq := iid_frequency_limit_eq_initialGap P e he q L H D hLi hL hH hbranch
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hL, heq] with ω hω heω
    rwa [← heω]
  · have hint (N : ℕ) : (∫ ω, ‖stationaryBooleanFrequency digitHead digitShift q N ω -
        L ω‖ ∂P.iidMeasure) = ∫ ω, ‖stationaryBooleanFrequency digitHead digitShift q N ω -
        D (initialMarkerGap e ω)‖ ∂P.iidMeasure := by
      apply integral_congr_ae
      filter_upwards [heq] with ω hω
      rw [hω]
    exact hL1.congr hint
  · rw [map_eq_countable_boundary_mixture P.iidMeasure (initialMarkerGap e) D
      (fun ω ↦ D (initialMarkerGap e ω)) (measurable_initialMarkerGap e) Filter.EventuallyEq.rfl]
    simp only [iidMeasure_initialMarkerGap P e he]

end IndependentZeroBlocks
