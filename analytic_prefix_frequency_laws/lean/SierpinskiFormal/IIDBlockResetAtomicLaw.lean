import SierpinskiFormal.IIDResetAtomicLaw
import SierpinskiFormal.IIDBlockPath

/-! # A common blocked initial boundary determines full physical frequencies -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter MeasureTheory Set Topology
open scoped BigOperators
namespace IndependentZeroBlocks

variable {A : Type*} [MeasurableSpace A] [MeasurableSingletonClass A]
  [Fintype A] [DecidableEq A] [Nonempty A]
  [TopologicalSpace A] [DiscreteTopology A] [BorelSpace A]

theorem ae_tendsto_annealed_prefixMeans (P : FiniteProbabilityWeights A)
    (q : List A → Bool) (L : (ℕ → A) → ℝ) (H : List A → ℝ)
    (hLi : Integrable L P.iidMeasure)
    (hL : ∀ᵐ ω ∂P.iidMeasure, Tendsto
      (fun N ↦ stationaryBooleanFrequency digitHead digitShift q N ω) atTop (𝓝 (L ω)))
    (hH : ∀ w, Tendsto (realCesaroMean (fun j ↦
      weightedWordExtensionAverage P.weight (booleanWordIndicator q) j w))
      atTop (𝓝 (H w))) :
    ∀ᵐ ω ∂P.iidMeasure, Tendsto
      (fun n ↦ H (stationaryPrefix digitHead digitShift (n + 1) ω)) atTop (𝓝 (L ω)) := by
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
  filter_upwards [hLi'.tendsto_ae_condExp hLm', hc, hmk] with ω hl hcω hmω
  rw [hmω]
  exact hl.congr hcω

theorem iid_block_frequency_limit_eq_initialGap
    (P : FiniteProbabilityWeights A) (ell : ℕ) (hell : 0 < ell)
    (e : Fin ell → A) (he : 0 < (P.blockLaw ell).weight e)
    (q : List A → Bool) (L : (ℕ → A) → ℝ) (H : List A → ℝ)
    (D : GapWords e → ℝ) (hLi : Integrable L P.iidMeasure)
    (hL : ∀ᵐ ω ∂P.iidMeasure, Tendsto
      (fun N ↦ stationaryBooleanFrequency digitHead digitShift q N ω) atTop (𝓝 (L ω)))
    (hH : ∀ w, Tendsto (realCesaroMean (fun j ↦
      weightedWordExtensionAverage P.weight (booleanWordIndicator q) j w))
      atTop (𝓝 (H w)))
    (hreset : ∀ (u : GapWords e) (t : List (Fin ell → A)),
      H (flattenBlocks ell (u.1 ++ [e] ++ t)) = D u) :
    L =ᵐ[P.iidMeasure] fun ω ↦ D (initialMarkerGap e (iidBlockPath ell ω)) := by
  have hpref := ae_tendsto_annealed_prefixMeans P q L H hLi hL hH
  have hh := (measurePreserving_iidBlockPath P ell hell).quasiMeasurePreserving.ae
    (ae_hasMarker (P.blockLaw ell) e he)
  have hsub : Tendsto (fun n : ℕ ↦ (n + 1) * ell - 1) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    have hm : n + 1 ≤ (n + 1) * ell := Nat.le_mul_of_pos_right _ hell
    omega
  filter_upwards [hpref, hh] with ω hpω hhω
  have hb : ∀ᶠ n in atTop,
      H (stationaryPrefix digitHead digitShift ((n + 1) * ell) ω) =
        D (initialMarkerGap e (iidBlockPath ell ω)) := by
    filter_upwards [eventually_prefix_after_initialMarker e (iidBlockPath ell ω) hhω]
      with n hn
    obtain ⟨t, ht⟩ := hn
    rw [← flatten_iidBlockPath_prefix, ht, hreset]
  have hc : Tendsto
      (fun n ↦ H (stationaryPrefix digitHead digitShift ((n + 1) * ell) ω))
      atTop (𝓝 (L ω)) := by
    have h := hpω.comp hsub
    have heq (n : ℕ) : (n + 1) * ell - 1 + 1 = (n + 1) * ell :=
      Nat.sub_add_cancel (Nat.mul_pos (Nat.succ_pos n) hell)
    simpa only [Function.comp_def, heq] using h
  exact tendsto_nhds_unique hc (tendsto_const_nhds.congr' (hb.mono fun _ hn ↦ hn.symm))

theorem iid_block_reset_atomic_law
    (P : FiniteProbabilityWeights A) (ell : ℕ) (hell : 0 < ell)
    (e : Fin ell → A) (he : 0 < (P.blockLaw ell).weight e)
    (q : List A → Bool)
    (hDLP : HasBooleanDoubleLimitProperty (fun w z ↦ q (z ++ w)))
    (D : GapWords e → ℝ)
    (hreset : ∀ (u : GapWords e) (t : List (Fin ell → A)),
      Tendsto (realCesaroMean (fun j ↦ weightedWordExtensionAverage P.weight
        (booleanWordIndicator q) j (flattenBlocks ell (u.1 ++ [e] ++ t))))
        atTop (𝓝 (D u))) :
    (∀ᵐ ω ∂P.iidMeasure, Tendsto
      (fun N ↦ stationaryBooleanFrequency digitHead digitShift q N ω)
      atTop (𝓝 (D (initialMarkerGap e (iidBlockPath ell ω))))) ∧
    Tendsto (fun N ↦ ∫ ω, ‖stationaryBooleanFrequency digitHead digitShift q N ω -
      D (initialMarkerGap e (iidBlockPath ell ω))‖ ∂P.iidMeasure) atTop (𝓝 0) ∧
    P.iidMeasure.map (fun ω ↦ D (initialMarkerGap e (iidBlockPath ell ω))) =
      Measure.sum (fun u : GapWords e ↦
        ENNReal.ofReal ((P.blockLaw ell).weight e *
          wordWeight (P.blockLaw ell).weight u.1) • Measure.dirac (D u)) := by
  obtain ⟨L, hLi, _, hL, hL1, _⟩ := exists_stationaryBooleanFrequency_limit
    digitHead measurable_digitHead digitShift P.measurePreserving_digitShift_iidMeasure q hDLP
  obtain ⟨H, hH⟩ := exists_all_context_annealed_means P q hDLP
  have heq := iid_block_frequency_limit_eq_initialGap P ell hell e he q L H D hLi hL hH
    (fun u t ↦ tendsto_nhds_unique (hH _) (hreset u t))
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hL, heq] with ω hω heω
    rwa [← heω]
  · apply hL1.congr
    intro N
    apply integral_congr_ae
    filter_upwards [heq] with ω hω
    rw [hω]
  · have hm : Measurable (fun ω : ℕ → (Fin ell → A) ↦ D (initialMarkerGap e ω)) :=
      (measurable_of_countable D).comp (measurable_initialMarkerGap e)
    rw [show (fun ω ↦ D (initialMarkerGap e (iidBlockPath ell ω))) =
      (fun ω ↦ D (initialMarkerGap e ω)) ∘ iidBlockPath ell from rfl,
      ← Measure.map_map hm (measurable_iidBlockPath ell),
      (measurePreserving_iidBlockPath P ell hell).map_eq]
    rw [map_eq_countable_boundary_mixture (P.blockLaw ell).iidMeasure (initialMarkerGap e) D
      (fun ω ↦ D (initialMarkerGap e ω)) (measurable_initialMarkerGap e) Filter.EventuallyEq.rfl]
    simp only [iidMeasure_initialMarkerGap (P.blockLaw ell) e he]

end IndependentZeroBlocks
