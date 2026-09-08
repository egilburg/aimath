import SierpinskiFormal.StationaryBooleanWeakCluster
import SierpinskiFormal.StationaryPointwise

/-!
# Uniform pathwise convergence for stable Boolean word predicates

The paired Boolean compacta provide the weak Bochner cluster required by the
skew mean and maximal theorems.  The conclusion holds for every stationary
finite-alphabet source, and convergence is in the norm of bounded word
functions: all fixed left contexts are controlled simultaneously.
-/

noncomputable section

set_option maxSynthPendingDepth 4
set_option maxHeartbeats 2000000

open Function Set Filter Topology MeasureTheory
open scoped ENNReal BigOperators BoundedContinuousFunction

namespace IndependentZeroBlocks

section Canonical

variable {A : Type*} [Fintype A] [Nonempty A] [DecidableEq A]
  [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [MeasurableSingletonClass A] [BorelSpace A]
  {μ : Measure (ℕ → A)} [IsProbabilityMeasure μ]

/-- On the canonical one-sided shift, stable Boolean word predicates have
almost surely convergent prefix averages, uniformly over every left context. -/
theorem ae_tendsto_stationaryBooleanWordCesaro_canonical
    (q : List A → Bool)
    (hDLP : HasBooleanDoubleLimitProperty (fun w z ↦ q (z ++ w)))
    (hshift : MeasurePreserving digitShift μ μ) :
    ∀ᵐ s ∂μ, ∃ h : BoundedWordFunction A,
      Tendsto (fun N => stationaryWordCesaro digitHead digitShift
        (booleanWordIndicator q) N s) atTop (𝓝 h) := by
  obtain ⟨a, ha⟩ := exists_weak_mapClusterPt_stationaryBooleanWordCesaro q hDLP hshift
  exact ae_exists_tendsto_stationaryWordCesaro_of_weak_mapClusterPt
    digitHead measurable_digitHead digitShift hshift (booleanWordIndicator q) a ha

end Canonical

section ArbitrarySource

variable {Ω A : Type*} [MeasurableSpace Ω]
  [Fintype A] [Nonempty A] [DecidableEq A]
  [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [MeasurableSingletonClass A] [BorelSpace A]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Every stationary finite-alphabet source gives almost-sure norm convergence
of stable Boolean word-prefix averages.  Neither independence nor ergodicity
of the source is assumed. -/
theorem ae_tendsto_stationaryBooleanWordCesaro
    (letter : Ω → A) (hletter : Measurable letter)
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (q : List A → Bool)
    (hDLP : HasBooleanDoubleLimitProperty (fun w z ↦ q (z ++ w))) :
    ∀ᵐ x ∂μ, ∃ h : BoundedWordFunction A,
      Tendsto (fun N => stationaryWordCesaro letter T
        (booleanWordIndicator q) N x) atTop (𝓝 h) := by
  let itinerary := stationaryItinerary letter T
  have hm : Measurable itinerary :=
    measurable_stationaryItinerary letter hletter T hT.measurable
  haveI : IsProbabilityMeasure (μ.map itinerary) := Measure.isProbabilityMeasure_map hm.aemeasurable
  apply ae_tendsto_stationaryWordCesaro_of_map_stationaryItinerary
    letter hletter T hT.measurable (booleanWordIndicator q)
  exact ae_tendsto_stationaryBooleanWordCesaro_canonical q hDLP
    (measurePreserving_digitShift_map_stationaryItinerary letter hletter T hT)

end ArbitrarySource

end IndependentZeroBlocks
