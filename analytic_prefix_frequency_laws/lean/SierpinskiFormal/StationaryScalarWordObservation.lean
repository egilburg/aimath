import SierpinskiFormal.ScalarWordStability
import SierpinskiFormal.StationaryBooleanMean
import SierpinskiFormal.FiniteStateDensity

set_option autoImplicit false

/-!
# Stationary limits for scalar word observations

The stationary Boolean theorem is applied to finite families of recognizable
scalar word functions over an arbitrary commutative ring.  The result keeps
the common Bochner `L¹` and almost-everywhere contextual prefix limit.
-/

noncomputable section

open Filter Topology MeasureTheory

namespace IndependentZeroBlocks

@[simp] theorem scalarWordBooleanValue_eq_boolIndicator_predicate
    {R A J : Type*} [Zero R]
    (op : (J → Bool) → Bool) (f : J → List A → R) (w : List A) :
    scalarWordBooleanValue op f w =
      boolIndicator (scalarWordBooleanPredicate op f w) := rfl

variable {Ω A R J : Type*} [MeasurableSpace Ω]
  [CommRing R] [Fintype J]
  [TopologicalSpace A] [DiscreteTopology A]
  [Fintype A] [Nonempty A] [DecidableEq A]
  [MeasurableSpace A] [MeasurableSingletonClass A] [BorelSpace A]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Every stationary finite-alphabet source has almost surely convergent
prefix averages for a finite Boolean combination of recognizable scalar word
supports, uniformly over all fixed left contexts. -/
theorem ae_tendsto_stationary_scalarWordBooleanPredicate
    (f : J → List A → R)
    (D : ∀ j, ScalarWordRepresentation R A (f j))
    (op : (J → Bool) → Bool)
    (letter : Ω → A) (hletter : Measurable letter)
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) :
    ∀ᵐ x ∂μ, ∃ h : BoundedWordFunction A,
      Tendsto (fun N ↦ stationaryWordCesaro letter T
        (booleanWordIndicator (scalarWordBooleanPredicate op f)) N x)
        atTop (𝓝 h) := by
  exact ae_tendsto_stationaryBooleanWordCesaro letter hletter T hT _
    (ScalarWordRepresentation.family_booleanPredicate_hasBooleanDoubleLimitProperty
      D op)

/-- Recognizable scalar Boolean prefix averages converge in Bochner `L¹` and
almost surely in supremum norm to the same limit field.  The coefficient ring,
alphabet, and finite observation family are all generic. -/
theorem exists_stationary_scalarWordBoolean_mean_and_ae_limit
    (f : J → List A → R)
    (D : ∀ j, ScalarWordRepresentation R A (f j))
    (op : (J → Bool) → Bool)
    (letter : Ω → A) (hletter : Measurable letter)
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) :
    let q := booleanWordIndicator (scalarWordBooleanPredicate op f)
    ∃ a : Lp (BoundedWordFunction A) 1 μ,
      Tendsto (fun N ↦ birkhoffAverage ℝ
        (stationaryWordSkewL1CLM letter hletter T hT) id N
        (Lp.const 1 μ q)) atTop (𝓝 a) ∧
      (∀ᵐ x ∂μ, Tendsto (fun N ↦ stationaryWordCesaro letter T q N x)
        atTop (𝓝 (a x))) := by
  exact exists_stationaryBooleanWordCesaro_mean_and_ae_limit
    letter hletter T hT _
      (ScalarWordRepresentation.family_booleanPredicate_hasBooleanDoubleLimitProperty
        D op)

end IndependentZeroBlocks
