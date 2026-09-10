import SierpinskiFormal.StationaryAlgebraicApplications
import SierpinskiFormal.StationaryMeanConvergence

/-! # A common Bochner and pathwise limit for stable Boolean predicates -/

noncomputable section
open Filter Topology MeasureTheory

namespace IndependentZeroBlocks

variable {Ω A : Type*} [MeasurableSpace Ω]
  [TopologicalSpace A] [DiscreteTopology A]
  [Fintype A] [Nonempty A] [DecidableEq A]
  [MeasurableSpace A] [MeasurableSingletonClass A] [BorelSpace A]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Stable Boolean prefix averages converge in Bochner `L¹` and almost surely
in supremum norm to one and the same limit field. -/
theorem exists_stationaryBooleanWordCesaro_mean_and_ae_limit
    (letter : Ω → A) (hletter : Measurable letter)
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (q : List A → Bool)
    (hDLP : HasBooleanDoubleLimitProperty (fun w z ↦ q (z ++ w))) :
    ∃ a : Lp (BoundedWordFunction A) 1 μ,
      Tendsto (fun N ↦ birkhoffAverage ℝ
        (stationaryWordSkewL1CLM letter hletter T hT) id N
        (Lp.const 1 μ (booleanWordIndicator q))) atTop (𝓝 a) ∧
      (∀ᵐ x ∂μ, Tendsto (fun N ↦ stationaryWordCesaro letter T
        (booleanWordIndicator q) N x) atTop (𝓝 (a x))) := by
  exact exists_stationaryWordSkewL1_mean_limit_of_ae_exists_limit
    letter hletter T hT (booleanWordIndicator q)
      (ae_tendsto_stationaryBooleanWordCesaro letter hletter T hT q hDLP)

/-- The same-limit mean and pathwise conclusion for the exact padded Boolean
polynomial predicate of the central regular-support theorem. -/
theorem exists_stationary_polynomialRegularPaddedSupport_mean_and_ae_limit
    {K I : Type*} [CommRing K] {b d : ℕ}
    (hb : 2 ≤ b) (f : I → ℕ → K)
    (hregular : ∀ i, IsRadixRegular b (f i))
    (P : Fin d → MvPolynomial I K) (op : (Fin d → Bool) → Bool)
    (letter : Ω → Fin b) (hletter : Measurable letter)
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) :
    let q := booleanWordIndicator (paddedPredicateBool
      (fun n ↦ op (fun j ↦ nonzeroBool
        (MvPolynomial.eval (fun i ↦ f i n) (P j))) = true) b)
    ∃ a : Lp (BoundedWordFunction (Fin b)) 1 μ,
      Tendsto (fun N ↦ birkhoffAverage ℝ
        (stationaryWordSkewL1CLM letter hletter T hT) id N
        (Lp.const 1 μ q)) atTop (𝓝 a) ∧
      (∀ᵐ x ∂μ, Tendsto (fun N ↦ stationaryWordCesaro letter T q N x)
        atTop (𝓝 (a x))) := by
  exact exists_stationaryWordSkewL1_mean_limit_of_ae_exists_limit
    letter hletter T hT _
      (ae_tendsto_stationary_polynomialRegularPaddedSupport
        hb f hregular P op letter hletter T hT)

end IndependentZeroBlocks
