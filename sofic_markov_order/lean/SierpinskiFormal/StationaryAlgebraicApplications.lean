import SierpinskiFormal.StationaryBooleanConvergence
import SierpinskiFormal.RecognizableSupportCompactness
import SierpinskiFormal.BooleanRegularLogDensity
import SierpinskiFormal.PolynomialObservedSupport

set_option autoImplicit false

/-!
# Stationary convergence for algebraic Boolean observations

The generic stable-Boolean stationary theorem is specialized to
recognizable matrix-word supports and to the padded polynomial support
language used by the central logarithmic-density theorem.
-/

noncomputable section

open Filter Topology MeasureTheory

namespace IndependentZeroBlocks

variable {Ω : Type*} [MeasurableSpace Ω]
  {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Every stationary finite-alphabet source has almost surely convergent
recognizable Boolean prefix averages, uniformly over all left contexts. -/
theorem ae_tendsto_stationary_recognizableBooleanWordSupport
    {K ι : Type*} [CommRing K] [Fintype ι]
    {b d : ℕ} (hb : 0 < b)
    (op : (Fin d → Bool) → Bool)
    (M : Fin d → Fin b → Matrix ι ι K)
    (u a : Fin d → ι → K)
    (letter : Ω → Fin b) (hletter : Measurable letter)
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) :
    ∀ᵐ x ∂μ, ∃ h : BoundedWordFunction (Fin b),
      Tendsto (fun N ↦ stationaryWordCesaro letter T
        (booleanWordIndicator (recognizableBooleanWordSupport op M u a)) N x)
        atTop (𝓝 h) := by
  letI : Nonempty (Fin b) := ⟨⟨0, hb⟩⟩
  exact ae_tendsto_stationaryBooleanWordCesaro letter hletter T hT _
    (recognizableBooleanWordSupport_rightKernel_hasBooleanDoubleLimitProperty
      op M u a)

/-- For every stationary base-`b` digit source, finite Boolean formulas in
polynomial observations of radix-regular sequences have almost surely
convergent padded-word prefix averages, uniformly over all left contexts.
This uses the same natural-number predicate as
`polynomial_boolean_standardLogDensity_exists`. -/
theorem ae_tendsto_stationary_polynomialRegularPaddedSupport
    {K I : Type*} [CommRing K] {b d : ℕ}
    (hb : 2 ≤ b) (f : I → ℕ → K)
    (hregular : ∀ i, IsRadixRegular b (f i))
    (P : Fin d → MvPolynomial I K)
    (op : (Fin d → Bool) → Bool)
    (letter : Ω → Fin b) (hletter : Measurable letter)
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) :
    ∀ᵐ x ∂μ, ∃ h : BoundedWordFunction (Fin b),
      Tendsto (fun N ↦ stationaryWordCesaro letter T
        (booleanWordIndicator (paddedPredicateBool
          (fun n ↦ op (fun j ↦ nonzeroBool
            (MvPolynomial.eval (fun i ↦ f i n) (P j))) = true) b)) N x)
        atTop (𝓝 h) := by
  letI : Nonempty (Fin b) := ⟨⟨0, by omega⟩⟩
  letI : Nonempty (Fin b) := ⟨⟨0, by omega⟩⟩
  let observed : Fin d → ℕ → K := fun j n ↦
    MvPolynomial.eval (fun i ↦ f i n) (P j)
  let S : ℕ → Prop := booleanRegularSupport op observed
  have hobserved : ∀ j, IsRadixRegular b (observed j) := fun j ↦
    IsRadixRegular.polynomial b hb f hregular (P j)
  have hstable : HasStablePaddedDigitKernel S b :=
    booleanRegularSupport_hasStablePaddedDigitKernel
      b hb op observed hobserved
  apply ae_tendsto_stationaryBooleanWordCesaro letter hletter T hT
    (paddedPredicateBool S b)
  simpa only [HasStablePaddedDigitKernel] using hstable.swap

end IndependentZeroBlocks
