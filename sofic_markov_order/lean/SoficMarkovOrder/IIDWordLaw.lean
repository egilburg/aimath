import SoficMarkovOrder.IIDMeasure
import SoficMarkovOrder.FiniteWords
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Exact finite-word laws for the canonical IID source

The first `n` letters read through the `sequenceHead`, `sequenceShift`, and
`orbitPrefix` definitions have the expected product distribution.  The
main result computes the integral of an arbitrary real observable on words.
-/

noncomputable section

open Function MeasureTheory
open scoped BigOperators ENNReal

namespace SoficMarkovOrder

namespace FiniteProbabilityWeights

variable {A : Type*}

/-- The canonical prefix is exactly the list of the first `n`
coordinates. -/
theorem orbitPrefix_sequence_eq_ofFn (n : ℕ) (ω : ℕ → A) :
    orbitPrefix sequenceHead sequenceShift n ω =
      List.ofFn (fun i : Fin n ↦ ω i.val) := by
  induction n generalizing ω with
  | zero => rfl
  | succ n ih =>
      rw [orbitPrefix_succ, List.ofFn_succ]
      simp only [sequenceHead_apply, List.singleton_append]
      congr 1
      simpa using ih (sequenceShift ω)

variable [MeasurableSpace A]

/-- The map which retains the first `n` coordinates is measurable. -/
theorem measurable_firstCoordinates (n : ℕ) :
    Measurable (fun ω : ℕ → A ↦ fun i : Fin n ↦ ω i.val) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply i.val

variable [Fintype A] [MeasurableSingletonClass A]

variable [DecidableEq A]

/-- Exact finite-horizon expectation law for the canonical IID source. -/
theorem integral_comp_orbitPrefix_sequence
    (L : FiniteProbabilityWeights A) (n : ℕ) (F : List A → ℝ) :
    (∫ ω, F (orbitPrefix sequenceHead sequenceShift n ω) ∂L.iidMeasure) =
      ∑ w : Fin n → A,
        wordWeight L.weight (List.ofFn w) * F (List.ofFn w) := by
  let φ : (ℕ → A) → (Fin n → A) := fun ω i ↦ ω i.val
  let G : (Fin n → A) → ℝ := fun w ↦ F (List.ofFn w)
  have hφ : Measurable φ := measurable_firstCoordinates n
  have hmap : L.iidMeasure.map φ =
      Measure.infinitePi (fun _ : Fin n ↦ L.letterMeasure) :=
    map_iidMeasure_firstCoordinates L n
  have hG : Integrable G
      (Measure.infinitePi (fun _ : Fin n ↦ L.letterMeasure)) := .of_finite
  have hGmap : Integrable G (L.iidMeasure.map φ) := by
    rw [hmap]
    exact hG
  calc
    (∫ ω, F (orbitPrefix sequenceHead sequenceShift n ω) ∂L.iidMeasure) =
        ∫ ω, G (φ ω) ∂L.iidMeasure := by
          congr 1
          funext ω
          exact congrArg F (orbitPrefix_sequence_eq_ofFn n ω)
    _ = ∫ w, G w ∂(L.iidMeasure.map φ) :=
      (integral_map hφ.aemeasurable hGmap.aestronglyMeasurable).symm
    _ = ∫ w, G w ∂(Measure.infinitePi
        (fun _ : Fin n ↦ L.letterMeasure)) := by rw [hmap]
    _ = ∑ w : Fin n → A,
        wordWeight L.weight (List.ofFn w) * F (List.ofFn w) := by
      rw [integral_fintype hG]
      apply Finset.sum_congr rfl
      intro w _
      simp only [Measure.real, Measure.infinitePi_singleton_of_fintype,
        letterMeasure_singleton, wordWeight, G, smul_eq_mul]
      rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ L.nonneg (w i)),
        ENNReal.toReal_ofReal (Finset.prod_nonneg fun i _ ↦ L.nonneg (w i))]
      simp [List.prod_ofFn]

end FiniteProbabilityWeights

end SoficMarkovOrder
