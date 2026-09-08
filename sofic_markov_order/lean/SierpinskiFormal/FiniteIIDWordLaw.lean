import SierpinskiFormal.FiniteIIDMeasure
import SierpinskiFormal.WeightedWordEnumeration
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Exact finite-word laws for the canonical IID source

The first `n` letters read through the accepted `digitHead`, `digitShift`, and
`stationaryPrefix` definitions have the expected product distribution.  The
main result computes the integral of an arbitrary real observable on words.
-/

noncomputable section

open Function MeasureTheory
open scoped BigOperators ENNReal

namespace IndependentZeroBlocks

namespace FiniteProbabilityWeights

variable {A : Type*}

/-- The accepted canonical prefix is exactly the list of the first `n`
coordinates. -/
theorem stationaryPrefix_digit_eq_ofFn (n : ℕ) (ω : ℕ → A) :
    stationaryPrefix digitHead digitShift n ω =
      List.ofFn (fun i : Fin n ↦ ω i.val) := by
  induction n generalizing ω with
  | zero => rfl
  | succ n ih =>
      rw [stationaryPrefix_succ, List.ofFn_succ]
      simp only [digitHead_apply, List.singleton_append]
      congr 1
      simpa using ih (digitShift ω)

variable [MeasurableSpace A]

/-- The map which retains the first `n` coordinates is measurable. -/
theorem measurable_firstCoordinates (n : ℕ) :
    Measurable (fun ω : ℕ → A ↦ fun i : Fin n ↦ ω i.val) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply i.val

variable [Fintype A] [MeasurableSingletonClass A]

/-- Every real observable of a fixed canonical prefix is measurable. -/
theorem measurable_comp_stationaryPrefix_digit (n : ℕ) (F : List A → ℝ) :
    Measurable (fun ω : ℕ → A ↦
      F (stationaryPrefix digitHead digitShift n ω)) := by
  rw [funext fun ω ↦ congrArg F (stationaryPrefix_digit_eq_ofFn n ω)]
  exact (measurable_of_countable (fun w : Fin n → A ↦ F (List.ofFn w))).comp
    (measurable_firstCoordinates n)

/-- Every real observable of a fixed prefix is integrable under the canonical
IID law. -/
theorem integrable_comp_stationaryPrefix_digit
    (L : FiniteProbabilityWeights A) (n : ℕ) (F : List A → ℝ) :
    Integrable (fun ω : ℕ → A ↦
      F (stationaryPrefix digitHead digitShift n ω)) L.iidMeasure := by
  let φ : (ℕ → A) → (Fin n → A) := fun ω i ↦ ω i.val
  let G : (Fin n → A) → ℝ := fun w ↦ F (List.ofFn w)
  have hφ : Measurable φ := measurable_firstCoordinates n
  have hmap : L.iidMeasure.map φ =
      Measure.infinitePi (fun _ : Fin n ↦ L.letterMeasure) :=
    map_iidMeasure_firstCoordinates L n
  have hG : Integrable G (L.iidMeasure.map φ) := by
    rw [hmap]
    exact .of_finite
  have hcomp := hG.comp_aemeasurable hφ.aemeasurable
  simpa [φ, G, Function.comp_def, stationaryPrefix_digit_eq_ofFn] using hcomp

variable [DecidableEq A]

/-- Exact finite-horizon expectation law for the canonical IID source. -/
theorem integral_comp_stationaryPrefix_digit
    (L : FiniteProbabilityWeights A) (n : ℕ) (F : List A → ℝ) :
    (∫ ω, F (stationaryPrefix digitHead digitShift n ω) ∂L.iidMeasure) =
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
    (∫ ω, F (stationaryPrefix digitHead digitShift n ω) ∂L.iidMeasure) =
        ∫ ω, G (φ ω) ∂L.iidMeasure := by
          congr 1
          funext ω
          exact congrArg F (stationaryPrefix_digit_eq_ofFn n ω)
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

omit [DecidableEq A] in
/-- Consumer-facing name for fixed-prefix measurability. -/
theorem measurable_stationaryPrefix (n : ℕ) (F : List A → ℝ) :
    Measurable (fun ω : ℕ → A ↦
      F (stationaryPrefix digitHead digitShift n ω)) :=
  measurable_comp_stationaryPrefix_digit n F

omit [DecidableEq A] in
/-- Consumer-facing name for fixed-prefix integrability under the IID law. -/
theorem integrable_stationaryPrefix
    (L : FiniteProbabilityWeights A) (n : ℕ) (F : List A → ℝ) :
    Integrable (fun ω : ℕ → A ↦
      F (stationaryPrefix digitHead digitShift n ω)) L.iidMeasure :=
  integrable_comp_stationaryPrefix_digit L n F

/-- Consumer-facing name for the exact fixed-prefix expectation law. -/
theorem integral_stationaryPrefix
    (L : FiniteProbabilityWeights A) (n : ℕ) (F : List A → ℝ) :
    (∫ ω, F (stationaryPrefix digitHead digitShift n ω) ∂L.iidMeasure) =
      ∑ w : Fin n → A,
        wordWeight L.weight (List.ofFn w) * F (List.ofFn w) :=
  integral_comp_stationaryPrefix_digit L n F

end FiniteProbabilityWeights

end IndependentZeroBlocks
