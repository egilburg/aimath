import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.Basic

/-! # Analytic normalization of positive finite weights

Using positive weights rather than simplex coordinates gives a convenient
open parameter domain for the density theorem. Normalization is analytic
where the total weight is nonzero.
-/

noncomputable section
open scoped BigOperators Topology
namespace IndependentZeroBlocks

variable {A : Type*} [Fintype A]

def normalizedRealWeights (p : A → ℝ) (a : A) : ℝ := p a / ∑ b, p b

def normalizedComplexWeights (p : A → ℂ) (a : A) : ℂ := p a / ∑ b, p b

theorem totalWeight_pos [Nonempty A] (p : A → ℝ) (hp : ∀ a, 0 < p a) :
    0 < ∑ a, p a :=
  Finset.sum_pos (fun a _ ↦ hp a) Finset.univ_nonempty

theorem normalizedRealWeights_pos [Nonempty A]
    (p : A → ℝ) (hp : ∀ a, 0 < p a) (a : A) :
    0 < normalizedRealWeights p a :=
  div_pos (hp a) (totalWeight_pos p hp)

theorem sum_normalizedRealWeights [Nonempty A]
    (p : A → ℝ) (hp : ∀ a, 0 < p a) :
    ∑ a, normalizedRealWeights p a = 1 := by
  simp only [normalizedRealWeights, div_eq_mul_inv, ← Finset.sum_mul]
  exact mul_inv_cancel₀ (ne_of_gt (totalWeight_pos p hp))

theorem normalizedRealWeights_eq_self (p : A → ℝ) (hp : ∑ a, p a = 1) :
    normalizedRealWeights p = p := by
  funext a
  simp [normalizedRealWeights, hp]

def complexifyWeightVector (p : A → ℝ) : A → ℂ := fun a ↦ (p a : ℂ)

@[simp] theorem normalizedComplexWeights_complexify (p : A → ℝ) :
    normalizedComplexWeights (complexifyWeightVector p) =
      complexifyWeightVector (normalizedRealWeights p) := by
  funext a
  simp [normalizedComplexWeights, normalizedRealWeights, complexifyWeightVector]

theorem analyticAt_normalizedComplexWeights (p : A → ℂ)
    (hp : ∑ a, p a ≠ 0) : AnalyticAt ℂ normalizedComplexWeights p := by
  apply AnalyticAt.pi
  intro a
  apply ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : A ↦ ℂ) a).analyticAt p).fun_div
  · have hb (b : A) : AnalyticAt ℂ (fun i : A → ℂ ↦ i b) p :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : A ↦ ℂ) b).analyticAt p
    convert! Finset.analyticAt_sum Finset.univ (fun b _ ↦ hb b) using 1
    funext i
    simp only [Finset.sum_apply]
  · exact hp

theorem analyticAt_complexifyWeightVector (p : A → ℝ) :
    AnalyticAt ℝ complexifyWeightVector p := by
  apply AnalyticAt.pi
  intro a
  exact (Complex.ofRealCLM.analyticAt (p a)).comp
    (f := fun x : A → ℝ ↦ x a) (x := p)
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : A ↦ ℝ) a).analyticAt p)

theorem analyticAt_realPart_complexify
    (f : (A → ℂ) → ℂ) (p : A → ℝ)
    (hf : AnalyticAt ℂ f (complexifyWeightVector p)) :
    AnalyticAt ℝ (fun x : A → ℝ ↦ (f (complexifyWeightVector x)).re) p := by
  have hr : AnalyticAt ℝ f (complexifyWeightVector p) := hf.restrictScalars
  have hcomp : AnalyticAt ℝ (fun x : A → ℝ ↦ f (complexifyWeightVector x)) p :=
    hr.comp (analyticAt_complexifyWeightVector p)
  exact (Complex.reCLM.analyticAt (f (complexifyWeightVector p))).comp
    (f := fun x : A → ℝ ↦ f (complexifyWeightVector x)) (x := p) hcomp

theorem complex_totalWeight_ne_zero [Nonempty A]
    (p : A → ℝ) (hp : ∀ a, 0 < p a) :
    ∑ a, complexifyWeightVector p a ≠ 0 := by
  simpa only [complexifyWeightVector, ← Complex.ofReal_sum, ne_eq,
    Complex.ofReal_eq_zero] using ne_of_gt (totalWeight_pos p hp)

end IndependentZeroBlocks
