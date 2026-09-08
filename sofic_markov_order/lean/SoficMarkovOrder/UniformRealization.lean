import SoficMarkovOrder.IIDPairFactor
import SoficMarkovOrder.PositiveCompletion
import SoficMarkovOrder.SelectorWeights

set_option autoImplicit false
noncomputable section
namespace SoficMarkovOrder
open MeasureTheory
open scoped BigOperators

variable {Q A : Type*} [Fintype Q] [DecidableEq Q] [Nonempty Q]
  [Fintype A] [DecidableEq A] [Nonempty A]

def uniformEmission (T : A → Module.End ℝ (Q → ℝ)) (ij : Q × Q) (a : A) : ℝ :=
  Fintype.card Q * endEntry (T a) ij.1 ij.2

theorem uniformEmission_nonneg (T : A → Module.End ℝ (Q → ℝ))
    (h0 : ∀ a i j, 0 ≤ endEntry (T a) i j) (ij : Q × Q) (a : A) :
    0 ≤ uniformEmission T ij a := mul_nonneg (by positivity) (h0 _ _ _)

theorem uniformEmission_sum (T : A → Module.End ℝ (Q → ℝ))
    (hsum : ∑ a, T a = uniformMean) (ij : Q × Q) : ∑ a, uniformEmission T ij a = 1 := by
  have he := congrArg (fun f => endEntry f ij.1 ij.2) hsum
  simp only [endEntry, LinearMap.sum_apply, Finset.sum_apply] at he
  simp only [uniformEmission, endEntry, ← Finset.mul_sum]
  rw [he]
  rw [show uniformMean (Pi.single ij.2 (1 : ℝ)) ij.1 = (Fintype.card Q : ℝ)⁻¹ from
    endEntry_uniformMean _ _]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

def uniformSelectorLaw (T : A → Module.End ℝ (Q → ℝ))
    (h0 : ∀ a i j, 0 ≤ endEntry (T a) i j) (hsum : ∑ a, T a = uniformMean) :
    FiniteProbabilityWeights ((Q × Q) → A) where
  weight := selectorWeight (uniformEmission T)
  nonneg F := Finset.prod_nonneg (fun ij _ => uniformEmission_nonneg T h0 ij (F ij))
  sum_eq_one := sum_selectorWeight_eq_one (uniformEmission T)
    (uniformEmission_sum T hsum)

theorem uniformSelector_marginal (T : A → Module.End ℝ (Q → ℝ))
    (h0 : ∀ a i j, 0 ≤ endEntry (T a) i j) (hsum : ∑ a, T a = uniformMean)
    (ij : Q × Q) (a : A) (r : ℝ) :
    (∑ F, (uniformSelectorLaw T h0 hsum).weight F * (if F ij = a then r else 0)) =
      uniformEmission T ij a * r := by
  classical
  have h := sum_selectorWeight_mul_apply
    (uniformEmission T) (uniformEmission_sum T hsum) ij (fun b => if b=a then r else 0)
  simpa [uniformSelectorLaw, mul_ite] using h

abbrev UniformIIDAlphabet (Q A : Type*) := Q × ((Q × Q) → A)

def uniformIIDLaw (S : FiniteProbabilityWeights ((Q × Q) → A)) :
    FiniteProbabilityWeights (UniformIIDAlphabet Q A) where
  weight b := (Fintype.card Q : ℝ)⁻¹ * S.weight b.2
  nonneg b := mul_nonneg (by positivity) (S.nonneg _)
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    simp [← Finset.mul_sum, S.sum_eq_one, Fintype.card_ne_zero]

abbrev uniformIIDCode (b c : UniformIIDAlphabet Q A) : A := b.2 (b.1, c.1)

def selectorCollapse (S : FiniteProbabilityWeights ((Q × Q) → A)) :
    (UniformIIDAlphabet Q A → ℝ) →ₗ[ℝ] (Q → ℝ) :=
  LinearMap.pi fun q => ∑ F, S.weight F • LinearMap.proj (q,F)

@[simp] theorem selectorCollapse_apply (S : FiniteProbabilityWeights ((Q × Q) → A))
    (x : UniformIIDAlphabet Q A → ℝ) (q : Q) :
    selectorCollapse S x q = ∑ F, S.weight F * x (q,F) := by
  simp [selectorCollapse, LinearMap.sum_apply]

@[simp] theorem selectorCollapse_ones (S : FiniteProbabilityWeights ((Q × Q) → A)) :
    selectorCollapse S (fun _ => 1) = fun _ => 1 := by
  ext q; simp [S.sum_eq_one]

theorem end_apply_eq_sum (f : Module.End ℝ (Q → ℝ)) (x : Q → ℝ) (i : Q) :
    f x i = ∑ j, endEntry f i j * x j := by
  have hx : (∑ j, x j • Pi.single j (1 : ℝ)) = x := by
    simpa only [Pi.basisFun_repr, Pi.basisFun_apply] using (Pi.basisFun ℝ Q).sum_repr x
  conv_lhs => rw [← hx]
  simp [map_sum, endEntry, mul_comm]

theorem selectorCollapse_intertwines (T : A → Module.End ℝ (Q → ℝ))
    (h0 : ∀ a i j, 0 ≤ endEntry (T a) i j) (hsum : ∑ a, T a = uniformMean)
    (a : A) (x : UniformIIDAlphabet Q A → ℝ) :
    selectorCollapse (uniformSelectorLaw T h0 hsum)
      (pairLetter (uniformIIDLaw (uniformSelectorLaw T h0 hsum)) uniformIIDCode a x) =
      T a (selectorCollapse (uniformSelectorLaw T h0 hsum) x) := by
  let S := uniformSelectorLaw T h0 hsum
  funext i
  rw [selectorCollapse_apply, end_apply_eq_sum]
  simp only [pairLetter_apply, Fintype.sum_prod_type, uniformIIDLaw, uniformIIDCode]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [selectorCollapse_apply, Finset.mul_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro F' _
  have he (F : (Q × Q) → A) :
      S.weight F * ((Fintype.card Q : ℝ)⁻¹ * S.weight F' *
        (if F (i,j) = a then x (j,F') else 0)) =
      S.weight F * (if F (i,j) = a then
        (Fintype.card Q : ℝ)⁻¹ * S.weight F' * x (j,F') else 0) := by
    split_ifs <;> simp
  dsimp only [S] at he
  simp_rw [he]
  rw [uniformSelector_marginal]
  unfold uniformEmission
  have hn : (Fintype.card Q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp

theorem selectorCollapse_word (T : A → Module.End ℝ (Q → ℝ))
    (h0 : ∀ a i j, 0 ≤ endEntry (T a) i j) (hsum : ∑ a, T a = uniformMean)
    (w : List A) (x : UniformIIDAlphabet Q A → ℝ) :
    selectorCollapse (uniformSelectorLaw T h0 hsum)
      (linearWord (pairLetter (uniformIIDLaw (uniformSelectorLaw T h0 hsum))
        uniformIIDCode) w x) =
      linearWord T w (selectorCollapse (uniformSelectorLaw T h0 hsum) x) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      simp only [linearWord_cons, Module.End.mul_apply]
      rw [selectorCollapse_intertwines, ih]

theorem iidRow_uniform (S : FiniteProbabilityWeights ((Q × Q) → A))
    (x : UniformIIDAlphabet Q A → ℝ) :
    iidRow (uniformIIDLaw S) x = averageRow (selectorCollapse S x) := by
  simp [iidRow_apply, uniformIIDLaw, averageRow_apply, Fintype.sum_prod_type,
    selectorCollapse_apply, Finset.mul_sum, mul_assoc]


variable [MeasurableSpace A] [MeasurableSingletonClass A]

/-- The finite noise alphabet carries its full measurable structure. -/
@[instance_reducible] def uniformIIDMeasurableSpace :
    MeasurableSpace (UniformIIDAlphabet Q A) := ⊤
attribute [local instance] uniformIIDMeasurableSpace

instance uniformIIDMeasurableSingletonClass :
    @MeasurableSingletonClass (UniformIIDAlphabet Q A) uniformIIDMeasurableSpace :=
  ⟨fun _ => trivial⟩

/-- A concrete stationary two-block IID factor realizing a nonnegative
presentation whose total transition is the uniform mean. -/
def uniformSoficMeasure (T : A → Module.End ℝ (Q → ℝ))
    (h0 : ∀ a i j, 0 ≤ endEntry (T a) i j) (hsum : ∑ a, T a = uniformMean) :
    Measure (ℕ → A) :=
  pairFactorMeasure (uniformIIDLaw (uniformSelectorLaw T h0 hsum)) uniformIIDCode

instance uniformSoficMeasure_probability (T : A → Module.End ℝ (Q → ℝ))
    (h0 : ∀ a i j, 0 ≤ endEntry (T a) i j) (hsum : ∑ a, T a = uniformMean) :
    IsProbabilityMeasure (uniformSoficMeasure T h0 hsum) := by
  unfold uniformSoficMeasure
  infer_instance

theorem uniformSoficMeasure_stationary (T : A → Module.End ℝ (Q → ℝ))
    (h0 : ∀ a i j, 0 ≤ endEntry (T a) i j) (hsum : ∑ a, T a = uniformMean) :
    MeasurePreserving sequenceShift (uniformSoficMeasure T h0 hsum)
      (uniformSoficMeasure T h0 hsum) := pairFactorMeasure_stationary _ _

theorem uniformSoficMeasure_cylinder (T : A → Module.End ℝ (Q → ℝ))
    (h0 : ∀ a i j, 0 ≤ endEntry (T a) i j) (hsum : ∑ a, T a = uniformMean)
    (w : List A) :
    (uniformSoficMeasure T h0 hsum).real (wordCylinder w) =
      representedWord T averageRow (fun _ => 1) w := by
  rw [uniformSoficMeasure, pairFactorMeasure_cylinder]
  simp only [representedWord, iidRow_uniform, selectorCollapse_word, selectorCollapse_ones]

end SoficMarkovOrder
