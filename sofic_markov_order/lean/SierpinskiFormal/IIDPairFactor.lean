import SierpinskiFormal.FiniteIIDWordLaw
import SierpinskiFormal.SoficProcessMarkov

set_option autoImplicit false
noncomputable section
namespace IndependentZeroBlocks
open MeasureTheory
open scoped BigOperators

variable {A B : Type*}

def pairOutput (code : B → B → A) : List B → List A
  | [] => []
  | [_] => []
  | b :: c :: w => code b c :: pairOutput code (c :: w)

def pairProcess (code : B → B → A) (ω : ℕ → B) (n : ℕ) : A := code (ω n) (ω (n+1))

theorem pairProcess_shift (code : B → B → A) :
    pairProcess code ∘ digitShift = digitShift ∘ pairProcess code := rfl

theorem pairOutput_prefix (code : B → B → A) (n : ℕ) (ω : ℕ → B) :
    pairOutput code (stationaryPrefix digitHead digitShift (n+1) ω) =
      stationaryPrefix digitHead digitShift n (pairProcess code ω) := by
  induction n generalizing ω with
  | zero => rfl
  | succ n ih =>
      change code (ω 0) (ω 1) :: pairOutput code
        (stationaryPrefix digitHead digitShift (n+1) (digitShift ω)) = _
      rw [ih]
      rfl

theorem mem_wordCylinder_iff_prefix (w : List A) (ω : ℕ → A) :
    ω ∈ wordCylinder w ↔ stationaryPrefix digitHead digitShift w.length ω = w := by
  induction w generalizing ω with
  | nil => simp [wordCylinder, stationaryPrefix]
  | cons a w ih =>
      change (ω 0 = a ∧ digitShift ω ∈ wordCylinder w) ↔
        ω 0 :: stationaryPrefix digitHead digitShift w.length (digitShift ω) = a :: w
      rw [List.cons.injEq, ih]

variable [Fintype B] [MeasurableSpace B] [MeasurableSingletonClass B]
  [MeasurableSpace A] [MeasurableSingletonClass A]

theorem measurable_pairProcess (code : B → B → A) : Measurable (pairProcess code) := by
  apply measurable_pi_lambda
  intro n
  change Measurable (fun ω : ℕ → B => code (ω n) (ω (n+1)))
  have hm : Measurable (fun ω : ℕ → B => (ω n, ω (n+1))) :=
    (measurable_pi_apply n).prodMk (measurable_pi_apply (n+1))
  exact (measurable_of_countable (fun bc : B × B => code bc.1 bc.2)).comp hm

def pairFactorMeasure (L : FiniteProbabilityWeights B) (code : B → B → A) :
    Measure (ℕ → A) := L.iidMeasure.map (pairProcess code)

instance pairFactorMeasure_probability (L : FiniteProbabilityWeights B) (code : B → B → A) :
    IsProbabilityMeasure (pairFactorMeasure L code) :=
  Measure.isProbabilityMeasure_map (measurable_pairProcess code).aemeasurable

theorem pairFactorMeasure_stationary (L : FiniteProbabilityWeights B) (code : B → B → A) :
    MeasurePreserving digitShift (pairFactorMeasure L code) (pairFactorMeasure L code) := by
  refine ⟨measurable_digitShift, ?_⟩
  unfold pairFactorMeasure
  rw [Measure.map_map measurable_digitShift (measurable_pairProcess code),
    ← pairProcess_shift, ← Measure.map_map (measurable_pairProcess code) measurable_digitShift,
    L.measurePreserving_digitShift_iidMeasure.map_eq]

variable [DecidableEq A] [DecidableEq B]

def pairLetter (L : FiniteProbabilityWeights B) (code : B → B → A) (a : A) :
    Module.End ℝ (B → ℝ) := LinearMap.pi fun b =>
      ∑ c : B, (if code b c = a then L.weight c else 0) • LinearMap.proj c

omit [MeasurableSpace B] [MeasurableSingletonClass B]
  [MeasurableSpace A] [MeasurableSingletonClass A] in
@[simp] theorem pairLetter_apply (L : FiniteProbabilityWeights B) (code : B → B → A)
    (a : A) (x : B → ℝ) (b : B) :
    pairLetter L code a x b = ∑ c, L.weight c * (if code b c = a then x c else 0) := by
  simp only [pairLetter, LinearMap.pi_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs <;> simp_all

def iidRow (L : FiniteProbabilityWeights B) : Module.Dual ℝ (B → ℝ) :=
  ∑ b : B, L.weight b • LinearMap.proj b

omit [MeasurableSpace B] [MeasurableSingletonClass B]
  [MeasurableSpace A] [MeasurableSingletonClass A] in
@[simp] theorem iidRow_apply (L : FiniteProbabilityWeights B) (x : B → ℝ) :
    iidRow L x = ∑ b, L.weight b * x b := by
  simp [iidRow, LinearMap.sum_apply]

omit [MeasurableSpace B] [MeasurableSingletonClass B]
  [MeasurableSpace A] [MeasurableSingletonClass A] in
theorem pair_tail_sum (L : FiniteProbabilityWeights B) (code : B → B → A)
    (w : List A) (b : B) :
    (∑ v : Fin w.length → B, wordWeight L.weight (List.ofFn v) *
      (if pairOutput code (b :: List.ofFn v) = w then 1 else 0)) =
      linearWord (pairLetter L code) w (fun _ => 1) b := by
  induction w generalizing b with
  | nil => simp [pairOutput, wordWeight, linearWord]
  | cons a w ih =>
      simp only [List.length_cons]
      rw [Fintype.sum_equiv (finSuccTupleEquiv w.length)
        (fun v => wordWeight L.weight (List.ofFn v) *
          (if pairOutput code (b :: List.ofFn v) = a :: w then 1 else 0))
        (fun cv : B × (Fin w.length → B) => L.weight cv.1 *
          (wordWeight L.weight (List.ofFn cv.2) *
            (if code b cv.1 = a ∧ pairOutput code (cv.1 :: List.ofFn cv.2) = w
              then 1 else 0))) (by
          intro v
          by_cases h₁ : code b (v 0) = a <;>
            by_cases h₂ : pairOutput code (v 0 :: List.ofFn (fun i => v i.succ)) = w <;>
            simp [List.ofFn_succ, finSuccTupleEquiv, pairOutput, wordWeight,
              mul_assoc, h₁, h₂])]
      rw [Fintype.sum_prod_type, linearWord_cons, Module.End.mul_apply, pairLetter_apply]
      apply Finset.sum_congr rfl
      intro c _
      simp only [Prod.fst, Prod.snd]
      rw [← Finset.mul_sum]
      congr 1
      by_cases hc : code b c = a
      · simpa [hc] using ih c
      · simp [hc]

omit [MeasurableSpace B] [MeasurableSingletonClass B]
  [MeasurableSpace A] [MeasurableSingletonClass A] in
theorem pair_full_sum (L : FiniteProbabilityWeights B) (code : B → B → A) (w : List A) :
    (∑ v : Fin (w.length+1) → B, wordWeight L.weight (List.ofFn v) *
      (if pairOutput code (List.ofFn v) = w then 1 else 0)) =
      representedWord (pairLetter L code) (iidRow L) (fun _ => 1) w := by
  rw [Fintype.sum_equiv (finSuccTupleEquiv w.length)
    (fun v => wordWeight L.weight (List.ofFn v) *
      (if pairOutput code (List.ofFn v) = w then 1 else 0))
    (fun cv : B × (Fin w.length → B) => L.weight cv.1 *
      (wordWeight L.weight (List.ofFn cv.2) *
        (if pairOutput code (cv.1 :: List.ofFn cv.2) = w then 1 else 0))) (by
      intro v
      simp [List.ofFn_succ, finSuccTupleEquiv, wordWeight, mul_assoc, mul_ite]
      <;> split_ifs <;> simp_all)]
  rw [Fintype.sum_prod_type]
  simp only [Prod.fst, Prod.snd, representedWord, iidRow_apply, ← Finset.mul_sum, pair_tail_sum]

theorem pairFactorMeasure_cylinder (L : FiniteProbabilityWeights B) (code : B → B → A)
    (w : List A) :
    (pairFactorMeasure L code).real (wordCylinder w) =
      representedWord (pairLetter L code) (iidRow L) (fun _ => 1) w := by
  have hset : pairProcess code ⁻¹' wordCylinder w =
      {ω | pairOutput code (stationaryPrefix digitHead digitShift (w.length+1) ω) = w} := by
    ext ω
    rw [Set.mem_preimage, mem_wordCylinder_iff_prefix, Set.mem_setOf_eq, pairOutput_prefix]
  rw [pairFactorMeasure, Measure.real, Measure.map_apply (measurable_pairProcess code)
    (measurableSet_wordCylinder w)]
  change L.iidMeasure.real (pairProcess code ⁻¹' wordCylinder w) = _
  rw [← integral_indicator_one (measurableSet_wordCylinder w |>.preimage
    (measurable_pairProcess code))]
  change (∫ ω, (pairProcess code ⁻¹' wordCylinder w).indicator (fun _ => (1 : ℝ)) ω
    ∂L.iidMeasure) = _
  simp only [hset, Set.indicator_apply, Set.mem_setOf_eq]
  rw [L.integral_comp_stationaryPrefix_digit (w.length+1)
    (fun v => if pairOutput code v = w then (1 : ℝ) else 0)]
  exact pair_full_sum L code w

end IndependentZeroBlocks
