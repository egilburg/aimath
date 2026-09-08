import SoficMarkovOrder.StationaryWordLaw
import SoficMarkovOrder.SequenceSpace
import Mathlib.MeasureTheory.Measure.Real

set_option autoImplicit false

/-!
# The binomial cutoff for actual stationary process laws

Cylinder events are defined on the canonical one-sided sequence space. The
Markov condition compares ordinary event conditional probabilities on all
positive-mass histories, for every finite future block.
-/

namespace SoficMarkovOrder
open MeasureTheory
open scoped BigOperators

variable {A : Type*}

/-- The event that the chronological prefix equals a specified finite word. -/
def wordCylinder : List A → Set (ℕ → A)
  | [] => Set.univ
  | a :: w => {ω | ω 0 = a} ∩ sequenceShift ⁻¹' wordCylinder w

theorem measurableSet_wordCylinder [MeasurableSpace A] [MeasurableSingletonClass A]
    (w : List A) : MeasurableSet (wordCylinder w) := by
  induction w with
  | nil => exact MeasurableSet.univ
  | cons a w ih =>
      exact ((measurableSet_singleton a).preimage (measurable_pi_apply 0)).inter
        (ih.preimage measurable_sequenceShift)

theorem iUnion_wordCylinder_append (w : List A) :
    (⋃ a : A, wordCylinder (w ++ [a])) = wordCylinder w := by
  induction w with
  | nil => ext ω; simp [wordCylinder]
  | cons b w ih =>
      simp only [List.cons_append, wordCylinder]
      rw [← Set.inter_iUnion, ← Set.preimage_iUnion, ih]

theorem iUnion_wordCylinder_cons (w : List A) :
    (⋃ a : A, wordCylinder (a :: w)) = sequenceShift ⁻¹' wordCylinder w := by
  ext ω
  simp [wordCylinder]

theorem pairwise_disjoint_wordCylinder_cons (w : List A) :
    Pairwise (fun a b => Disjoint (wordCylinder (a :: w)) (wordCylinder (b :: w))) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  intro ω ha hb
  exact hab (ha.1.symm.trans hb.1)

theorem pairwise_disjoint_wordCylinder_append (w : List A) :
    Pairwise (fun a b => Disjoint (wordCylinder (w ++ [a])) (wordCylinder (w ++ [b]))) := by
  induction w with
  | nil => exact pairwise_disjoint_wordCylinder_cons []
  | cons c w ih =>
      intro a b hab
      apply Set.disjoint_left.mpr
      intro ω ha hb
      exact Set.disjoint_left.mp (ih hab) ha.2 hb.2

/-- Every stationary sequence probability measure gives a stationary cylinder law. -/
noncomputable def stationaryCylinderLaw [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (μ : Measure (ℕ → A)) [IsProbabilityMeasure μ]
    (hstationary : MeasurePreserving sequenceShift μ μ) : StationaryWordLaw A where
  mass w := μ.real (wordCylinder w)
  nonneg _ := measureReal_nonneg
  mass_nil := by simp [wordCylinder]
  sum_append w := by
    rw [← measureReal_iUnion_fintype (pairwise_disjoint_wordCylinder_append w)
      (fun a => measurableSet_wordCylinder (w ++ [a])), iUnion_wordCylinder_append]
  sum_prepend w := by
    rw [← measureReal_iUnion_fintype (pairwise_disjoint_wordCylinder_cons w)
      (fun a => measurableSet_wordCylinder (a :: w)), iUnion_wordCylinder_cons]
    exact hstationary.measureReal_preimage (measurableSet_wordCylinder w).nullMeasurableSet

/-- Finite-history Markovity of an actual process, expressed by event conditional
probabilities. This definition makes no reference to a matrix representation. -/
def ProcessMarkov [MeasurableSpace A] (μ : Measure (ℕ → A)) (k : ℕ) : Prop :=
  ∀ u v z : List A, v.length = k → 0 < μ.real (wordCylinder (u ++ v)) →
    μ.real (wordCylinder (u ++ v ++ z)) / μ.real (wordCylinder (u ++ v)) =
      μ.real (wordCylinder (v ++ z)) / μ.real (wordCylinder v)

/-- The stochastic rank criterion follows from cylinder consistency and reducedness. -/
theorem processMarkov_iff_rankOne [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (μ : Measure (ℕ → A)) [IsProbabilityMeasure μ]
    (hstationary : MeasurePreserving sequenceShift μ μ)
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (T : A → Module.End ℝ V) (l : Module.Dual ℝ V) (g : V)
    (hrep : ∀ w, μ.real (wordCylinder w) = representedWord T l g w)
    (hr : WordReduced T l g) (k : ℕ) :
    ProcessMarkov μ k ↔
      ∀ v : List A, v.length = k → Module.finrank ℝ (linearWord T v).range ≤ 1 := by
  exact (stationaryCylinderLaw μ hstationary).conditionalMarkov_iff_rankOne
    T l g (funext hrep) hr k

/-- A stationary finite-dimensional process of finite Markov order has order
at most the binomial coefficient of its intrinsic real Hankel dimension. -/
theorem stationary_process_markov_cutoff_hankel [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (μ : Measure (ℕ → A)) [IsProbabilityMeasure μ]
    (hstationary : MeasurePreserving sequenceShift μ μ)
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (T : A → Module.End ℝ V) (l : Module.Dual ℝ V) (g : V)
    (hrep : ∀ w, μ.real (wordCylinder w) = representedWord T l g w)
    (hr : WordReduced T l g) (hfinite : ∃ k, ProcessMarkov μ k) :
    ProcessMarkov μ ((Module.finrank ℝ
      (wordHankelSpan (fun w => μ.real (wordCylinder w)))).choose 2) := by
  exact (stationaryCylinderLaw μ hstationary).conditionalMarkov_cutoff_hankel
    T l g (funext hrep) hr hfinite

end SoficMarkovOrder
