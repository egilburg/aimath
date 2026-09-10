import SierpinskiFormal.StationarySourceBridge
import Mathlib.Probability.Independence.InfinitePi

/-!
# Canonical IID measures on a finite alphabet

This file turns nonnegative finite probability weights into the corresponding
atomic one-letter measure and its infinite product on one-sided sequences.
It also records the shift invariance and finite-coordinate marginal needed by
the strong-law interface.
-/

noncomputable section

open Function MeasureTheory
open scoped BigOperators ENNReal

namespace IndependentZeroBlocks

/-- A probability vector on a finite alphabet, kept in real coordinates for
compatibility with the existing weighted-word API. -/
structure FiniteProbabilityWeights (A : Type*) [Fintype A] where
  weight : A → ℝ
  nonneg : ∀ a, 0 ≤ weight a
  sum_eq_one : ∑ a, weight a = 1

namespace FiniteProbabilityWeights

variable {A : Type*} [Fintype A]

/-- The atomic one-letter law associated to finite probability weights. -/
def letterMeasure (L : FiniteProbabilityWeights A) [MeasurableSpace A] : Measure A :=
  ∑ a, ENNReal.ofReal (L.weight a) • Measure.dirac a

instance letterMeasure.instIsProbabilityMeasure (L : FiniteProbabilityWeights A)
    [MeasurableSpace A] : IsProbabilityMeasure L.letterMeasure where
  measure_univ := by
    rw [letterMeasure]
    change (∑ a ∈ Finset.univ,
      ENNReal.ofReal (L.weight a) • Measure.dirac a) Set.univ = 1
    rw [Measure.finsetSum_apply]
    simp only [Measure.smul_apply,
      Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ ↦ L.nonneg a), L.sum_eq_one]
    simp

/-- The canonical one-sided IID law associated to finite probability weights. -/
def iidMeasure (L : FiniteProbabilityWeights A) [MeasurableSpace A] : Measure (ℕ → A) :=
  Measure.infinitePi (fun _ : ℕ ↦ L.letterMeasure)

instance iidMeasure.instIsProbabilityMeasure (L : FiniteProbabilityWeights A)
    [MeasurableSpace A] : IsProbabilityMeasure L.iidMeasure := by
  unfold iidMeasure
  infer_instance

@[simp] theorem letterMeasure_singleton [DecidableEq A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (L : FiniteProbabilityWeights A) (a : A) :
    L.letterMeasure {a} = ENNReal.ofReal (L.weight a) := by
  rw [letterMeasure]
  change (∑ b ∈ Finset.univ,
    ENNReal.ofReal (L.weight b) • Measure.dirac b) {a} = _
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hba
    simp [hba]
  · simp

@[simp] theorem letterMeasure_singleton_real [DecidableEq A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (L : FiniteProbabilityWeights A) (a : A) :
    L.letterMeasure.real {a} = L.weight a := by
  rw [Measure.real, letterMeasure_singleton, ENNReal.toReal_ofReal (L.nonneg a)]

/-- The IID law is invariant under the accepted canonical left shift. -/
theorem measurePreserving_digitShift_iidMeasure [MeasurableSpace A]
    (L : FiniteProbabilityWeights A) :
    MeasurePreserving digitShift L.iidMeasure L.iidMeasure := by
  refine ⟨measurable_digitShift, ?_⟩
  change (Measure.infinitePi (fun _ : ℕ ↦ L.letterMeasure)).map
      (fun ω n ↦ ω (Nat.succ n)) =
    Measure.infinitePi (fun _ : ℕ ↦ L.letterMeasure)
  simpa only using
    (Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : ℕ ↦ L.letterMeasure) Nat.succ_injective)

/-- The first `n` coordinates of the infinite IID law have the finite product
law. This is derived from `Measure.infinitePi`, rather than assumed. -/
theorem map_iidMeasure_firstCoordinates [MeasurableSpace A]
    (L : FiniteProbabilityWeights A) (n : ℕ) :
    L.iidMeasure.map (fun ω (i : Fin n) ↦ ω i.val) =
      Measure.infinitePi (fun _ : Fin n ↦ L.letterMeasure) := by
  simpa only [iidMeasure] using
    (Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : ℕ ↦ L.letterMeasure) Fin.val_injective)

end FiniteProbabilityWeights

end IndependentZeroBlocks
