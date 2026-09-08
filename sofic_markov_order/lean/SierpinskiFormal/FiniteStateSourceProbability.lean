import SierpinskiFormal.FiniteIIDWordLaw
import SierpinskiFormal.FiniteStateSourceLaw
import SierpinskiFormal.StationaryBooleanFrequency

/-! # A canonical path measure for finite-state sources

The source is driven by independent simultaneous edge selectors. The exact
integral theorem identifies this constructed process with the accepted
edge-recursive expectation, including all prefix lengths and Boolean events.
-/

noncomputable section
open Filter Set MeasureTheory Topology
open scoped BigOperators

namespace IndependentZeroBlocks
namespace FiniteStateSource

variable {Q A : Type*} [Fintype Q]

/-- Use the full measurable structure on the finite selector alphabet. -/
@[instance_reducible] def selectorMeasurableSpace (S : FiniteStateSource Q A) :
    MeasurableSpace S.Selector := ⊤

attribute [local instance] selectorMeasurableSpace

/-- Use the discrete topology on the finite selector alphabet. -/
@[instance_reducible] def selectorTopologicalSpace (S : FiniteStateSource Q A) :
    TopologicalSpace S.Selector := ⊥

attribute [local instance] selectorTopologicalSpace

instance selectorMeasurableSingletonClass (S : FiniteStateSource Q A) :
    @MeasurableSingletonClass S.Selector S.selectorMeasurableSpace := ⟨fun _ ↦ trivial⟩

instance selectorDiscreteTopology (S : FiniteStateSource Q A) :
    @DiscreteTopology S.Selector S.selectorTopologicalSpace := ⟨rfl⟩

/-- Normalized nonnegative outgoing rows give a genuine selector probability
vector. This construction allows zero weights. -/
def selectorProbabilityWeights (S : FiniteStateSource Q A)
    (p : (q : Q) → S.Edge q → ℝ)
    (hp0 : ∀ q e, 0 ≤ p q e) (hp1 : ∀ q, ∑ e, p q e = 1) :
    FiniteProbabilityWeights S.Selector where
  weight := sourceSelectorWeights p
  nonneg f := Finset.prod_nonneg fun q _ ↦ hp0 q (f q)
  sum_eq_one := S.sum_selectorWeight_eq_one p hp1

/-- The selector law associated with positive raw edge parameters. -/
def normalizedSelectorLaw (S : FiniteStateSource Q A)
    (p : (q : Q) → S.Edge q → ℝ) (hp : ∀ q e, 0 < p q e) :
    FiniteProbabilityWeights S.Selector :=
  S.selectorProbabilityWeights (normalizedSourceWeights p)
    (fun q e ↦ (normalizedSourceWeights_pos p hp q e).le)
    (sum_normalizedSourceWeights p hp)

/-- The emitted chronological prefix along a single selector path. -/
def pathPrefix (S : FiniteStateSource Q A) (q : Q) (n : ℕ)
    (ω : ℕ → S.Selector) : List A :=
  S.transducer.outputWord q (stationaryPrefix digitHead digitShift n ω)

@[simp] theorem pathPrefix_zero (S : FiniteStateSource Q A)
    (q : Q) (ω : ℕ → S.Selector) : S.pathPrefix q 0 ω = [] := rfl

/-- The sampled path chooses only the current state's outgoing edge. -/
@[simp] theorem pathPrefix_succ (S : FiniteStateSource Q A)
    (q : Q) (n : ℕ) (ω : ℕ → S.Selector) :
    S.pathPrefix q (n + 1) ω = S.label q (ω 0 q) ::
      S.pathPrefix (S.target q (ω 0 q)) n (digitShift ω) := rfl

/-- Prefix frequency of an event on the actual emitted path. -/
def pathFrequency (S : FiniteStateSource Q A) (q : Q) (event : List A → Bool)
    (N : ℕ) (ω : ℕ → S.Selector) : ℝ :=
  realCesaroMean (fun n ↦ boolIndicator (event (S.pathPrefix q n ω))) N

theorem pathFrequency_eq_stationary (S : FiniteStateSource Q A)
    (q : Q) (event : List A → Bool) (N : ℕ) (ω : ℕ → S.Selector) :
    S.pathFrequency q event N ω =
      stationaryBooleanFrequency digitHead digitShift
        (fun w ↦ event (S.transducer.outputWord q w)) N ω := rfl

/-- All finite-prefix integrals agree with the edge-by-edge source law. -/
theorem integral_pathPrefix (S : FiniteStateSource Q A)
    (p : (q : Q) → S.Edge q → ℝ)
    (hp0 : ∀ q e, 0 ≤ p q e) (hp1 : ∀ q, ∑ e, p q e = 1)
    (F : List A → ℝ) (q : Q) (n : ℕ) :
    (∫ ω, F (S.pathPrefix q n ω) ∂(S.selectorProbabilityWeights p hp0 hp1).iidMeasure) =
      S.sourceExpectation p F q n := by
  rw [S.sourceExpectation_eq_selector_tuple_sum p hp1 F q n]
  exact (S.selectorProbabilityWeights p hp0 hp1).integral_comp_stationaryPrefix_digit
    n (fun w ↦ F (S.transducer.outputWord q w))

theorem integrable_pathPrefix (S : FiniteStateSource Q A)
    (p : (q : Q) → S.Edge q → ℝ)
    (hp0 : ∀ q e, 0 ≤ p q e) (hp1 : ∀ q, ∑ e, p q e = 1)
    (F : List A → ℝ) (q : Q) (n : ℕ) :
    Integrable (fun ω ↦ F (S.pathPrefix q n ω))
      (S.selectorProbabilityWeights p hp0 hp1).iidMeasure :=
  (S.selectorProbabilityWeights p hp0 hp1).integrable_comp_stationaryPrefix_digit
    n (fun w ↦ F (S.transducer.outputWord q w))

/-- Expected path frequencies are exactly the accepted source Cesàro means. -/
theorem integral_pathFrequency (S : FiniteStateSource Q A)
    (p : (q : Q) → S.Edge q → ℝ)
    (hp0 : ∀ q e, 0 ≤ p q e) (hp1 : ∀ q, ∑ e, p q e = 1)
    (event : List A → Bool) (q : Q) (N : ℕ) :
    (∫ ω, S.pathFrequency q event N ω ∂(S.selectorProbabilityWeights p hp0 hp1).iidMeasure) =
      realCesaroMean (S.sourceExpectation p (fun w ↦ boolIndicator (event w)) q) N := by
  simp only [pathFrequency, realCesaroMean]
  rw [integral_div, integral_finsetSum]
  · congr 1
    apply Finset.sum_congr rfl
    intro n _
    exact S.integral_pathPrefix p hp0 hp1 (fun w ↦ boolIndicator (event w)) q n
  · intro n _
    exact S.integrable_pathPrefix p hp0 hp1 (fun w ↦ boolIndicator (event w)) q n

end FiniteStateSource
end IndependentZeroBlocks
