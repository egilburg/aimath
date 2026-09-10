import SierpinskiFormal.BlockTransformExpectations
import SierpinskiFormal.SourceScalarWordAtomicLaw

/-! # Analytic branches and exact mixed moments for finite-state sources -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter MeasureTheory Set Topology
open scoped BigOperators
namespace IndependentZeroBlocks
namespace FiniteStateSource

attribute [local instance] selectorMeasurableSpace selectorTopologicalSpace
variable {Q A J : Type*} [Fintype Q] [DecidableEq Q] [Fintype J]

def sourceBlockBranch (S : FiniteStateSource Q A) (h : List S.Selector)
    (m : BlockBranchCoefficients h)
    (hm : ∀ s ξ u v, (m s ξ u v : ℝ) ∈ Icc (0 : ℝ) 1)
    (p : (r : Q) → S.Edge r → ℝ) (u : GapWords (endoMarkerBlock h)) : ℝ :=
  normalizedBlockBranch h m hm (sourceSelectorWeights (normalizedSourceWeights p)) u

def sourceBlockMixedMoment (S : FiniteStateSource Q A) (h : List S.Selector)
    (m : J → BlockBranchCoefficients h)
    (hm : ∀ j s ξ u v, (m j s ξ u v : ℝ) ∈ Icc (0 : ℝ) 1)
    (k : J → ℕ) (p : (r : Q) → S.Edge r → ℝ) : ℝ :=
  normalizedBlockMixedMoment h m hm k (sourceSelectorWeights (normalizedSourceWeights p))

theorem normalizedSelectorLaw_pos (S : FiniteStateSource Q A)
    (p : (r : Q) → S.Edge r → ℝ) (hp : ∀ r e, 0 < p r e) :
    ∀ a, 0 < (S.normalizedSelectorLaw p hp).weight a :=
  S.selectorWeight_pos _ (normalizedSourceWeights_pos p hp)

theorem sourceBlockBranch_eq (S : FiniteStateSource Q A) (h : List S.Selector)
    (m : BlockBranchCoefficients h)
    (hm : ∀ s ξ u v, (m s ξ u v : ℝ) ∈ Icc (0 : ℝ) 1)
    (p : (r : Q) → S.Edge r → ℝ) (hp : ∀ r e, 0 < p r e)
    (u : GapWords (endoMarkerBlock h)) :
    S.sourceBlockBranch h m hm p u =
      blockMarkerBranch h.length (endoMarkerBlock h) m (S.normalizedSelectorLaw p hp).weight u := by
  unfold sourceBlockBranch
  change normalizedBlockBranch h m hm (S.normalizedSelectorLaw p hp).weight u = _
  rw [normalizedBlockBranch_eq h m hm _ (S.normalizedSelectorLaw_pos p hp),
    normalizedRealWeights_eq_self _ (S.normalizedSelectorLaw p hp).sum_eq_one]

theorem analyticAt_sourceBlockBranch (S : FiniteStateSource Q A) (h : List S.Selector)
    (m : BlockBranchCoefficients h)
    (hm : ∀ s ξ u v, (m s ξ u v : ℝ) ∈ Icc (0 : ℝ) 1)
    (p : (r : Q) → S.Edge r → ℝ) (hp : ∀ r e, 0 < p r e)
    (u : GapWords (endoMarkerBlock h)) :
    AnalyticAt ℝ (fun z ↦ S.sourceBlockBranch h m hm z u) p := by
  exact (analyticAt_normalizedBlockBranch h m hm _ (S.normalizedSelectorLaw_pos p hp) u).comp
    (f := fun z ↦ sourceSelectorWeights (normalizedSourceWeights z))
    (x := p) (analyticAt_normalizedSourceSelectorWeights p hp)

theorem analyticAt_sourceBlockMixedMoment (S : FiniteStateSource Q A) (h : List S.Selector)
    (m : J → BlockBranchCoefficients h)
    (hm : ∀ j s ξ u v, (m j s ξ u v : ℝ) ∈ Icc (0 : ℝ) 1)
    (k : J → ℕ) (p : (r : Q) → S.Edge r → ℝ) (hp : ∀ r e, 0 < p r e) :
    AnalyticAt ℝ (S.sourceBlockMixedMoment h m hm k) p :=
  (analyticAt_normalizedBlockMixedMoment h m hm k _ (S.normalizedSelectorLaw_pos p hp)).comp
    (f := fun z ↦ sourceSelectorWeights (normalizedSourceWeights z))
    (x := p) (analyticAt_normalizedSourceSelectorWeights p hp)

theorem normalizedIIDLaw_selector_eq (S : FiniteStateSource Q A)
    (p : (r : Q) → S.Edge r → ℝ) (hp : ∀ r e, 0 < p r e) :
    normalizedIIDLaw (S.normalizedSelectorLaw p hp).weight
      (S.normalizedSelectorLaw_pos p hp) = S.normalizedSelectorLaw p hp := by
  have hgen (P : FiniteProbabilityWeights S.Selector) (hP : ∀ a, 0 < P.weight a) :
      normalizedIIDLaw P.weight hP = P := by
    cases P with
    | mk w hn hs =>
      unfold normalizedIIDLaw
      congr 1
      exact normalizedRealWeights_eq_self w hs
  exact hgen _ _

/-- All mixed moments of any finite collection sharing this marker are
exactly the analytic expressions above, evaluated on the actual selector path. -/
theorem sourceBlockMixedMoment_eq_integral (S : FiniteStateSource Q A)
    (h : List S.Selector) (hh : h ≠ []) (m : J → BlockBranchCoefficients h)
    (hm : ∀ j s ξ u v, (m j s ξ u v : ℝ) ∈ Icc (0 : ℝ) 1)
    (k : J → ℕ) (p : (r : Q) → S.Edge r → ℝ) (hp : ∀ r e, 0 < p r e) :
    S.sourceBlockMixedMoment h m hm k p =
      ∫ ω, ∏ j, S.sourceBlockBranch h (m j) (hm j) p
        (initialMarkerGap (endoMarkerBlock h) (iidBlockPath h.length ω)) ^ k j
        ∂(S.normalizedSelectorLaw p hp).iidMeasure := by
  have hmoment := normalizedBlockMixedMoment_eq_integral h hh m hm k _
    (S.normalizedSelectorLaw_pos p hp)
  rw [S.normalizedIIDLaw_selector_eq p hp] at hmoment
  exact hmoment

end FiniteStateSource
end IndependentZeroBlocks
