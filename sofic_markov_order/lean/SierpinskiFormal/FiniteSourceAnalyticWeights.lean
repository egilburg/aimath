import SierpinskiFormal.BernoulliWeightNormalization

/-! # Analytic normalization of finite-state source parameters

Allowed outgoing edges are fixed; every row of positive edge weights is
normalized separately. The induced IID selector law is analytic on this
open parameter domain. No claim is made across changes of support.
-/

noncomputable section
open scoped BigOperators Topology

namespace IndependentZeroBlocks

theorem analyticAt_normalizedRealWeights {A : Type*} [Fintype A]
    (p : A → ℝ) (hp : ∑ a, p a ≠ 0) :
    AnalyticAt ℝ normalizedRealWeights p := by
  apply AnalyticAt.pi
  intro a
  apply ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : A ↦ ℝ) a).analyticAt p).fun_div
  · have hb (b : A) : AnalyticAt ℝ (fun i : A → ℝ ↦ i b) p :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : A ↦ ℝ) b).analyticAt p
    convert! Finset.analyticAt_sum Finset.univ (fun b _ ↦ hb b) using 1
    funext i
    simp only [Finset.sum_apply]
  · exact hp

variable {Q : Type*} [Fintype Q] {E : Q → Type*}
  [∀ q, Fintype (E q)] [∀ q, Nonempty (E q)]

/- Mathlib provides finiteness, but not a `Fintype` instance, for a dependent
finite product.  The analytic selector map needs the concrete instance. -/
local instance selectorIndexDecidableEq : DecidableEq Q :=
  Classical.decEq Q

local instance selectorFintype : Fintype ((q : Q) → E q) :=
  Pi.instFintype

/-- Normalize positive outgoing weights at each state separately. -/
def normalizedSourceWeights (p : (q : Q) → E q → ℝ) : (q : Q) → E q → ℝ :=
  fun q ↦ normalizedRealWeights (p q)

theorem normalizedSourceWeights_pos
    (p : (q : Q) → E q → ℝ) (hp : ∀ q e, 0 < p q e) (q : Q) (e : E q) :
    0 < normalizedSourceWeights p q e :=
  normalizedRealWeights_pos (p q) (hp q) e

theorem sum_normalizedSourceWeights
    (p : (q : Q) → E q → ℝ) (hp : ∀ q e, 0 < p q e) (q : Q) :
    ∑ e, normalizedSourceWeights p q e = 1 :=
  sum_normalizedRealWeights (p q) (hp q)

theorem normalizedSourceWeights_eq_self
    (p : (q : Q) → E q → ℝ) (hp : ∀ q, ∑ e, p q e = 1) :
    normalizedSourceWeights p = p := by
  funext q
  exact normalizedRealWeights_eq_self (p q) (hp q)

theorem analyticAt_normalizedSourceWeights
    (p : (q : Q) → E q → ℝ) (hp : ∀ q e, 0 < p q e) :
    AnalyticAt ℝ normalizedSourceWeights p := by
  apply AnalyticAt.pi
  intro q
  exact (analyticAt_normalizedRealWeights (p q) (ne_of_gt (totalWeight_pos (p q) (hp q)))).comp
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun q : Q ↦ E q → ℝ) q).analyticAt p)

/-- Polynomial selector weight for an arbitrary family of outgoing weights. -/
def sourceSelectorWeights (p : (q : Q) → E q → ℝ) (f : (q : Q) → E q) : ℝ :=
  ∏ q, p q (f q)

theorem analyticAt_sourceSelectorWeights (p : (q : Q) → E q → ℝ) :
    AnalyticAt ℝ sourceSelectorWeights p := by
  apply AnalyticAt.pi
  intro f
  apply Finset.analyticAt_fun_prod Finset.univ
  intro q _
  exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : E q ↦ ℝ) (f q)).analyticAt
    (p q)).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun q : Q ↦ E q → ℝ) q).analyticAt p)

theorem analyticAt_normalizedSourceSelectorWeights
    (p : (q : Q) → E q → ℝ) (hp : ∀ q e, 0 < p q e) :
    AnalyticAt ℝ (fun u ↦ sourceSelectorWeights (normalizedSourceWeights u)) p :=
  (analyticAt_sourceSelectorWeights (normalizedSourceWeights p)).comp
    (analyticAt_normalizedSourceWeights p hp)

end IndependentZeroBlocks
