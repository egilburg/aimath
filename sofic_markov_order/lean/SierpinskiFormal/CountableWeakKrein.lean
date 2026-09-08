import SierpinskiFormal.WeakContinuousMapConvergence
import SierpinskiFormal.KreinWeakHullReduction
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# A state-space route toward Krein compactness for countable weak compacta

The intended application has a countable compact Hausdorff parameter space
`X` and a bounded map `j : X → E` which is continuous after applying every
continuous linear functional on `E`.
-/

noncomputable section

open Set Topology MeasureTheory
open scoped Topology

namespace IndependentZeroBlocks

section States

variable (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- Positive, normalized functionals on the real continuous functions on a
compact space, viewed with their weak-star topology. -/
def positiveNormalizedStates : Set (WeakDual ℝ C(X, ℝ)) :=
  {L | (∀ f : C(X, ℝ), 0 ≤ f → 0 ≤ L f) ∧ L 1 = 1}

omit [CompactSpace X] [T2Space X] in
theorem positiveNormalizedStates_pos
    {L : WeakDual ℝ C(X, ℝ)} (hL : L ∈ positiveNormalizedStates X)
    {f : C(X, ℝ)} (hf : 0 ≤ f) : 0 ≤ L f :=
  hL.1 f hf

omit [CompactSpace X] [T2Space X] in
theorem positiveNormalizedStates_one
    {L : WeakDual ℝ C(X, ℝ)} (hL : L ∈ positiveNormalizedStates X) :
    L 1 = 1 :=
  hL.2

omit [CompactSpace X] [T2Space X] in
theorem positiveNormalizedStates_mono
    {L : WeakDual ℝ C(X, ℝ)} (hL : L ∈ positiveNormalizedStates X)
    {f g : C(X, ℝ)} (hfg : f ≤ g) : L f ≤ L g := by
  have hnonneg : 0 ≤ g - f := fun x ↦ sub_nonneg.mpr (hfg x)
  have := positiveNormalizedStates_pos X hL hnonneg
  simpa only [map_sub, sub_nonneg] using this

omit [T2Space X] in
theorem positiveNormalizedStates_norm_le_one [Nonempty X]
    {L : WeakDual ℝ C(X, ℝ)} (hL : L ∈ positiveNormalizedStates X) :
    ‖WeakDual.toStrongDual L‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  rw [one_mul, Real.norm_eq_abs, abs_le]
  constructor
  · calc
      -‖f‖ = L ((-‖f‖) • (1 : C(X, ℝ))) := by
        rw [map_smul, positiveNormalizedStates_one X hL]
        simp
      _ ≤ L f := positiveNormalizedStates_mono X hL (fun x ↦ by
        simpa using ContinuousMap.neg_norm_le_apply f x)
  · calc
      L f ≤ L (‖f‖ • (1 : C(X, ℝ))) :=
        positiveNormalizedStates_mono X hL (fun x ↦ by
          simpa using ContinuousMap.apply_le_norm f x)
      _ = ‖f‖ := by
        rw [map_smul, positiveNormalizedStates_one X hL]
        simp

omit [CompactSpace X] [T2Space X] in
theorem isClosed_positiveNormalizedStates :
    IsClosed (positiveNormalizedStates X) := by
  have hpos : IsClosed {L : WeakDual ℝ C(X, ℝ) |
      ∀ f : C(X, ℝ), 0 ≤ f → 0 ≤ L f} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun f ↦ isClosed_iInter fun _ ↦
      isClosed_Ici.preimage (WeakDual.eval_continuous f)
  have hone : IsClosed {L : WeakDual ℝ C(X, ℝ) | L 1 = 1} :=
    isClosed_eq (WeakDual.eval_continuous 1) continuous_const
  exact hpos.inter hone

omit [T2Space X] in
/-- The normalized positive state space is weak-star compact. -/
theorem isCompact_positiveNormalizedStates [Nonempty X] :
    IsCompact (positiveNormalizedStates X) := by
  apply (WeakDual.isCompact_closedBall (0 : StrongDual ℝ C(X, ℝ)) 1).of_isClosed_subset
    (isClosed_positiveNormalizedStates X)
  intro L hL
  show dist (WeakDual.toStrongDual L) 0 ≤ 1
  simpa using positiveNormalizedStates_norm_le_one X hL

end States

section RieszStates

open CompactlySupported CompactlySupportedContinuousMap

variable (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]

/-- The subtype of positive normalized weak-star functionals. -/
abbrev PositiveNormalizedState := positiveNormalizedStates X

/-- Restriction of a state to compactly supported continuous maps. -/
def stateLambda (L : PositiveNormalizedState X) : C_c(X, ℝ) →ₗ[ℝ] ℝ where
  toFun f := L.1 f.toContinuousMap
  map_add' f g := by
    change L.1 (f.toContinuousMap + g.toContinuousMap) = _
    exact map_add L.1 _ _
  map_smul' r f := by
    change L.1 (r • f.toContinuousMap) = r • L.1 f.toContinuousMap
    exact map_smul L.1 _ _

omit [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] in
theorem stateLambda_pos (L : PositiveNormalizedState X)
    (f : C_c(X, ℝ)) (hf : 0 ≤ f) : 0 ≤ stateLambda X L f := by
  exact L.2.1 f.toContinuousMap fun x ↦ hf x

/-- The Riesz measure represented by a positive normalized state. -/
def stateRieszMeasure (L : PositiveNormalizedState X) : Measure X :=
  RealRMK.rieszMeasure (PositiveLinearMap.mk₀ (stateLambda X L) (stateLambda_pos X L))

instance stateRieszMeasure_isFinite (L : PositiveNormalizedState X) :
    IsFiniteMeasure (stateRieszMeasure X L) :=
  IsFiniteMeasure.mk (by
    dsimp [stateRieszMeasure, RealRMK.rieszMeasure]
    rw [Content.measure_apply _ MeasurableSet.univ]
    exact Content.outerMeasure_lt_top_of_isCompact _ isCompact_univ)

/-- The Riesz measure reproduces the state on every continuous function. -/
theorem integral_stateRieszMeasure (L : PositiveNormalizedState X)
    (f : C(X, ℝ)) :
    ∫ x, f x ∂(stateRieszMeasure X L) = L.1 f := by
  let f' : C_c(X, ℝ) := CompactlySupportedContinuousMap.continuousMapEquiv f
  let LambdaPos : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
    PositiveLinearMap.mk₀ (stateLambda X L) (stateLambda_pos X L)
  calc
    ∫ x, f x ∂(stateRieszMeasure X L) = ∫ x, f' x ∂(stateRieszMeasure X L) := by rfl
    _ = LambdaPos f' := by
      simpa only [stateRieszMeasure, LambdaPos] using
        RealRMK.integral_rieszMeasure LambdaPos f'
    _ = L.1 f'.toContinuousMap := by rfl
    _ = L.1 f := congrArg L.1 (ContinuousMap.ext fun _ ↦ rfl)

end RieszStates

section CountableBarycenters

variable (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X] [Countable X] [Nonempty X]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]

local instance weakSpaceT2 : T2Space (WeakSpace ℝ E) := by
  apply (WeakBilin.isEmbedding (B := (topDualPairing ℝ E).flip) ?_).t2Space
  intro x y hxy
  apply (NormedSpace.eq_iff_forall_dual_eq ℝ).2
  intro phi
  exact LinearMap.congr_fun hxy phi

omit [Nonempty X] [NormedSpace ℝ E] [CompleteSpace E] in
/-- On a countable Borel space every map into a normed space is strongly
measurable: it is measurable because points are measurable, and its range is
countable, hence separable. -/
theorem stronglyMeasurable_of_countable_domain (j : X → E) :
    StronglyMeasurable j := by
  rw [stronglyMeasurable_iff_measurable_separable]
  exact ⟨measurable_of_countable j, Set.countable_range j |>.isSeparable⟩

omit [Nonempty X] [NormedSpace ℝ E] [CompleteSpace E] in
/-- A bounded map on the countable parameter space is integrable against
every state Riesz measure. -/
theorem integrable_stateRieszMeasure_of_countable
    (j : X → E) (C : ℝ) (hj : ∀ x, ‖j x‖ ≤ C)
    (L : PositiveNormalizedState X) :
    Integrable j (stateRieszMeasure X L) := by
  apply (integrable_const C).mono'
  · exact (stronglyMeasurable_of_countable_domain X j).aestronglyMeasurable
  · exact Filter.Eventually.of_forall hj

/-- The Bochner barycenter of the Riesz measure represented by a state. -/
def stateBarycenter (j : X → E) (L : PositiveNormalizedState X) : E :=
  ∫ x, j x ∂(stateRieszMeasure X L)

omit [Nonempty X] in
/-- Every scalar weak coordinate of the barycenter is evaluation of the
state at the corresponding continuous scalar function. -/
theorem apply_stateBarycenter
    (j : X → E) (C : ℝ) (hj : ∀ x, ‖j x‖ ≤ C)
    (hjweak : ∀ phi : E →L[ℝ] ℝ, Continuous (fun x ↦ phi (j x)))
    (L : PositiveNormalizedState X) (phi : E →L[ℝ] ℝ) :
    phi (stateBarycenter X j L) =
      L.1 ⟨fun x ↦ phi (j x), hjweak phi⟩ := by
  have hjint := integrable_stateRieszMeasure_of_countable X j C hj L
  let g : C(X, ℝ) := ⟨fun x ↦ phi (j x), hjweak phi⟩
  calc
    phi (stateBarycenter X j L) = ∫ x, phi (j x) ∂(stateRieszMeasure X L) :=
      (phi.integral_comp_comm hjint).symm
    _ = L.1 g := integral_stateRieszMeasure X L g
    _ = L.1 ⟨fun x ↦ phi (j x), hjweak phi⟩ := rfl

omit [Nonempty X] in
/-- The barycenter map is continuous from the weak-star state space to the
weak topology of the Banach space. -/
theorem continuous_toWeakSpace_stateBarycenter
    (j : X → E) (C : ℝ) (hj : ∀ x, ‖j x‖ ≤ C)
    (hjweak : ∀ phi : E →L[ℝ] ℝ, Continuous (fun x ↦ phi (j x))) :
    Continuous (fun L : PositiveNormalizedState X ↦
      toWeakSpace ℝ E (stateBarycenter X j L)) := by
  apply WeakBilin.continuous_of_continuous_eval
  intro phi
  let g : C(X, ℝ) := ⟨fun x ↦ phi (j x), hjweak phi⟩
  have heval : Continuous (fun L : PositiveNormalizedState X ↦ L.1 g) :=
    (WeakDual.eval_continuous g).comp continuous_subtype_val
  convert heval using 1
  funext L
  exact apply_stateBarycenter X j C hj hjweak L phi

/-- The weak range of all state barycenters is compact. -/
theorem isCompact_range_toWeakSpace_stateBarycenter
    (j : X → E) (C : ℝ) (hj : ∀ x, ‖j x‖ ≤ C)
    (hjweak : ∀ phi : E →L[ℝ] ℝ, Continuous (fun x ↦ phi (j x))) :
    IsCompact (Set.range (fun L : PositiveNormalizedState X ↦
      toWeakSpace ℝ E (stateBarycenter X j L))) := by
  letI : CompactSpace (PositiveNormalizedState X) :=
    isCompact_iff_compactSpace.mp (isCompact_positiveNormalizedStates X)
  exact isCompact_range
    (continuous_toWeakSpace_stateBarycenter X j C hj hjweak)

/-- Point evaluation is a positive normalized state. -/
def evaluationState (x : X) : PositiveNormalizedState X :=
  ⟨StrongDual.toWeakDual (ContinuousMap.evalCLM ℝ x), by
    constructor
    · intro f hf
      exact hf x
    · rfl⟩

omit [Nonempty X] in
/-- The barycenter of a point-evaluation state is the original point. -/
theorem stateBarycenter_evaluationState
    (j : X → E) (C : ℝ) (hj : ∀ x, ‖j x‖ ≤ C)
    (hjweak : ∀ phi : E →L[ℝ] ℝ, Continuous (fun x ↦ phi (j x)))
    (x : X) :
    stateBarycenter X j (evaluationState X x) = j x := by
  rw [NormedSpace.eq_iff_forall_dual_eq ℝ]
  intro phi
  rw [apply_stateBarycenter X j C hj hjweak]
  simp only [evaluationState, StrongDual.toWeakDual_apply, ContinuousMap.evalCLM_apply,
    ContinuousMap.coe_mk]

/-- Convex combinations of states are states. -/
def combineStates (L M : PositiveNormalizedState X)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    PositiveNormalizedState X :=
  ⟨a • L.1 + b • M.1, by
    constructor
    · intro f hf
      change 0 ≤ a * L.1 f + b * M.1 f
      exact add_nonneg (mul_nonneg ha (L.2.1 f hf))
        (mul_nonneg hb (M.2.1 f hf))
    · change a * L.1 1 + b * M.1 1 = 1
      rw [L.2.2, M.2.2, mul_one, mul_one, hab]⟩

omit [Nonempty X] in
/-- The barycenter construction respects convex combinations of states. -/
theorem stateBarycenter_combineStates
    (j : X → E) (C : ℝ) (hj : ∀ x, ‖j x‖ ≤ C)
    (hjweak : ∀ phi : E →L[ℝ] ℝ, Continuous (fun x ↦ phi (j x)))
    (L M : PositiveNormalizedState X)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    stateBarycenter X j (combineStates X L M a b ha hb hab) =
      a • stateBarycenter X j L + b • stateBarycenter X j M := by
  rw [NormedSpace.eq_iff_forall_dual_eq ℝ]
  intro phi
  rw [apply_stateBarycenter X j C hj hjweak,
    map_add, map_smul, map_smul,
    apply_stateBarycenter X j C hj hjweak,
    apply_stateBarycenter X j C hj hjweak]
  change a * L.1 _ + b * M.1 _ = _
  simp

omit [Nonempty X] in
/-- The weak range of the barycenter map is convex. -/
theorem convex_range_toWeakSpace_stateBarycenter
    (j : X → E) (C : ℝ) (hj : ∀ x, ‖j x‖ ≤ C)
    (hjweak : ∀ phi : E →L[ℝ] ℝ, Continuous (fun x ↦ phi (j x))) :
    Convex ℝ (Set.range (fun L : PositiveNormalizedState X ↦
      toWeakSpace ℝ E (stateBarycenter X j L))) := by
  intro _ hx _ hy a b ha hb hab
  obtain ⟨L, rfl⟩ := hx
  obtain ⟨M, rfl⟩ := hy
  refine ⟨combineStates X L M a b ha hb hab, ?_⟩
  change toWeakSpace ℝ E
      (stateBarycenter X j (combineStates X L M a b ha hb hab)) = _
  rw [stateBarycenter_combineStates X j C hj hjweak]
  simp

/-- Countability removes the measurability obstruction in the barycenter
proof of Krein's theorem.  The norm-closed convex hull of the range of a
bounded weakly continuous map from a countable compact Hausdorff space is
weakly compact. -/
theorem isCompact_toWeakSpace_image_closedConvexHull_range
    (j : X → E) (C : ℝ) (hj : ∀ x, ‖j x‖ ≤ C)
    (hjweak : ∀ phi : E →L[ℝ] ℝ, Continuous (fun x ↦ phi (j x))) :
    IsCompact (toWeakSpace ℝ E '' closedConvexHull ℝ (Set.range j)) := by
  rw [toWeakSpace_image_closedConvexHull]
  let R : Set (WeakSpace ℝ E) := Set.range (fun L : PositiveNormalizedState X ↦
    toWeakSpace ℝ E (stateBarycenter X j L))
  have hRcompact : IsCompact R :=
    isCompact_range_toWeakSpace_stateBarycenter X j C hj hjweak
  have hRclosed : IsClosed R := hRcompact.isClosed
  have hRconvex : Convex ℝ R :=
    convex_range_toWeakSpace_stateBarycenter X j C hj hjweak
  have hcontains : toWeakSpace ℝ E '' Set.range j ⊆ R := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    refine ⟨evaluationState X x, ?_⟩
    change toWeakSpace ℝ E (stateBarycenter X j (evaluationState X x)) = _
    rw [stateBarycenter_evaluationState X j C hj hjweak]
  apply hRcompact.of_isClosed_subset isClosed_closure
  exact closure_minimal (convexHull_min hcontains hRconvex) hRclosed

end CountableBarycenters

section CountableWeakCompactSets

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

local instance weakSpaceT2' : T2Space (WeakSpace ℝ E) := by
  apply (WeakBilin.isEmbedding (B := (topDualPairing ℝ E).flip) ?_).t2Space
  intro x y hxy
  apply (NormedSpace.eq_iff_forall_dual_eq ℝ).2
  intro phi
  exact LinearMap.congr_fun hxy phi

/-- Krein compactness for the countable case needed by Boolean translation
orbits: a nonempty, countable, norm-bounded weakly compact set in a real
Banach space has weakly compact norm-closed convex hull. -/
theorem Set.Countable.isCompact_toWeakSpace_image_closedConvexHull
    {K : Set E} (hKcount : K.Countable) (hKne : K.Nonempty)
    (C : ℝ) (hKbound : ∀ x ∈ K, ‖x‖ ≤ C)
    (hKcompact : IsCompact (toWeakSpace ℝ E '' K)) :
    IsCompact (toWeakSpace ℝ E '' closedConvexHull ℝ K) := by
  let X := {x : WeakSpace ℝ E // x ∈ toWeakSpace ℝ E '' K}
  letI : CompactSpace X := isCompact_iff_compactSpace.mp hKcompact
  letI : Countable X := Set.Countable.to_subtype (hKcount.image (toWeakSpace ℝ E))
  letI : Nonempty X := by
    obtain ⟨x, hx⟩ := hKne
    exact ⟨⟨toWeakSpace ℝ E x, ⟨x, hx, rfl⟩⟩⟩
  letI : MeasurableSpace X := borel X
  letI : BorelSpace X := ⟨rfl⟩
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  let j : X → E := fun x ↦ (toWeakSpace ℝ E).symm x.1
  have hjbound : ∀ x, ‖j x‖ ≤ C := by
    intro x
    obtain ⟨y, hy, hxy⟩ := x.2
    have heq : y = j x := by
      simpa [j] using congrArg (toWeakSpace ℝ E).symm hxy
    simpa [← heq] using hKbound y hy
  have hjweak : ∀ phi : E →L[ℝ] ℝ, Continuous (fun x ↦ phi (j x)) := by
    intro phi
    let phi' : StrongDual ℝ (WeakSpace ℝ E) :=
      { toLinearMap := (phi : E →ₗ[ℝ] ℝ).comp
          ((toWeakSpace ℝ E).symm : WeakSpace ℝ E →ₗ[ℝ] E)
        cont := WeakBilin.eval_continuous (topDualPairing ℝ E).flip phi }
    change Continuous (fun x : X ↦ phi' x.1)
    exact phi'.continuous.comp continuous_subtype_val
  have hrange : Set.range j = K := by
    apply Set.Subset.antisymm
    · rintro y ⟨x, rfl⟩
      obtain ⟨z, hz, hxz⟩ := x.2
      have := congrArg (toWeakSpace ℝ E).symm hxz
      simpa [j] using this.symm ▸ hz
    · intro y hy
      let x : X := ⟨toWeakSpace ℝ E y, ⟨y, hy, rfl⟩⟩
      refine ⟨x, ?_⟩
      simp [j, x]
  simpa only [hrange] using
    isCompact_toWeakSpace_image_closedConvexHull_range X j C hjbound hjweak

end CountableWeakCompactSets

end IndependentZeroBlocks
