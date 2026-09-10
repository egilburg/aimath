import SierpinskiFormal.CountableWeakKrein
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Stationary states on compact spaces

The compact weak-star state space supplies a stationary state for every
positive unital operator on continuous real functions.  This is the
Krylov--Bogoliubov Cesaro argument in a form suited to countable group flows.
-/

noncomputable section

open Filter Set Topology MeasureTheory
open scoped BigOperators Topology

namespace IndependentZeroBlocks

variable (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]

theorem weakDual_finset_sum_apply {ι : Type*} (s : Finset ι)
    (L : ι → WeakDual ℝ C(X, ℝ)) (f : C(X, ℝ)) :
    (∑ i ∈ s, L i) f = ∑ i ∈ s, L i f := by
  classical
  induction s using Finset.induction with
  | empty => rfl
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      change L a f + (∑ i ∈ s, L i) f = L a f + ∑ i ∈ s, L i f
      rw [ih]

/-- Positivity and preservation of one for an operator on continuous
functions. -/
def IsMarkovOperator (P : C(X, ℝ) →L[ℝ] C(X, ℝ)) : Prop :=
  (∀ f : C(X, ℝ), 0 ≤ f → 0 ≤ P f) ∧ P 1 = 1

/-- Pullback of a state by a Markov operator. -/
def pullbackState (P : C(X, ℝ) →L[ℝ] C(X, ℝ))
    (hP : IsMarkovOperator X P) (L : PositiveNormalizedState X) :
    PositiveNormalizedState X :=
  ⟨StrongDual.toWeakDual ((WeakDual.toStrongDual L.1).comp P), by
    constructor
    · intro f hf
      exact L.2.1 (P f) (hP.1 f hf)
    · change L.1 (P 1) = 1
      rw [hP.2, L.2.2]⟩

@[simp] theorem pullbackState_apply
    (P : C(X, ℝ) →L[ℝ] C(X, ℝ)) (hP : IsMarkovOperator X P)
    (L : PositiveNormalizedState X) (f : C(X, ℝ)) :
    (pullbackState X P hP L).1 f = L.1 (P f) := by
  change (StrongDual.toWeakDual ((WeakDual.toStrongDual L.1).comp P)) f = L.1 (P f)
  simp only [StrongDual.toWeakDual_apply, ContinuousLinearMap.comp_apply,
    WeakDual.toStrongDual_apply]

/-- Pullback is continuous for the weak-star state topology. -/
theorem continuous_pullbackState
    (P : C(X, ℝ) →L[ℝ] C(X, ℝ)) (hP : IsMarkovOperator X P) :
    Continuous (pullbackState X P hP) := by
  apply Continuous.subtype_mk
  apply WeakBilin.continuous_of_continuous_eval
  intro (f : C(X, ℝ))
  exact (WeakDual.eval_continuous (P f)).comp continuous_subtype_val

/-- Cesaro average of the first `n+1` iterates of a state. -/
def stateCesaro (P : C(X, ℝ) →L[ℝ] C(X, ℝ))
    (hP : IsMarkovOperator X P) (L : PositiveNormalizedState X) (n : ℕ) :
    PositiveNormalizedState X :=
  ⟨((n + 1 : ℕ) : ℝ)⁻¹ •
      ∑ k ∈ Finset.range (n + 1), ((pullbackState X P hP)^[k] L).1, by
    constructor
    · intro f hf
      change 0 ≤ (((n + 1 : ℕ) : ℝ)⁻¹ •
        ∑ k ∈ Finset.range (n + 1), ((pullbackState X P hP)^[k] L).1) f
      rw [show ((((n + 1 : ℕ) : ℝ)⁻¹ •
          ∑ k ∈ Finset.range (n + 1), ((pullbackState X P hP)^[k] L).1) f) =
            ((n + 1 : ℕ) : ℝ)⁻¹ *
              ((∑ k ∈ Finset.range (n + 1), ((pullbackState X P hP)^[k] L).1) f) by rfl,
        weakDual_finset_sum_apply]
      change 0 ≤ ((n + 1 : ℕ) : ℝ)⁻¹ *
        ∑ k ∈ Finset.range (n + 1), (((pullbackState X P hP)^[k] L).1 f)
      exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
        (Finset.sum_nonneg fun k _ ↦ (((pullbackState X P hP)^[k] L).2.1 f hf))
    · change ((((n + 1 : ℕ) : ℝ)⁻¹ •
        ∑ k ∈ Finset.range (n + 1), ((pullbackState X P hP)^[k] L).1) 1) = 1
      rw [show ((((n + 1 : ℕ) : ℝ)⁻¹ •
          ∑ k ∈ Finset.range (n + 1), ((pullbackState X P hP)^[k] L).1) 1) =
            ((n + 1 : ℕ) : ℝ)⁻¹ *
              ((∑ k ∈ Finset.range (n + 1), ((pullbackState X P hP)^[k] L).1) 1) by rfl,
        weakDual_finset_sum_apply]
      change ((n + 1 : ℕ) : ℝ)⁻¹ *
        ∑ k ∈ Finset.range (n + 1), (((pullbackState X P hP)^[k] L).1 1) = 1
      have hone : ∀ k, (((pullbackState X P hP)^[k] L).1 1) = 1 :=
        fun k ↦ ((pullbackState X P hP)^[k] L).2.2
      simp_rw [hone]
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp⟩

@[simp] theorem stateCesaro_apply
    (P : C(X, ℝ) →L[ℝ] C(X, ℝ)) (hP : IsMarkovOperator X P)
    (L : PositiveNormalizedState X) (n : ℕ) (f : C(X, ℝ)) :
    (stateCesaro X P hP L n).1 f =
      ((n + 1 : ℕ) : ℝ)⁻¹ *
        ∑ k ∈ Finset.range (n + 1), (((pullbackState X P hP)^[k] L).1 f) := by
  change ((((n + 1 : ℕ) : ℝ)⁻¹ •
    ∑ k ∈ Finset.range (n + 1), ((pullbackState X P hP)^[k] L).1) f) = _
  rw [show ((((n + 1 : ℕ) : ℝ)⁻¹ •
      ∑ k ∈ Finset.range (n + 1), ((pullbackState X P hP)^[k] L).1) f) =
        ((n + 1 : ℕ) : ℝ)⁻¹ *
          ((∑ k ∈ Finset.range (n + 1), ((pullbackState X P hP)^[k] L).1) f) by rfl,
    weakDual_finset_sum_apply]

/-- The scalar defect of the Cesaro states tends to zero. -/
theorem tendsto_pullbackState_stateCesaro_sub
    [Nonempty X]
    (P : C(X, ℝ) →L[ℝ] C(X, ℝ)) (hP : IsMarkovOperator X P)
    (L : PositiveNormalizedState X) (f : C(X, ℝ)) :
    Tendsto (fun n ↦
      (pullbackState X P hP (stateCesaro X P hP L n)).1 f -
        (stateCesaro X P hP L n).1 f) atTop (𝓝 0) := by
  have hbound : ∀ n,
      ‖(((pullbackState X P hP)^[n] L).1 f)‖ ≤ ‖f‖ := by
    intro n
    have hn := positiveNormalizedStates_norm_le_one X
      (((pullbackState X P hP)^[n] L).2)
    exact (ContinuousLinearMap.le_opNorm (WeakDual.toStrongDual
      (((pullbackState X P hP)^[n] L).1)) f).trans
      (by simpa using mul_le_mul_of_nonneg_right hn (norm_nonneg f))
  have htel : ∀ n,
      (pullbackState X P hP (stateCesaro X P hP L n)).1 f -
          (stateCesaro X P hP L n).1 f =
        ((n + 1 : ℕ) : ℝ)⁻¹ *
          ((((pullbackState X P hP)^[n + 1] L).1 f) - L.1 f) := by
    intro n
    rw [pullbackState_apply, stateCesaro_apply, stateCesaro_apply]
    change ((n + 1 : ℕ) : ℝ)⁻¹ *
          ∑ k ∈ Finset.range (n + 1),
            (((pullbackState X P hP)^[k] L).1 (P f)) - _ = _
    have hshift : ∀ k,
        (((pullbackState X P hP)^[k] L).1 (P f)) =
          (((pullbackState X P hP)^[k + 1] L).1 f) := by
      intro k
      calc
        (((pullbackState X P hP)^[k] L).1 (P f)) =
            (pullbackState X P hP ((pullbackState X P hP)^[k] L)).1 f :=
              (pullbackState_apply X P hP ((pullbackState X P hP)^[k] L) f).symm
        _ = (((pullbackState X P hP)^[k + 1] L).1 f) := by
          rw [Function.iterate_succ_apply']
    simp_rw [hshift]
    rw [← mul_sub]
    congr 1
    rw [Finset.sum_range_succ, Finset.sum_range_succ']
    simp
  rw [show (fun n ↦
      (pullbackState X P hP (stateCesaro X P hP L n)).1 f -
        (stateCesaro X P hP L n).1 f) =
      (fun n ↦ ((n + 1 : ℕ) : ℝ)⁻¹ *
        ((((pullbackState X P hP)^[n + 1] L).1 f) - L.1 f)) from funext htel]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hden : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) := by
    have hcast : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    exact hcast.inv_tendsto_atTop
  apply squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg _)
    ?_ (by simpa using hden.norm.mul_const (2 * ‖f‖))
  filter_upwards with n
  rw [norm_mul]
  rw [Real.norm_eq_abs, abs_inv]
  simp only [Nat.cast_add, Nat.cast_one]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (abs_nonneg _))
  have hL : ‖L.1 f‖ ≤ ‖f‖ := by simpa using hbound 0
  exact (norm_sub_le _ _).trans (by
    simpa [two_mul] using add_le_add (hbound (n + 1)) hL)

/-- Every initial state has a stationary cluster point among its Cesaro
iterates.  The cluster witness lets applications identify the stationary
state's value from known scalar Cesaro limits. -/
theorem exists_stationary_state_isMapClusterPt
    [Nonempty X] (P : C(X, ℝ) →L[ℝ] C(X, ℝ))
    (hP : IsMarkovOperator X P) (L0 : PositiveNormalizedState X) :
    ∃ L : PositiveNormalizedState X,
      pullbackState X P hP L = L ∧
      MapClusterPt L atTop (stateCesaro X P hP L0) := by
  letI : CompactSpace (PositiveNormalizedState X) :=
    isCompact_iff_compactSpace.mp (isCompact_positiveNormalizedStates X)
  obtain ⟨L, hcluster⟩ : ∃ L, MapClusterPt L atTop (stateCesaro X P hP L0) := by
    obtain ⟨L, _, hL⟩ := (isCompact_univ : IsCompact (Set.univ : Set (PositiveNormalizedState X))).exists_mapClusterPt
      (by simp : Tendsto (stateCesaro X P hP L0) atTop (𝓟 Set.univ))
    exact ⟨L, hL⟩
  let u := stateCesaro X P hP L0
  let F : Filter ℕ := comap u (𝓝 L) ⊓ atTop
  haveI : NeBot F := neBot_inf_comap_iff_map'.mpr hcluster
  have hu : Tendsto u F (𝓝 L) :=
    tendsto_iff_comap.mpr (show F ≤ comap u (𝓝 L) from inf_le_left)
  have hFtop : F ≤ atTop := inf_le_right
  refine ⟨L, Subtype.ext ?_, hcluster⟩
  apply ContinuousLinearMap.ext
  intro f
  have hbase : Tendsto (fun n ↦ (u n).1 f) F (𝓝 (L.1 f)) :=
    (((WeakDual.eval_continuous f).comp continuous_subtype_val).tendsto L).comp hu
  have hpull : Tendsto (fun n ↦ (pullbackState X P hP (u n)).1 f) F
      (𝓝 ((pullbackState X P hP L).1 f)) := by
    exact (((WeakDual.eval_continuous f).comp continuous_subtype_val).tendsto _).comp
      ((continuous_pullbackState X P hP).continuousAt.tendsto.comp hu)
  have hdiff := hpull.sub hbase
  have hzero := (tendsto_pullbackState_stateCesaro_sub X P hP L0 f).mono_left hFtop
  have hz : (pullbackState X P hP L).1 f - L.1 f = 0 :=
    tendsto_nhds_unique hdiff hzero
  exact sub_eq_zero.mp hz

/-- Every Markov operator on `C(X,ℝ)` has a stationary positive normalized
state. -/
theorem exists_stationary_state
    [Nonempty X] (P : C(X, ℝ) →L[ℝ] C(X, ℝ))
    (hP : IsMarkovOperator X P) :
    ∃ L : PositiveNormalizedState X, pullbackState X P hP L = L := by
  let L0 : PositiveNormalizedState X := evaluationState X (Classical.choice ‹Nonempty X›)
  obtain ⟨L, hfixed, _⟩ := exists_stationary_state_isMapClusterPt X P hP L0
  exact ⟨L, hfixed⟩

section FiniteMaps

variable {D : Type*} [Fintype D] [Nonempty D]

/-- Precomposition by a continuous self-map, as an operator on continuous
real functions. -/
def continuousPrecompCLM (T : C(X, X)) : C(X, ℝ) →L[ℝ] C(X, ℝ) :=
  ({ toFun := fun f ↦ f.comp T
     map_add' := by intros; ext x; rfl
     map_smul' := by intros; ext x; rfl } :
    C(X, ℝ) →ₗ[ℝ] C(X, ℝ)).mkContinuous 1 (by
      intro f
      have h : ‖f.comp T‖ ≤ ‖f‖ := by
        apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
        intro x
        exact ContinuousMap.norm_coe_le_norm f (T x)
      simpa using h)

@[simp] theorem continuousPrecompCLM_apply (T : C(X, X))
    (f : C(X, ℝ)) (x : X) : continuousPrecompCLM X T f x = f (T x) := rfl

/-- Markov operator associated with a finite law on continuous self-maps. -/
def finiteMapAverage (T : D → C(X, X)) (weight : D → ℝ) :
    C(X, ℝ) →L[ℝ] C(X, ℝ) :=
  ∑ d, weight d • continuousPrecompCLM X (T d)

@[simp] theorem finiteMapAverage_apply (T : D → C(X, X)) (weight : D → ℝ)
    (f : C(X, ℝ)) (x : X) :
    finiteMapAverage X T weight f x = ∑ d, weight d * f (T d x) := by
  simp [finiteMapAverage, continuousPrecompCLM_apply]

theorem finiteMapAverage_isMarkov (T : D → C(X, X)) (weight : D → ℝ)
    (hweight : ∀ d, 0 ≤ weight d) (hweight_one : ∑ d, weight d = 1) :
    IsMarkovOperator X (finiteMapAverage X T weight) := by
  constructor
  · intro f hf x
    change 0 ≤ finiteMapAverage X T weight f x
    rw [finiteMapAverage_apply]
    exact Finset.sum_nonneg fun d _ ↦ mul_nonneg (hweight d) (hf (T d x))
  · ext x
    simp [finiteMapAverage_apply, hweight_one]

/-- Krylov--Bogoliubov existence for a finite random choice of continuous
self-maps of a compact Hausdorff space. -/
theorem exists_stationary_state_finiteMapAverage
    [Nonempty X] (T : D → C(X, X)) (weight : D → ℝ)
    (hweight : ∀ d, 0 ≤ weight d) (hweight_one : ∑ d, weight d = 1) :
    ∃ L : PositiveNormalizedState X,
      pullbackState X (finiteMapAverage X T weight)
        (finiteMapAverage_isMarkov X T weight hweight hweight_one) L = L :=
  exists_stationary_state X (finiteMapAverage X T weight)
    (finiteMapAverage_isMarkov X T weight hweight hweight_one)

section RieszMeasure

variable [MeasurableSpace X] [BorelSpace X]

/-- The Riesz measure of a normalized positive state is a probability. -/
instance stateRieszMeasure_isProbabilityMeasure (L : PositiveNormalizedState X) :
    IsProbabilityMeasure (stateRieszMeasure X L) := by
  constructor
  rw [← ENNReal.toReal_eq_one_iff]
  have h := integral_stateRieszMeasure X L (1 : C(X, ℝ))
  simpa [MeasureTheory.integral_const, measureReal_def,
    positiveNormalizedStates_one X] using h

/-- The finite weighted sum of pushforwards associated with the maps. -/
def finiteMapMeasureAverage (T : D → C(X, X)) (weight : D → ℝ)
    (μ : Measure X) : Measure X :=
  ∑ d, ENNReal.ofReal (weight d) • Measure.map (T d) μ

/-- A fixed state yields a stationary Riesz measure.  The mild
`HasOuterApproxClosed` hypothesis is available for metrizable spaces and
allows finite Borel measures to be identified by continuous test functions. -/
theorem stateRieszMeasure_eq_finiteMapMeasureAverage
    [HasOuterApproxClosed X]
    (T : D → C(X, X)) (weight : D → ℝ)
    (hweight : ∀ d, 0 ≤ weight d) (hweight_one : ∑ d, weight d = 1)
    (L : PositiveNormalizedState X)
    (hfixed : pullbackState X (finiteMapAverage X T weight)
      (finiteMapAverage_isMarkov X T weight hweight hweight_one) L = L) :
    stateRieszMeasure X L =
      finiteMapMeasureAverage X T weight (stateRieszMeasure X L) := by
  letI : IsFiniteMeasure
      (finiteMapMeasureAverage X T weight (stateRieszMeasure X L)) := by
    constructor
    simp [finiteMapMeasureAverage, Measure.sum_apply, Measure.smul_apply,
      Measure.map_apply, (T _).continuous.measurable]
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  let fc : C(X, ℝ) := f.toContinuousMap
  have hstate : L.1 fc = ∑ d, weight d * L.1 (fc.comp (T d)) := by
    have hfixeval := congrArg (fun M : PositiveNormalizedState X ↦ M.1 fc) hfixed
    change L.1 (finiteMapAverage X T weight fc) = L.1 fc at hfixeval
    calc
      L.1 fc = L.1 (finiteMapAverage X T weight fc) := hfixeval.symm
      _ = L.1 (∑ d, weight d • continuousPrecompCLM X (T d) fc) := by
        congr 1
        ext x
        simp [finiteMapAverage_apply, continuousPrecompCLM_apply]
      _ = ∑ d, L.1 (weight d • continuousPrecompCLM X (T d) fc) :=
        map_sum L.1 _ _
      _ = ∑ d, weight d * L.1 (fc.comp (T d)) := by
        apply Finset.sum_congr rfl
        intro d _
        rw [map_smul]
        rfl
  change (∫ x, fc x ∂stateRieszMeasure X L) =
    ∫ x, fc x ∂finiteMapMeasureAverage X T weight (stateRieszMeasure X L)
  rw [integral_stateRieszMeasure X L fc]
  rw [hstate]
  unfold finiteMapMeasureAverage
  rw [MeasureTheory.integral_finset_sum_measure]
  · apply Finset.sum_congr rfl
    intro d _
    rw [MeasureTheory.integral_smul_measure]
    rw [ENNReal.toReal_ofReal (hweight d)]
    simp only [smul_eq_mul]
    congr 1
    calc
      L.1 (fc.comp (T d)) =
          ∫ x, fc (T d x) ∂stateRieszMeasure X L := by
            simpa using (integral_stateRieszMeasure X L (fc.comp (T d))).symm
      _ = ∫ x, fc x ∂Measure.map (T d) (stateRieszMeasure X L) := by
        rw [MeasureTheory.integral_map (T d).continuous.measurable.aemeasurable
          fc.continuous.aestronglyMeasurable]
  · intro d _
    letI : IsFiniteMeasure (Measure.map (T d) (stateRieszMeasure X L)) := by
      constructor
      rw [Measure.map_apply (T d).continuous.measurable MeasurableSet.univ]
      simp
    letI : IsFiniteMeasure
        (ENNReal.ofReal (weight d) • Measure.map (T d) (stateRieszMeasure X L)) := by
      constructor
      rw [Measure.smul_apply]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
    exact f.integrable _

end RieszMeasure

end FiniteMaps

end IndependentZeroBlocks
