import SierpinskiFormal.StationaryL1Duality
import SierpinskiFormal.StationaryFiberBarycenter
import SierpinskiFormal.StationaryGraphTests

/-!
# Weak L1 clusters from empirical graph-state clusters

This module turns a weak-star cluster of empirical graph states into a weak
cluster of the corresponding vector-valued Cesaro averages.  Countability of
the compact range supplies strong measurability without a separability
assumption on the ambient Banach space.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal BigOperators

namespace IndependentZeroBlocks

section GraphRangeLp

variable {X K E : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K]
  [MeasurableSingletonClass K] [Countable K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure X} [IsFiniteMeasure μ]

/-- A countable-valued weak-range map is strongly measurable as an
`E`-valued function. -/
theorem stronglyMeasurable_graphRange (j : K → E) (g : C(X, K)) :
    StronglyMeasurable (fun x => j (g x)) := by
  borelize E
  rw [stronglyMeasurable_iff_measurable_separable]
  constructor
  · exact (measurable_of_countable j).comp g.continuous.measurable
  · apply Set.Countable.isSeparable
    exact (Set.countable_range j).mono (by
      simpa only [Function.comp_def] using
        Set.range_comp_subset_range (fun x : X => g x) j)

/-- A uniformly bounded graph range defines an element of Bochner `L¹`. -/
theorem memLp_one_graphRange (j : K → E) (C : ℝ) (hj : ∀ k, ‖j k‖ ≤ C)
    (g : C(X, K)) : MemLp (fun x => j (g x)) 1 μ :=
  MemLp.of_bound (stronglyMeasurable_graphRange j g).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => hj (g x))

/-- The `L¹` class of the graph range `x ↦ j(g(x))`. -/
noncomputable def graphRangeLp (j : K → E) (C : ℝ) (hj : ∀ k, ‖j k‖ ≤ C)
    (g : C(X, K)) : Lp E 1 μ :=
  (memLp_one_graphRange (μ := μ) j C hj g).toLp (fun x => j (g x))

 theorem graphRangeLp_coeFn (j : K → E) (C : ℝ) (hj : ∀ k, ‖j k‖ ≤ C)
    (g : C(X, K)) :
    ⇑(graphRangeLp (μ := μ) j C hj g) =ᵐ[μ] fun x => j (g x) :=
  (memLp_one_graphRange (μ := μ) j C hj g).coeFn_toLp

/-- The average of the first `N+1` graph-range vectors in Bochner `L¹`. -/
noncomputable def graphCesaroLp (j : K → E) (C : ℝ) (hj : ∀ k, ‖j k‖ ≤ C)
    (g : ℕ → C(X, K)) (N : ℕ) : Lp E 1 μ :=
  (N + 1 : ℝ)⁻¹ • ∑ n ∈ Finset.range (N + 1),
    graphRangeLp (μ := μ) j C hj (g n)

/-- The RN barycenter of a product measure, represented in Bochner `L¹`. -/
noncomputable def fiberBarycenterLp [CompleteSpace E]
    (ν : Measure (X × K)) [IsFiniteMeasure ν]
    (hν : ν.fst = μ) (j : K → E) (C : ℝ) (hj : ∀ k, ‖j k‖ ≤ C) :
    Lp E 1 μ :=
  (memLp_one_iff_integrable.mpr
    (integrable_countableFiberBarycenter ν μ hν j C hj)).toLp
      (countableFiberBarycenter ν μ j)

 theorem fiberBarycenterLp_coeFn [CompleteSpace E]
    (ν : Measure (X × K)) [IsFiniteMeasure ν]
    (hν : ν.fst = μ) (j : K → E) (C : ℝ) (hj : ∀ k, ‖j k‖ ≤ C) :
    ⇑(fiberBarycenterLp (μ := μ) ν hν j C hj) =ᵐ[μ]
      countableFiberBarycenter ν μ j :=
  (memLp_one_iff_integrable.mpr
    (integrable_countableFiberBarycenter ν μ hν j C hj)).coeFn_toLp

theorem dualFieldPairing_graphRangeLp_eq_integral
    (j : K → E) (C : ℝ) (hj : ∀ k, ‖j k‖ ≤ C) (g : C(X, K))
    (η : Lp (E →L[ℝ] ℝ) ∞ μ) :
    dualFieldPairing μ η (graphRangeLp (μ := μ) j C hj g) =
      ∫ x, η x (j (g x)) ∂μ := by
  rw [dualFieldPairing_apply]
  apply integral_congr_ae
  filter_upwards [graphRangeLp_coeFn (μ := μ) j C hj g] with x hx
  rw [hx]

theorem dualFieldPairing_graphCesaroLp_eq
    (j : K → E) (C : ℝ) (hj : ∀ k, ‖j k‖ ≤ C)
    (g : ℕ → C(X, K)) (N : ℕ) (η : Lp (E →L[ℝ] ℝ) ∞ μ) :
    dualFieldPairing μ η (graphCesaroLp (μ := μ) j C hj g N) =
      (N + 1 : ℝ)⁻¹ * ∑ n ∈ Finset.range (N + 1),
        ∫ x, η x (j (g n x)) ∂μ := by
  rw [graphCesaroLp, map_smul, map_sum]
  simp only [smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  exact dualFieldPairing_graphRangeLp_eq_integral (μ := μ) j C hj (g n) η

end GraphRangeLp

section DualCriterion

variable {X E : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure X}

/-- A common cofinal filter on which every represented dual pairing
converges produces a weak cluster point. -/
theorem mapClusterPt_toWeakSpace_of_dualFieldPairing_tendsto
    (u : ℕ → Lp E 1 μ) (h : Lp E 1 μ)
    (G : Filter ℕ) [NeBot G] (hG : G ≤ atTop)
    (hdual : ∀ Λ : Lp E 1 μ →L[ℝ] ℝ,
      ∃ η : Lp (E →L[ℝ] ℝ) ∞ μ, Λ = dualFieldPairing μ η)
    (htendsto : ∀ η : Lp (E →L[ℝ] ℝ) ∞ μ,
      Tendsto (fun N => dualFieldPairing μ η (u N)) G
        (𝓝 (dualFieldPairing μ η h))) :
    MapClusterPt (toWeakSpace ℝ (Lp E 1 μ) h) atTop
      (fun N => toWeakSpace ℝ (Lp E 1 μ) (u N)) := by
  have hinj : Function.Injective (topDualPairing ℝ (Lp E 1 μ)).flip := by
    intro v w hvw
    apply (NormedSpace.eq_iff_forall_dual_eq ℝ).mpr
    intro Λ
    exact LinearMap.congr_fun hvw Λ
  have hweak : Tendsto (fun N => toWeakSpace ℝ (Lp E 1 μ) (u N)) G
      (𝓝 (toWeakSpace ℝ (Lp E 1 μ) h)) := by
    apply (WeakBilin.tendsto_iff_forall_eval_tendsto _ hinj).mpr
    intro Λ
    obtain ⟨η, rfl⟩ := hdual Λ
    change Tendsto (fun N => dualFieldPairing μ η (u N)) G
      (𝓝 (dualFieldPairing μ η h))
    exact htendsto η
  exact hweak.mapClusterPt.mono (map_mono hG)

end DualCriterion

section LpTopBound

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
  {μ : Measure X}

/-- A bundled `L∞` function admits a finite real almost-everywhere norm
bound, in the form used by the fiber-barycenter pairing theorem. -/
theorem exists_ae_norm_bound_Lp_top (η : Lp E ∞ μ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᵐ x ∂μ, ‖η x‖ ≤ D := by
  have htop : eLpNormEssSup (fun x => η x) μ < ⊤ := by
    have h := (Lp.memLp η).2
    simpa only [eLpNorm_exponent_top] using h
  obtain ⟨D, hD⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp htop
  refine ⟨(D : ℝ), D.coe_nonneg, ?_⟩
  filter_upwards [hD] with x hx
  exact_mod_cast hx

end LpTopBound

section GraphStateWeakCluster

variable {X K E : Type*}
  [TopologicalSpace X] [CompactSpace X] [T2Space X] [NormalSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [HasOuterApproxClosed X]
  [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [TopologicalSpace.PseudoMetrizableSpace K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
  [MeasurableSingletonClass K] [Countable K]
  [BorelSpace (X × K)] [HasOuterApproxClosed (X × K)]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure X} [IsProbabilityMeasure μ] [μ.WeaklyRegular]

/-- A weak-star cluster of empirical graph states gives a weak `L¹` cluster
of the corresponding vector Cesaro averages, provided all `L¹` functionals
have a bounded dual-field representation. -/
theorem mapClusterPt_graphCesaroLp_of_empiricalGraphState_cluster
    (j : K → E) (C : ℝ) (hC : 0 ≤ C) (hj : ∀ k, ‖j k‖ ≤ C)
    (hjweak : ∀ φ : E →L[ℝ] ℝ, Continuous (fun k => φ (j k)))
    (g : ℕ → C(X, K)) (L : PositiveNormalizedState (X × K))
    (hL : MapClusterPt L.1 atTop
      (fun N => (empiricalGraphState (μ := μ) g N).1))
    (hdual : ∀ Λ : Lp E 1 μ →L[ℝ] ℝ,
      ∃ η : Lp (E →L[ℝ] ℝ) ∞ μ, Λ = dualFieldPairing μ η) :
    MapClusterPt
      (toWeakSpace ℝ (Lp E 1 μ)
        (fiberBarycenterLp (μ := μ) (stateRieszMeasure (X × K) L)
          (stateRieszMeasure_fst_eq_of_mapClusterPt_empiricalGraphState g L hL)
          j C hj))
      atTop
      (fun N => toWeakSpace ℝ (Lp E 1 μ)
        (graphCesaroLp (μ := μ) j C hj g N)) := by
  let ν : Measure (X × K) := stateRieszMeasure (X × K) L
  have hν : ν.fst = μ :=
    stateRieszMeasure_fst_eq_of_mapClusterPt_empiricalGraphState g L hL
  let stateSeq : ℕ → WeakDual ℝ C(X × K, ℝ) :=
    fun N => (empiricalGraphState (μ := μ) g N).1
  let G : Filter ℕ := comap stateSeq (𝓝 L.1) ⊓ atTop
  haveI : NeBot G := neBot_inf_comap_iff_map'.mpr hL
  have hG : G ≤ atTop := inf_le_right
  have hstate : Tendsto stateSeq G (𝓝 L.1) :=
    tendsto_iff_comap.mpr (show G ≤ comap stateSeq (𝓝 L.1) from inf_le_left)
  have hufst : ∀ N,
      (stateRieszMeasure (X × K) (empiricalGraphState (μ := μ) g N)).fst = μ := by
    intro N
    apply stateRieszMeasure_fst_eq_of_continuousMapFst
    exact empiricalGraphState_continuousMapFst (μ := μ) g N
  apply mapClusterPt_toWeakSpace_of_dualFieldPairing_tendsto
    (u := fun N => graphCesaroLp (μ := μ) j C hj g N)
    (h := fiberBarycenterLp (μ := μ) ν hν j C hj)
    G hG hdual
  intro η
  let R : (E →L[ℝ] ℝ) →L[ℝ] C(K, ℝ) :=
    weakRangeDualRestriction j C hC hj hjweak
  let Φ : X → C(K, ℝ) := fun x => R (η x)
  have hΦm : StronglyMeasurable Φ :=
    R.continuous.comp_stronglyMeasurable (Lp.stronglyMeasurable η)
  have hηi : Integrable (fun x => η x) μ :=
    (Lp.memLp η).integrable le_top
  have hΦi : Integrable Φ μ := R.integrable_comp hηi
  have htest := tendsto_integral_fiberTest_of_tendsto_states_fixed_fst
    (fun N => empiricalGraphState (μ := μ) g N) L G hstate hufst hν
    Φ hΦm hΦi
  have hleft : (fun N => dualFieldPairing μ η
      (graphCesaroLp (μ := μ) j C hj g N)) =
      (fun N => ∫ z, fiberTest Φ z ∂stateRieszMeasure
        (X × K) (empiricalGraphState (μ := μ) g N)) := by
    funext N
    rw [dualFieldPairing_graphCesaroLp_eq]
    rw [integral_fiberTest_empiricalGraphState g N Φ hΦm hΦi]
    congr 1
  obtain ⟨D, hD, hηbound⟩ := exists_ae_norm_bound_Lp_top η
  have hkernel : Measurable (fun z : X × K => η z.1 (j z.2)) := by
    have hjoint := stronglyMeasurable_fiberTest Φ hΦm
    change StronglyMeasurable (fun z : X × K => η z.1 (j z.2)) at hjoint
    exact hjoint.measurable
  have hbary := integral_apply_countableFiberBarycenter_eq_of_ae_bound
    ν μ hν j C hC hj (fun x => η x) (Lp.stronglyMeasurable η)
      hkernel D hD hηbound
  have hright : dualFieldPairing μ η
      (fiberBarycenterLp (μ := μ) ν hν j C hj) =
      ∫ z, fiberTest Φ z ∂ν := by
    rw [dualFieldPairing_apply]
    calc
      (∫ x, η x ((fiberBarycenterLp (μ := μ) ν hν j C hj) x) ∂μ) =
          ∫ x, η x (countableFiberBarycenter ν μ j x) ∂μ := by
        apply integral_congr_ae
        filter_upwards [fiberBarycenterLp_coeFn (μ := μ) ν hν j C hj]
          with x hx
        rw [hx]
      _ = ∫ z, η z.1 (j z.2) ∂ν := hbary
      _ = ∫ z, fiberTest Φ z ∂ν := by
        apply integral_congr_ae
        filter_upwards with z
        rfl
  rw [hleft, hright]
  exact htest

variable {K₀ : Type*} [TopologicalSpace K₀] [CompactSpace K₀] [T2Space K₀]
  [Nonempty K₀] [MeasurableSpace K₀] [BorelSpace K₀]
  [SecondCountableTopology K₀] [Countable K₀]

set_option maxSynthPendingDepth 3 in
/-- The unconditional graph-cluster theorem when the Banach value space has
a countable compact norming representation. -/
theorem mapClusterPt_graphCesaroLp_of_isometricContinuousMapEmbedding
    (J : E →ₗᵢ[ℝ] C(K₀, ℝ))
    (j : K → E) (C : ℝ) (hC : 0 ≤ C) (hj : ∀ k, ‖j k‖ ≤ C)
    (hjweak : ∀ φ : E →L[ℝ] ℝ, Continuous (fun k => φ (j k)))
    (g : ℕ → C(X, K)) (L : PositiveNormalizedState (X × K))
    (hL : MapClusterPt L.1 atTop
      (fun N => (empiricalGraphState (μ := μ) g N).1)) :
    MapClusterPt
      (toWeakSpace ℝ (Lp E 1 μ)
        (fiberBarycenterLp (μ := μ) (stateRieszMeasure (X × K) L)
          (stateRieszMeasure_fst_eq_of_mapClusterPt_empiricalGraphState g L hL)
          j C hj))
      atTop
      (fun N => toWeakSpace ℝ (Lp E 1 μ)
        (graphCesaroLp (μ := μ) j C hj g N)) := by
  apply mapClusterPt_graphCesaroLp_of_empiricalGraphState_cluster
    j C hC hj hjweak g L hL
  intro Λ
  exact exists_dualFieldPairing_of_isometricContinuousMapEmbedding J Λ

end GraphStateWeakCluster

end IndependentZeroBlocks
