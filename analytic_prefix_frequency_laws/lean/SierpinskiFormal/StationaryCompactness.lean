import Mathlib.MeasureTheory.Function.UniformIntegrable
import SierpinskiFormal.StationaryFiberMeasures
import SierpinskiFormal.StationaryFiberBarycenter
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.WeakDual
import SierpinskiFormal.CountableWeakKrein

/-!
# Compactness inputs for stationary Bochner averages

This file records the part of the stationary compactness argument that is
available in Mathlib without a vector-valued Dunford--Pettis/Diestel theorem:
a uniformly pointwise bounded family on a finite measure space is uniformly
integrable in Bochner `L¹`.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace IndependentZeroBlocks

section HilbertWeakCompactness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

/-- The inverse Riesz map, regarded as a map from the weak-star dual to the
weak topology of a real Hilbert space. -/
noncomputable def weakDualToWeakSpaceHilbert : WeakDual ℝ H → WeakSpace ℝ H :=
  fun L ↦ toWeakSpace ℝ H
    ((InnerProductSpace.toDual ℝ H).symm L.toStrongDual)

theorem continuous_weakDualToWeakSpaceHilbert :
    Continuous (weakDualToWeakSpaceHilbert (H := H)) := by
  apply WeakBilin.continuous_of_continuous_eval
  intro phi
  have hcont : Continuous (fun L : WeakDual ℝ H ↦
      L ((InnerProductSpace.toDual ℝ H).symm phi)) :=
    WeakDual.eval_continuous _
  convert hcont using 1
  funext L
  change phi ((InnerProductSpace.toDual ℝ H).symm L.toStrongDual) =
    L.toStrongDual ((InnerProductSpace.toDual ℝ H).symm phi)
  rw [← InnerProductSpace.toDual_symm_apply,
    ← InnerProductSpace.toDual_symm_apply]
  exact real_inner_comm _ _

/-- Closed balls of a real Hilbert space are compact in its weak topology.
This is the scalar `L²` compactness input for a diagonal-coordinate proof. -/
theorem isCompact_toWeakSpace_image_closedBall_hilbert (r : ℝ) :
    IsCompact (toWeakSpace ℝ H '' Metric.closedBall (0 : H) r) := by
  let B : Set (WeakDual ℝ H) :=
    WeakDual.toStrongDual ⁻¹' Metric.closedBall
      (0 : StrongDual ℝ H) r
  have hB : IsCompact B := WeakDual.isCompact_closedBall (0 : StrongDual ℝ H) r
  have himage : weakDualToWeakSpaceHilbert (H := H) '' B =
      toWeakSpace ℝ H '' Metric.closedBall (0 : H) r := by
    ext z
    constructor
    · rintro ⟨L, hL, rfl⟩
      let x : H := (InnerProductSpace.toDual ℝ H).symm L.toStrongDual
      refine ⟨x, ?_, rfl⟩
      change dist x 0 ≤ r
      change dist L.toStrongDual 0 ≤ r at hL
      simpa [dist_eq_norm, x] using hL
    · rintro ⟨x, hx, rfl⟩
      let L : WeakDual ℝ H :=
        StrongDual.toWeakDual ((InnerProductSpace.toDual ℝ H) x)
      refine ⟨L, ?_, ?_⟩
      · change dist ((InnerProductSpace.toDual ℝ H) x)
          (0 : StrongDual ℝ H) ≤ r
        simpa [dist_eq_norm] using hx
      · simp [weakDualToWeakSpaceHilbert, L]
  rw [← himage]
  exact hB.image continuous_weakDualToWeakSpaceHilbert

/-- Every norm-bounded sequence in a real Hilbert space has a weak cluster
point, expressed in the filter form used by `WeakMeanErgodic.lean`. -/
theorem exists_weak_mapClusterPt_of_norm_le_hilbert
    (u : ℕ → H) (r : ℝ) (hu : ∀ n, ‖u n‖ ≤ r) :
    ∃ a : H, MapClusterPt (toWeakSpace ℝ H a) atTop
      (fun n ↦ toWeakSpace ℝ H (u n)) := by
  let C : Set (WeakSpace ℝ H) :=
    toWeakSpace ℝ H '' Metric.closedBall (0 : H) r
  have hC : IsCompact C :=
    isCompact_toWeakSpace_image_closedBall_hilbert (H := H) r
  have hmem : ∀ᶠ n in atTop, toWeakSpace ℝ H (u n) ∈ C := by
    filter_upwards [] with n
    exact ⟨u n, by simpa [dist_eq_norm] using hu n, rfl⟩
  obtain ⟨a, haC, ha⟩ := hC.exists_mapClusterPt
    (tendsto_principal.mpr hmem)
  obtain ⟨a, _, rfl⟩ := haC
  exact ⟨a, ha⟩

/-- A single cofinal filter can weakly cluster any family of coordinatewise
bounded Hilbert-space sequences.  Tychonoff compactness handles all
coordinates simultaneously, so this lemma does not require countability of
the coordinate type. -/
theorem exists_pi_weak_mapClusterPt_of_norm_le_hilbert
    {I : Type*} {H : I → Type*}
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℝ (H i)]
    [∀ i, CompleteSpace (H i)]
    (u : ℕ → ∀ i, H i) (r : I → ℝ) (hu : ∀ n i, ‖u n i‖ ≤ r i) :
    ∃ a : ∀ i, H i,
      MapClusterPt (fun i ↦ toWeakSpace ℝ (H i) (a i)) atTop
        (fun n i ↦ toWeakSpace ℝ (H i) (u n i)) := by
  let C : Set (∀ i, WeakSpace ℝ (H i)) := Set.pi Set.univ
    (fun i ↦ toWeakSpace ℝ (H i) '' Metric.closedBall (0 : H i) (r i))
  have hC : IsCompact C := isCompact_univ_pi fun i ↦
    isCompact_toWeakSpace_image_closedBall_hilbert (H := H i) (r i)
  have hmem : ∀ᶠ n in atTop,
      (fun i ↦ toWeakSpace ℝ (H i) (u n i)) ∈ C := by
    filter_upwards [] with n
    intro i _
    exact ⟨u n i, by simpa [dist_eq_norm] using hu n i, rfl⟩
  obtain ⟨w, _, hw⟩ := hC.exists_mapClusterPt
    (tendsto_principal.mpr hmem)
  let a : ∀ i, H i := fun i ↦ (toWeakSpace ℝ (H i)).symm (w i)
  refine ⟨a, ?_⟩
  simpa only [a, LinearEquiv.apply_symm_apply] using hw

end HilbertWeakCompactness

section GraphStates

variable {X K : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace K] [CompactSpace K]
  {μ : Measure X} [IsProbabilityMeasure μ]

/-- Integration along the graph of a continuous map, as a continuous linear
functional on the continuous functions of the product compactum. -/
noncomputable def graphIntegralCLM (g : C(X, K)) :
    C(X × K, ℝ) →L[ℝ] ℝ := by
  let L : C(X × K, ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun F ↦ ∫ x, F (x, g x) ∂μ
      map_add' := by
        intro F G
        have hF : Integrable (fun x ↦ F (x, g x)) μ := by
          apply (integrable_const ‖F‖).mono'
          · exact (F.continuous.comp
              (continuous_id.prodMk g.continuous)).aestronglyMeasurable
          · exact Filter.Eventually.of_forall fun x ↦
              ContinuousMap.norm_coe_le_norm F _
        have hG : Integrable (fun x ↦ G (x, g x)) μ := by
          apply (integrable_const ‖G‖).mono'
          · exact (G.continuous.comp
              (continuous_id.prodMk g.continuous)).aestronglyMeasurable
          · exact Filter.Eventually.of_forall fun x ↦
              ContinuousMap.norm_coe_le_norm G _
        simpa using integral_add hF hG
      map_smul' := by
        intro c F
        simpa using integral_smul c (fun x ↦ F (x, g x)) }
  exact L.mkContinuous 1 (fun F ↦ by
    have h := norm_integral_le_of_norm_le_const
      (μ := μ) (f := fun x ↦ F (x, g x))
      (Filter.Eventually.of_forall fun x ↦
        ContinuousMap.norm_coe_le_norm F _)
    simpa [L] using h)

@[simp] theorem graphIntegralCLM_apply (g : C(X, K))
    (F : C(X × K, ℝ)) :
    graphIntegralCLM (μ := μ) g F = ∫ x, F (x, g x) ∂μ := rfl

/-- The probability state associated to the graph of a continuous map. -/
noncomputable def graphState (g : C(X, K)) :
    PositiveNormalizedState (X × K) :=
  ⟨StrongDual.toWeakDual (graphIntegralCLM (μ := μ) g), by
    constructor
    · intro F hF
      change 0 ≤ ∫ x, F (x, g x) ∂μ
      exact integral_nonneg_of_ae (Filter.Eventually.of_forall fun x ↦ hF (x, g x))
    · change ∫ _ : X, (1 : ℝ) ∂μ = 1
      simp⟩

@[simp] theorem graphState_apply (g : C(X, K)) (F : C(X × K, ℝ)) :
    (graphState (μ := μ) g).1 F = ∫ x, F (x, g x) ∂μ := rfl

/-- Pull a continuous scalar function on the source back along the first
projection of the graph product. -/
def continuousMapFst (F : C(X, ℝ)) : C(X × K, ℝ) :=
  F.comp ⟨Prod.fst, continuous_fst⟩

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] [CompactSpace K] in
@[simp] theorem continuousMapFst_apply (F : C(X, ℝ)) (x : X) (k : K) :
    continuousMapFst (K := K) F (x, k) = F x := rfl

/-- The empirical graph state of the first `N+1` continuous maps. Its Riesz
measure is the joint probability measure whose conditional law at `x` is the
uniform empirical measure of `g 0 x, ..., g N x`. -/
noncomputable def empiricalGraphState (g : ℕ → C(X, K)) (N : ℕ) :
    PositiveNormalizedState (X × K) :=
  ⟨(N + 1 : ℝ)⁻¹ • ∑ n ∈ Finset.range (N + 1), (graphState (μ := μ) (g n)).1, by
    constructor
    · intro F hF
      change 0 ≤ ((N + 1 : ℝ)⁻¹ •
        ∑ n ∈ Finset.range (N + 1), (graphState (μ := μ) (g n)).1) F
      rw [← WeakDual.toStrongDual_apply, map_smul, map_sum, smul_apply, sum_apply]
      change 0 ≤ (N + 1 : ℝ)⁻¹ *
        ∑ n ∈ Finset.range (N + 1), (graphState (μ := μ) (g n)).1 F
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun n _ ↦
        (graphState (μ := μ) (g n)).2.1 F hF)
    · change (((N + 1 : ℝ)⁻¹ •
        ∑ n ∈ Finset.range (N + 1), (graphState (μ := μ) (g n)).1) 1) = 1
      rw [← WeakDual.toStrongDual_apply, map_smul, map_sum, smul_apply, sum_apply]
      simp [positiveNormalizedStates_one (X × K), Nat.cast_add_one_ne_zero]⟩

theorem empiricalGraphState_apply (g : ℕ → C(X, K)) (N : ℕ)
    (F : C(X × K, ℝ)) :
    (empiricalGraphState (μ := μ) g N).1 F =
      (N + 1 : ℝ)⁻¹ * ∑ n ∈ Finset.range (N + 1),
        ∫ x, F (x, g n x) ∂μ := by
  change (((N + 1 : ℝ)⁻¹ •
    ∑ n ∈ Finset.range (N + 1), (graphState (μ := μ) (g n)).1) F) = _
  rw [← WeakDual.toStrongDual_apply, map_smul, map_sum, smul_apply, sum_apply]
  rw [smul_eq_mul]
  congr 1

/-- Every empirical graph state has first marginal `μ`, expressed against
continuous scalar test functions. -/
theorem empiricalGraphState_continuousMapFst (g : ℕ → C(X, K)) (N : ℕ)
    (F : C(X, ℝ)) :
    (empiricalGraphState (μ := μ) g N).1 (continuousMapFst (K := K) F) =
      ∫ x, F x ∂μ := by
  rw [empiricalGraphState_apply]
  simp [continuousMapFst, Nat.cast_add_one_ne_zero]

/-- Empirical graph states have a weak-star cluster point. This packages the
compactness step which produces the limiting joint state before its countable
fiber disintegration. -/
theorem exists_mapClusterPt_empiricalGraphState
    [T2Space X] [T2Space K] [Nonempty X] [Nonempty K]
    (g : ℕ → C(X, K)) :
    ∃ L : PositiveNormalizedState (X × K),
      MapClusterPt L.1 atTop
        (fun N ↦ (empiricalGraphState (μ := μ) g N).1) := by
  have hmem : ∀ᶠ N in atTop,
      (empiricalGraphState (μ := μ) g N).1 ∈
        positiveNormalizedStates (X × K) := by
    filter_upwards [] with N
    exact (empiricalGraphState (μ := μ) g N).2
  obtain ⟨L, hL, hcluster⟩ :=
    (isCompact_positiveNormalizedStates (X × K)).exists_mapClusterPt
      (tendsto_principal.mpr hmem)
  exact ⟨⟨L, hL⟩, hcluster⟩

/-- A weak-star cluster state of the empirical graph states retains the fixed
first marginal, at the level of all continuous scalar test functions. -/
theorem mapClusterPt_empiricalGraphState_continuousMapFst
    [T2Space X] [T2Space K]
    (g : ℕ → C(X, K)) (L : PositiveNormalizedState (X × K))
    (hL : MapClusterPt L.1 atTop
      (fun N ↦ (empiricalGraphState (μ := μ) g N).1))
    (F : C(X, ℝ)) :
    L.1 (continuousMapFst (K := K) F) = ∫ x, F x ∂μ := by
  let u : ℕ → WeakDual ℝ C(X × K, ℝ) :=
    fun N ↦ (empiricalGraphState (μ := μ) g N).1
  let G : Filter ℕ := comap u (𝓝 L.1) ⊓ atTop
  haveI : NeBot G := neBot_inf_comap_iff_map'.mpr hL
  have hu : Tendsto u G (𝓝 L.1) :=
    tendsto_iff_comap.mpr (show G ≤ comap u (𝓝 L.1) from inf_le_left)
  have heval : Tendsto
      (fun N ↦ (u N) (continuousMapFst (K := K) F)) G
      (𝓝 (L.1 (continuousMapFst (K := K) F))) :=
    (WeakDual.eval_continuous (continuousMapFst (K := K) F)).tendsto L.1 |>.comp hu
  have hconst : Tendsto
      (fun N ↦ (u N) (continuousMapFst (K := K) F)) G
      (𝓝 (∫ x, F x ∂μ)) := by
    have heq : (fun N ↦ (u N) (continuousMapFst (K := K) F)) =
        (fun _ : ℕ ↦ ∫ x, F x ∂μ) := by
      funext N
      exact empiricalGraphState_continuousMapFst (μ := μ) g N F
    rw [heq]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique heval hconst

/-- The Riesz measure of a normalized state has total mass one. -/
theorem stateRieszMeasure_univ_eq_one
    [T2Space X] [T2Space K] [MeasurableSpace K] [BorelSpace (X × K)]
    (L : PositiveNormalizedState (X × K)) :
    stateRieszMeasure (X × K) L Set.univ = 1 := by
  apply (ENNReal.toReal_eq_one_iff _).mp
  rw [← measureReal_def]
  have h := integral_stateRieszMeasure (X × K) L (1 : C(X × K, ℝ))
  simpa [MeasureTheory.integral_const, positiveNormalizedStates_one] using h

/-- If a state on the product has the prescribed source marginal against
every continuous scalar test, then the first marginal of its Riesz measure
is literally the prescribed measure. -/
theorem stateRieszMeasure_fst_eq_of_continuousMapFst
    [T2Space X] [T2Space K] [HasOuterApproxClosed X]
    [MeasurableSpace K] [BorelSpace (X × K)]
    (L : PositiveNormalizedState (X × K))
    (hL : ∀ F : C(X, ℝ),
      L.1 (continuousMapFst (K := K) F) = ∫ x, F x ∂μ) :
    (stateRieszMeasure (X × K) L).fst = μ := by
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [Measure.fst]
  rw [MeasureTheory.integral_map measurable_fst.aemeasurable
    f.continuous.aestronglyMeasurable]
  change (∫ z : X × K,
    (continuousMapFst (K := K) f.toContinuousMap) z
      ∂(stateRieszMeasure (X × K) L)) = _
  rw [integral_stateRieszMeasure]
  exact hL f.toContinuousMap

/-- The Riesz measure of a cluster state of empirical graph states has first
marginal exactly `μ`. -/
theorem stateRieszMeasure_fst_eq_of_mapClusterPt_empiricalGraphState
    [T2Space X] [T2Space K] [HasOuterApproxClosed X]
    [MeasurableSpace K] [BorelSpace (X × K)]
    (g : ℕ → C(X, K)) (L : PositiveNormalizedState (X × K))
    (hL : MapClusterPt L.1 atTop
      (fun N ↦ (empiricalGraphState (μ := μ) g N).1)) :
    (stateRieszMeasure (X × K) L).fst = μ :=
  stateRieszMeasure_fst_eq_of_continuousMapFst L
    (mapClusterPt_empiricalGraphState_continuousMapFst g L hL)

end GraphStates





variable {Ω E ι : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] {μ : Measure Ω}

/-- A positive finite Cesaro average of points in a convex set remains in
that set.  The hypotheses are a.e. for each iterate; countability lets us
choose one conull set on which all iterate hypotheses hold. -/
theorem ae_cesaro_mem_of_ae_mem [NormedSpace ℝ E]
    {f : ℕ → Ω → E} {s : Set E} (hs : Convex ℝ s)
    (hf : ∀ n, ∀ᵐ x ∂μ, f n x ∈ s) {N : ℕ} (hN : N ≠ 0) :
    ∀ᵐ x ∂μ, (N : ℝ)⁻¹ • (∑ n ∈ Finset.range N, f n x) ∈ s := by
  rw [← ae_all_iff] at hf
  filter_upwards [hf] with x hx
  rw [Finset.smul_sum]
  apply hs.sum_mem (w := fun _ : ℕ ↦ (N : ℝ)⁻¹)
  · intro _ _
    positivity
  · simp [hN]
  · intro n hn
    exact hx n

/-- A uniformly a.e. norm-bounded family on a finite measure space is
uniformly integrable in Bochner `L¹`.

This is the uniform-integrability half of the specialized Diestel criterion
needed for stationary word averages.  The weak compactness conclusion is a
separate, currently absent theorem. -/
theorem uniformIntegrable_one_of_ae_norm_le [IsFiniteMeasure μ]
    {f : ι → Ω → E} (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (C : ℝ) (hC : ∀ i, ∀ᵐ x ∂μ, ‖f i x‖ ≤ C) :
    UniformIntegrable f 1 μ := by
  apply uniformIntegrable_of le_rfl ENNReal.one_ne_top hf
  intro ε hε
  let D : NNReal := Real.toNNReal C + 1
  refine ⟨D, fun i ↦ ?_⟩
  have hzero : ({x | D ≤ ‖f i x‖₊}.indicator (f i)) =ᵐ[μ] 0 := by
    filter_upwards [hC i] with x hx
    have hxnot : x ∉ {x | D ≤ ‖f i x‖₊} := by
      intro hDx
      have hreal : (Real.toNNReal C : ℝ) + 1 ≤ ‖f i x‖ := by
        exact_mod_cast hDx
      have hCle : C ≤ (Real.toNNReal C : ℝ) := by
        by_cases hC0 : 0 ≤ C
        · rw [Real.coe_toNNReal C hC0]
        · exact (le_of_not_ge hC0).trans (NNReal.coe_nonneg _)
      linarith
    simp [Set.indicator_of_notMem hxnot]
  calc
    eLpNorm ({x | D ≤ ‖f i x‖₊}.indicator (f i)) 1 μ
        = eLpNorm (0 : Ω → E) 1 μ := eLpNorm_congr_ae hzero
    _ = 0 := eLpNorm_zero
    _ ≤ ENNReal.ofReal ε := bot_le

/-- Cesaro averages of a uniformly a.e. bounded, strongly measurable family
are uniformly integrable in Bochner `L¹`. -/
theorem uniformIntegrable_one_cesaro_of_ae_norm_le
    [NormedSpace ℝ E] [IsFiniteMeasure μ]
    {f : ℕ → Ω → E} (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (C : ℝ) (hC : ∀ n, ∀ᵐ x ∂μ, ‖f n x‖ ≤ C) :
    UniformIntegrable
      (fun N : ℕ ↦ (N : ℝ)⁻¹ • (∑ n ∈ Finset.range N, f n)) 1 μ := by
  exact uniformIntegrable_average le_rfl
    (uniformIntegrable_one_of_ae_norm_le hf C hC)

end IndependentZeroBlocks
