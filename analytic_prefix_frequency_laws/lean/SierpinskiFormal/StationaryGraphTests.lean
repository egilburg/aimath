import SierpinskiFormal.StationaryCompactness
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.CompactOpen

set_option autoImplicit false

/-!
# Extending graph-state convergence to measurable compact-valued tests

Weak-star convergence of graph states initially controls continuous tests on
the product.  A common first marginal makes approximation in
`L¹(μ; C(K, ℝ))` uniform over all the graph measures, so the convergence
extends to strongly measurable integrable fields of continuous fiber tests.
-/

noncomputable section

namespace IndependentZeroBlocks

open Filter Topology MeasureTheory

section GraphMeasures

variable {X K : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
  [BorelSpace (X × K)] [HasOuterApproxClosed (X × K)]
  {μ : Measure X} [IsProbabilityMeasure μ]

/-- The Riesz measure of a graph state is literally the pushforward of the
source measure by the graph map. -/
theorem stateRieszMeasure_graphState_eq_map (g : C(X, K)) :
    stateRieszMeasure (X × K) (graphState (μ := μ) g) =
      Measure.map (fun x ↦ (x, g x)) μ := by
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro F
  change (∫ z, F.toContinuousMap z ∂stateRieszMeasure
      (X × K) (graphState (μ := μ) g)) = _
  rw [integral_stateRieszMeasure, graphState_apply]
  rw [integral_map]
  · rfl
  · exact (measurable_id.prodMk g.measurable).aemeasurable
  · exact F.continuous.aestronglyMeasurable

/-- The positive measure obtained by uniformly averaging the first `N+1`
graph pushforwards. -/
noncomputable def empiricalGraphMeasure (g : ℕ → C(X, K)) (N : ℕ) :
    Measure (X × K) :=
  ENNReal.ofReal ((N + 1 : ℝ)⁻¹) • ∑ n ∈ Finset.range (N + 1),
    Measure.map (fun x ↦ (x, g n x)) μ

/-- The Riesz measure of an empirical graph state is the literal uniform
finite average of its graph pushforwards. -/
theorem stateRieszMeasure_empiricalGraphState_eq (g : ℕ → C(X, K)) (N : ℕ) :
    stateRieszMeasure (X × K) (empiricalGraphState (μ := μ) g N) =
      empiricalGraphMeasure (μ := μ) g N := by
  letI : IsFiniteMeasure (empiricalGraphMeasure (μ := μ) g N) := by
    apply IsFiniteMeasure.mk
    have hm (n : ℕ) : Measure.map (fun x ↦ (x, g n x)) μ Set.univ = 1 := by
      change Measure.map (fun x ↦ (id x, g n x)) μ Set.univ = 1
      rw [Measure.map_apply_of_aemeasurable
        (measurable_id.prodMk (g n).measurable).aemeasurable MeasurableSet.univ]
      simp
    rw [empiricalGraphMeasure, Measure.smul_apply]
    change ENNReal.ofReal ((N + 1 : ℝ)⁻¹) *
      (∑ n ∈ Finset.range (N + 1),
        Measure.map (fun x ↦ (x, g n x)) μ) Set.univ < ⊤
    have heval (s : Finset ℕ) :
        (∑ n ∈ s, Measure.map (fun x ↦ (x, g n x)) μ) Set.univ =
        ∑ n ∈ s, Measure.map (fun x ↦ (x, g n x)) μ Set.univ := by
      classical
      induction s using Finset.induction_on with
      | empty => simp
      | @insert n s hn ih => simp [hn, ih, Measure.add_apply]
    rw [heval (Finset.range (N + 1))]
    simp_rw [hm]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.natCast_lt_top _)
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro F
  change (∫ z, F.toContinuousMap z ∂stateRieszMeasure
      (X × K) (empiricalGraphState (μ := μ) g N)) = _
  rw [integral_stateRieszMeasure, empiricalGraphState_apply]
  have hInt (n : ℕ) : Integrable F
      (Measure.map (fun x ↦ (x, g n x)) μ) := by
    letI : IsFiniteMeasure (Measure.map (fun x ↦ (x, g n x)) μ) :=
      Measure.isFiniteMeasure_map μ _
    apply (integrable_const ‖F‖).mono'
    · exact F.continuous.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun z ↦
        BoundedContinuousFunction.norm_coe_le_norm F z
  rw [empiricalGraphMeasure, integral_smul_measure,
    integral_finset_sum_measure (fun n _ ↦ hInt n)]
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ (N + 1 : ℝ)⁻¹)]
  rw [smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  simpa only [Function.comp_apply, id_eq, BoundedContinuousFunction.coe_toContinuousMap] using
    (integral_map
      (measurable_id.prodMk (g n).measurable).aemeasurable
      F.continuous.aestronglyMeasurable).symm

end GraphMeasures

/-- Evaluate a field of continuous fiber functions on a point of the product. -/
def fiberTest {X K : Type*} [TopologicalSpace K]
    (Φ : X → C(K, ℝ)) (z : X × K) : ℝ :=
  Φ z.1 z.2

theorem stronglyMeasurable_fiberTest
    {X K : Type*} [MeasurableSpace X]
    [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [TopologicalSpace.PseudoMetrizableSpace K]
    [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
    (Φ : X → C(K, ℝ)) (hΦ : StronglyMeasurable Φ) :
    StronglyMeasurable (fiberTest Φ) := by
  have hfirst : StronglyMeasurable (fun z : X × K ↦ Φ z.1) :=
    hΦ.comp_measurable measurable_fst
  have hsecond : StronglyMeasurable (fun z : X × K ↦ z.2) :=
    measurable_snd.stronglyMeasurable
  exact continuous_eval.comp_stronglyMeasurable (hfirst.prodMk hsecond)

/-- Integration of a strongly measurable integrable fiber test against an
empirical graph-state measure is exactly the uniform finite average of its
integrals along the individual graphs. -/
theorem integral_fiberTest_empiricalGraphState
    {X K : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [TopologicalSpace.PseudoMetrizableSpace K]
    [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
    [BorelSpace (X × K)] [HasOuterApproxClosed (X × K)]
    {μ : Measure X} [IsProbabilityMeasure μ]
    (g : ℕ → C(X, K)) (N : ℕ) (Φ : X → C(K, ℝ))
    (hΦ : StronglyMeasurable Φ) (hΦi : Integrable Φ μ) :
    (∫ z, fiberTest Φ z
        ∂stateRieszMeasure (X × K) (empiricalGraphState (μ := μ) g N)) =
      (N + 1 : ℝ)⁻¹ * ∑ n ∈ Finset.range (N + 1),
        ∫ x, Φ x (g n x) ∂μ := by
  rw [stateRieszMeasure_empiricalGraphState_eq (μ := μ) g N]
  have hjoint : StronglyMeasurable (fiberTest Φ) :=
    stronglyMeasurable_fiberTest Φ hΦ
  have hInt (n : ℕ) : Integrable (fiberTest Φ)
      (Measure.map (fun x ↦ (x, g n x)) μ) := by
    apply (integrable_map_measure hjoint.aestronglyMeasurable
      (measurable_id.prodMk (g n).measurable).aemeasurable).mpr
    apply hΦi.norm.mono'
    · exact (hjoint.comp_measurable
        (measurable_id.prodMk (g n).measurable)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x ↦ by
        simpa [fiberTest] using
          (ContinuousMap.norm_coe_le_norm (Φ x) (g n x))
  rw [empiricalGraphMeasure, integral_smul_measure,
    integral_finset_sum_measure (fun n _ ↦ hInt n)]
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ (N + 1 : ℝ)⁻¹)]
  rw [smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  simpa only [fiberTest, Function.comp_apply, id_eq] using
    (integral_map
      (measurable_id.prodMk (g n).measurable).aemeasurable
      hjoint.aestronglyMeasurable)

/-- Pulling an integrable scalar function back along the first projection is
integrable for every measure having first marginal `μ`. -/
theorem integrable_comp_fst_of_fst_eq
    {X K : Type*} [MeasurableSpace X] [MeasurableSpace K]
    {ν : Measure (X × K)} {μ : Measure X} (hν : ν.fst = μ)
    {f : X → ℝ} (hf : Integrable f μ) :
    Integrable (fun z : X × K ↦ f z.1) ν := by
  have hf' : Integrable f ν.fst := by simpa [hν] using hf
  exact hf'.comp_aemeasurable measurable_fst.aemeasurable

theorem integral_comp_fst_of_fst_eq
    {X K : Type*} [MeasurableSpace X] [MeasurableSpace K]
    {ν : Measure (X × K)} {μ : Measure X} (hν : ν.fst = μ)
    {f : X → ℝ} (hf : AEStronglyMeasurable f μ) :
    (∫ z : X × K, f z.1 ∂ν) = ∫ x, f x ∂μ := by
  have hf' : AEStronglyMeasurable f ν.fst := by simpa [hν] using hf
  calc
    (∫ z : X × K, f z.1 ∂ν) = ∫ x, f x ∂ν.fst := by
      change (∫ z : X × K, f z.1 ∂ν) = ∫ x, f x ∂Measure.map Prod.fst ν
      exact (integral_map measurable_fst.aemeasurable hf').symm
    _ = ∫ x, f x ∂μ := by rw [hν]

/-- The error of a fiber test is controlled solely by the `L¹` error of its
field in the common first marginal. -/
theorem norm_integral_fiberTest_sub_le
    {X K : Type*} [MeasurableSpace X]
    [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [TopologicalSpace.PseudoMetrizableSpace K]
    [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
    {ν : Measure (X × K)} {μ : Measure X} (hν : ν.fst = μ)
    (Φ Ψ : X → C(K, ℝ))
    (hΦ : StronglyMeasurable Φ) (hΨ : StronglyMeasurable Ψ)
    (hΦi : Integrable Φ μ) (hΨi : Integrable Ψ μ)
    (hint : Integrable (fun x ↦ ‖Φ x - Ψ x‖) μ) :
    ‖(∫ z, fiberTest Φ z ∂ν) - ∫ z, fiberTest Ψ z ∂ν‖ ≤
      ∫ x, ‖Φ x - Ψ x‖ ∂μ := by
  have hdomint : Integrable (fun z : X × K ↦ ‖Φ z.1 - Ψ z.1‖) ν :=
    integrable_comp_fst_of_fst_eq hν hint
  have hΦjoint : StronglyMeasurable (fiberTest Φ) :=
    stronglyMeasurable_fiberTest Φ hΦ
  have hΨjoint : StronglyMeasurable (fiberTest Ψ) :=
    stronglyMeasurable_fiberTest Ψ hΨ
  have hΦnormint : Integrable (fun z : X × K ↦ ‖Φ z.1‖) ν :=
    integrable_comp_fst_of_fst_eq hν hΦi.norm
  have hΨnormint : Integrable (fun z : X × K ↦ ‖Ψ z.1‖) ν :=
    integrable_comp_fst_of_fst_eq hν hΨi.norm
  have hΦjointInt : Integrable (fiberTest Φ) ν :=
    hΦnormint.mono' hΦjoint.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z ↦
        ContinuousMap.norm_coe_le_norm (Φ z.1) z.2)
  have hΨjointInt : Integrable (fiberTest Ψ) ν :=
    hΨnormint.mono' hΨjoint.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z ↦
        ContinuousMap.norm_coe_le_norm (Ψ z.1) z.2)
  have hsubint : Integrable (fun z ↦ fiberTest Φ z - fiberTest Ψ z) ν :=
    hdomint.mono' (hΦjoint.sub hΨjoint).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z ↦ by
        simpa [fiberTest, Real.norm_eq_abs] using
          ContinuousMap.norm_coe_le_norm (Φ z.1 - Ψ z.1) z.2)
  rw [← integral_sub hΦjointInt hΨjointInt]
  refine (norm_integral_le_of_norm_le hdomint ?_).trans_eq ?_
  · exact Filter.Eventually.of_forall fun z ↦ by
      simpa [fiberTest, Real.norm_eq_abs] using
        ContinuousMap.norm_coe_le_norm (Φ z.1 - Ψ z.1) z.2
  · exact integral_comp_fst_of_fst_eq hν hint.aestronglyMeasurable

/-- Along any filter on which positive normalized states converge weak-star,
their Riesz measures converge on every strongly measurable integrable field
of continuous fiber tests, provided all first marginals are the same. -/
theorem tendsto_integral_fiberTest_of_tendsto_states_fixed_fst
    {X K : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [NormalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [TopologicalSpace.PseudoMetrizableSpace K]
    [MeasurableSpace K] [BorelSpace K]
    [SecondCountableTopology K]
    [SecondCountableTopologyEither X C(K, ℝ)]
    {μ : Measure X} [IsProbabilityMeasure μ] [μ.WeaklyRegular]
    (u : ℕ → PositiveNormalizedState (X × K))
    (L : PositiveNormalizedState (X × K)) (F : Filter ℕ)
    (hu : Tendsto (fun n ↦ (u n).1) F (𝓝 L.1))
    (hufst : ∀ n, (stateRieszMeasure (X × K) (u n)).fst = μ)
    (hLfst : (stateRieszMeasure (X × K) L).fst = μ)
    (Φ : X → C(K, ℝ)) (hΦm : StronglyMeasurable Φ)
    (hΦi : Integrable Φ μ) :
    Tendsto
      (fun n ↦ ∫ z, fiberTest Φ z
        ∂stateRieszMeasure (X × K) (u n)) F
      (𝓝 (∫ z, fiberTest Φ z ∂stateRieszMeasure (X × K) L)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨Ψb, hΨerr, hΨint⟩ :=
    hΦi.exists_boundedContinuous_integral_sub_le (ε := ε / 4) (by positivity)
  let Ψ : C(X, C(K, ℝ)) := Ψb.toContinuousMap
  let test : C(X × K, ℝ) := Ψ.uncurry
  have hΨm : StronglyMeasurable (fun x ↦ Ψ x) := Ψ.continuous.stronglyMeasurable
  have herrint : Integrable (fun x ↦ ‖Φ x - Ψ x‖) μ := by
    exact hΦi.sub hΨint |>.norm
  have hcont : Tendsto
      (fun n ↦ ∫ z, fiberTest (fun x ↦ Ψ x) z
        ∂stateRieszMeasure (X × K) (u n)) F
      (𝓝 (∫ z, fiberTest (fun x ↦ Ψ x) z
        ∂stateRieszMeasure (X × K) L)) := by
    have heval := (WeakDual.eval_continuous test).tendsto L.1 |>.comp hu
    convert heval using 1
    · funext n
      simpa [test, Ψ, fiberTest, Function.uncurry] using
        integral_stateRieszMeasure (X × K) (u n) test
    · congr 1
      simpa [test, Ψ, fiberTest, Function.uncurry] using
        integral_stateRieszMeasure (X × K) L test
  have hevent := (Metric.tendsto_nhds.mp hcont (ε / 2) (by positivity))
  filter_upwards [hevent] with n hn
  have hnerr := norm_integral_fiberTest_sub_le (hufst n)
    Φ (fun x ↦ Ψ x) hΦm hΨm hΦi hΨint herrint
  have hLerr := norm_integral_fiberTest_sub_le hLfst
    Φ (fun x ↦ Ψ x) hΦm hΨm hΦi hΨint herrint
  have hbound : ∫ x, ‖Φ x - Ψ x‖ ∂μ ≤ ε / 4 := by
    simpa [Ψ] using hΨerr
  have hnerr' : dist
      (∫ z, fiberTest Φ z ∂stateRieszMeasure (X × K) (u n))
      (∫ z, fiberTest (fun x ↦ Ψ x) z
        ∂stateRieszMeasure (X × K) (u n)) ≤ ε / 4 := by
    simpa [Real.dist_eq] using hnerr.trans hbound
  have hLerr' : dist
      (∫ z, fiberTest (fun x ↦ Ψ x) z ∂stateRieszMeasure (X × K) L)
      (∫ z, fiberTest Φ z ∂stateRieszMeasure (X × K) L) ≤ ε / 4 := by
    rw [Real.dist_eq, abs_sub_comm]
    exact hLerr.trans hbound
  exact lt_of_le_of_lt (dist_triangle4 _ _ _ _) (by linarith)

/-- `L¹`-bundled form.  The canonical representative of an `L¹` field is
strongly measurable, so this version is convenient after constructing a
dual test field only up to almost-everywhere equality. -/
theorem tendsto_integral_fiberTest_L1_of_tendsto_states_fixed_fst
    {X K : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [NormalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [TopologicalSpace.PseudoMetrizableSpace K]
    [MeasurableSpace K] [BorelSpace K]
    [SecondCountableTopology K]
    [SecondCountableTopologyEither X C(K, ℝ)]
    {μ : Measure X} [IsProbabilityMeasure μ] [μ.WeaklyRegular]
    (u : ℕ → PositiveNormalizedState (X × K))
    (L : PositiveNormalizedState (X × K)) (F : Filter ℕ)
    (hu : Tendsto (fun n ↦ (u n).1) F (𝓝 L.1))
    (hufst : ∀ n, (stateRieszMeasure (X × K) (u n)).fst = μ)
    (hLfst : (stateRieszMeasure (X × K) L).fst = μ)
    (Φ : Lp C(K, ℝ) 1 μ) :
    Tendsto
      (fun n ↦ ∫ z, fiberTest (fun x ↦ Φ x) z
        ∂stateRieszMeasure (X × K) (u n)) F
      (𝓝 (∫ z, fiberTest (fun x ↦ Φ x) z
        ∂stateRieszMeasure (X × K) L)) :=
  tendsto_integral_fiberTest_of_tendsto_states_fixed_fst
    u L F hu hufst hLfst (fun x ↦ Φ x)
      (Lp.stronglyMeasurable Φ) (L1.integrable_coeFn Φ)

end IndependentZeroBlocks
