import SierpinskiFormal.StationaryL1Skew
import SierpinskiFormal.StationaryMaximal
import SierpinskiFormal.WeakMeanErgodic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

/-!
# From an `L¹` mean decomposition to pathwise skew convergence

This file joins the mean-ergodic and maximal stages.  A fixed `L¹` vector plus
coboundaries with finite-range transfer functions gives almost-everywhere
convergence of all skew Cesàro averages.  The finite-range representatives are
globally bounded, so their coboundaries telescope pointwise.
-/

noncomputable section

set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 3

open Function Set Filter Topology MeasureTheory Bornology
open scoped ENNReal BigOperators

namespace IndependentZeroBlocks

section Terminal

variable {Ω A E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [Fintype A] [DecidableEq A] [MeasurableSpace A] [MeasurableSingletonClass A]
  {μ : Measure Ω} [IsFiniteMeasure μ]

/-- Simple `L¹` transfer functions are sufficient to approximate every point
in the closed range of a continuous linear coboundary operator. -/
theorem exists_simple_coboundary_approx_of_mem_closure_range
    (V : Lp E 1 μ →L[ℝ] Lp E 1 μ) (v : Lp E 1 μ)
    (hv : v ∈ closure (LinearMap.range V.toLinearMap : Set (Lp E 1 μ))) :
    ∃ y : ℕ → Lp.simpleFunc E 1 μ,
      Tendsto (fun k => V (y k : Lp E 1 μ)) atTop (𝓝 v) := by
  let S : Set (Lp E 1 μ) := Lp.simpleFunc E 1 μ
  have hSdense : Dense S := Lp.simpleFunc.dense ENNReal.one_ne_top
  have hrange : (LinearMap.range V.toLinearMap : Set (Lp E 1 μ)) ⊆
      closure (V '' S) := by
    rintro _ ⟨z, rfl⟩
    exact V.continuous.range_subset_closure_image_dense hSdense ⟨z, rfl⟩
  have hvS : v ∈ closure (V '' S) :=
    closure_minimal hrange isClosed_closure hv
  obtain ⟨b, hbmem, hb⟩ := mem_closure_iff_seq_limit.mp hvS
  choose z hzS hz using hbmem
  let y : ℕ → Lp.simpleFunc E 1 μ := fun k => ⟨z k, hzS k⟩
  refine ⟨y, ?_⟩
  exact hb.congr' (Filter.Eventually.of_forall fun k => by
    simpa only [y] using (hz k).symm)

/-- Norm convergence of Cesàro averages of a contraction determines the
standard mean-ergodic decomposition: the limit is fixed and the initial
vector minus the limit lies in the closed coboundary range. -/
theorem fixed_and_sub_mem_closure_range_of_tendsto_birkhoffAverage
    (V : Lp E 1 μ →L[ℝ] Lp E 1 μ) (hV : LipschitzWith 1 V)
    (q a : Lp E 1 μ)
    (hmean : Tendsto (birkhoffAverage ℝ V id · q) atTop (𝓝 a)) :
    IsFixedPt V a ∧
      q - a ∈ closure (LinearMap.range (V.toLinearMap - 1) : Set (Lp E 1 μ)) := by
  have horbit : IsBounded (Set.range (id <| V^[·] q)) :=
    isBounded_iff_forall_norm_le.2 ⟨‖q‖, Set.forall_mem_range.2 fun n => by
      have hz : V^[n] 0 = 0 := iterate_map_zero (V : Lp E 1 μ →+ Lp E 1 μ) n
      simpa [hz] using (hV.iterate n).dist_le_mul q 0⟩
  have hres0 : Tendsto (fun n =>
      V (birkhoffAverage ℝ V id n q) - birkhoffAverage ℝ V id n q)
      atTop (𝓝 0) := by
    simpa only [map_birkhoffAverage_initial] using
      tendsto_birkhoffAverage_apply_sub_birkhoffAverage ℝ horbit
  have hreslim : Tendsto (fun n =>
      V (birkhoffAverage ℝ V id n q) - birkhoffAverage ℝ V id n q)
      atTop (𝓝 (V a - a)) :=
    (V.continuous.continuousAt.tendsto.comp hmean).sub hmean
  have hfixed : IsFixedPt V a := by
    exact sub_eq_zero.mp (tendsto_nhds_unique hreslim hres0)
  let W := LinearMap.range (V.toLinearMap - 1)
  have hsub : Tendsto (fun n => q - birkhoffAverage ℝ V id n q)
      atTop (𝓝 (q - a)) := tendsto_const_nhds.sub hmean
  have hmem : ∀ᶠ n in atTop, q - birkhoffAverage ℝ V id n q ∈ W := by
    filter_upwards [eventually_ne_atTop 0] with n hn
    have hh := W.neg_mem (birkhoffAverage_sub_mem_range V q hn)
    simpa only [neg_sub] using hh
  exact ⟨hfixed, mem_closure_of_tendsto hsub hmem⟩

set_option maxHeartbeats 150000 in
/-- A norm limit of contraction Cesàro averages admits simple transfer
functions whose coboundaries converge to the transient component. -/
theorem exists_fixed_simple_coboundary_tendsto_sub_of_tendsto_birkhoffAverage
    (V : Lp E 1 μ →L[ℝ] Lp E 1 μ) (hV : LipschitzWith 1 V)
    (q a : Lp E 1 μ)
    (hmean : Tendsto (birkhoffAverage ℝ V id · q) atTop (𝓝 a)) :
    ∃ y : ℕ → Lp.simpleFunc E 1 μ,
      IsFixedPt V a ∧ Tendsto (fun k =>
        (V - 1) (y k : Lp E 1 μ)) atTop (𝓝 (q - a)) := by
  obtain ⟨ha, hqa⟩ :=
    fixed_and_sub_mem_closure_range_of_tendsto_birkhoffAverage
      V hV q a hmean
  have hmap : (V - 1).toLinearMap = V.toLinearMap - 1 := by
    ext z
    rfl
  have hqa' : q - a ∈ closure
      (LinearMap.range (V - 1).toLinearMap : Set (Lp E 1 μ)) := by
    rw [hmap]
    exact hqa
  obtain ⟨y, hy⟩ := exists_simple_coboundary_approx_of_mem_closure_range
    (V - 1) (q - a) hqa'
  exact ⟨y, ha, hy⟩

/-- Adding the fixed component converts convergence of raw coboundaries to
convergence of the fixed-plus-coboundary approximation. -/
theorem tendsto_fixed_add_simple_coboundary_of_tendsto_sub
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (V : F →L[ℝ] F) (q a : F) (y : ℕ → F)
    (hy : Tendsto (fun k => (V - 1) (y k))
      atTop (𝓝 (q - a))) :
    Tendsto (fun k => a + (V (y k) - y k)) atTop (𝓝 q) := by
  have hsum := (show Tendsto (fun _ : ℕ => a) atTop (𝓝 a) from
    tendsto_const_nhds).add hy
  simpa only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    add_sub_cancel] using hsum

/-- A fixed `L¹` point plus finite-range coboundaries converging in `L¹` to
`q` yields almost-everywhere pointwise convergence of the skew averages of the
canonical representative of `q`. -/
theorem ae_exists_tendsto_stationarySkewAverage_of_fixed_simple_coboundary_approx
    (R : A → E →L[ℝ] E) (hR : ∀ a, ‖R a‖ ≤ 1)
    (letter : Ω → A) (hletter : Measurable letter)
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (q a : Lp E 1 μ)
    (ha : stationarySkewL1CLM R hR letter hletter T hT a = a)
    (y : ℕ → Lp.simpleFunc E 1 μ)
    (happrox : Tendsto (fun k => a +
      (stationarySkewL1CLM R hR letter hletter T hT (y k : Lp E 1 μ) -
        (y k : Lp E 1 μ))) atTop (𝓝 q)) :
    ∀ᵐ x ∂μ, ∃ z : E, Tendsto (fun N => birkhoffAverage ℝ
      (stationarySkewApply R letter T) id N (fun x => q x) x)
      atTop (𝓝 z) := by
  let U := stationarySkewL1CLM R hR letter hletter T hT
  let hLp : ℕ → Lp E 1 μ := fun k => a + (U (y k : Lp E 1 μ) - (y k : Lp E 1 μ))
  let p : Ω → E := fun x => a x
  let ys : ℕ → Ω → E := fun k => Lp.simpleFunc.toSimpleFunc (y k)
  have hp : stationarySkewApply R letter T p =ᵐ[μ] p := by
    have hu := stationarySkewL1_coeFn R hR letter hletter T hT a
    change (fun x => U a x) =ᵐ[μ]
      stationarySkewL1Representative R letter T a at hu
    rw [ha] at hu
    have hu' : (fun x => a x) =ᵐ[μ]
        stationarySkewL1Representative R letter T a := hu
    exact hu'.symm
  have hys : ∀ k, ys k =ᵐ[μ] fun x => (y k : Lp E 1 μ) x :=
    fun k => Lp.simpleFunc.toSimpleFunc_eq_toFun (y k)
  have hcore : ∀ k, (fun x => hLp k x) =ᵐ[μ]
      p + (stationarySkewApply R letter T (ys k) - ys k) := by
    intro k
    have hysT := hT.quasiMeasurePreserving.ae_eq_comp (hys k)
    have hU := stationarySkewL1_coeFn R hR letter hletter T hT
      (y k : Lp E 1 μ)
    filter_upwards [Lp.coeFn_add a (U (y k : Lp E 1 μ) - (y k : Lp E 1 μ)),
      Lp.coeFn_sub (U (y k : Lp E 1 μ)) (y k : Lp E 1 μ),
      hU, hys k, hysT] with x hadd hsub hUx hyx hyTx
    simp only [hLp, p, ys, Pi.add_apply, Pi.sub_apply]
    rw [hadd]
    simp only [Pi.add_apply]
    rw [hsub]
    simp only [Pi.sub_apply]
    change a x + (stationarySkewL1 R hR letter hletter T hT
      (y k : Lp E 1 μ) x - (y k : Lp E 1 μ) x) = _
    rw [hUx]
    change a x + (R (letter x) ((y k : Lp E 1 μ) (T x)) -
      (y k : Lp E 1 μ) x) =
      a x + (R (letter x) (Lp.simpleFunc.toSimpleFunc (y k) (T x)) -
        Lp.simpleFunc.toSimpleFunc (y k) x)
    rw [← hyx]
    have hyTx' : Lp.simpleFunc.toSimpleFunc (y k) (T x) =
        (y k : Lp E 1 μ) (T x) := by simpa [Function.comp_def] using hyTx
    rw [← hyTx']
  choose C hC using fun k =>
    (Lp.simpleFunc.toSimpleFunc (y k)).finite_range.image norm |>.exists_le
  have hy_bound : ∀ k x, ‖ys k x‖ ≤ C k := by
    intro k x
    apply hC k _
    exact ⟨ys k x, ⟨x, rfl⟩, rfl⟩
  have hcore_conv : ∀ k, ∀ᵐ x ∂μ, ∃ z : E, Tendsto
      (fun N => birkhoffAverage ℝ (stationarySkewApply R letter T)
        id N (fun x => hLp k x) x) atTop (𝓝 z) := by
    intro k
    have hc := ae_tendsto_birkhoffAverage_fixed_add_bounded_coboundary
      R hR letter T hT.quasiMeasurePreserving p (ys k) hp (C k)
      (Filter.Eventually.of_forall (hy_bound k))
    have havg := ae_all_birkhoffAverage_stationarySkewApply_congr
      R letter T hT.quasiMeasurePreserving
      (fun x => hLp k x)
      (p + (stationarySkewApply R letter T (ys k) - ys k)) (hcore k)
    filter_upwards [hc, havg] with x hcx havgx
    exact ⟨p x, hcx.congr' (Filter.Eventually.of_forall fun N => (havgx N).symm)⟩
  have herr_meas : ∀ k, Measurable (fun x => ‖q x - hLp k x‖) := by
    intro k
    exact ((Lp.stronglyMeasurable q).sub (Lp.stronglyMeasurable (hLp k))).norm.measurable
  have herr_int : ∀ k, Integrable (fun x => ‖q x - hLp k x‖) μ := by
    intro k
    have hm : MemLp (fun x => q x - hLp k x) 1 μ :=
      (Lp.memLp q).sub (Lp.memLp (hLp k))
    exact (hm.integrable le_rfl).norm
  have herr_eq : ∀ k, (∫ x, ‖q x - hLp k x‖ ∂μ) = dist q (hLp k) := by
    intro k
    rw [dist_eq_norm, L1.norm_eq_integral_norm]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub q (hLp k)] with x hx
    rw [hx]
    rfl
  have herr_zero : Tendsto (fun k => ∫ x, ‖q x - hLp k x‖ ∂μ)
      atTop (𝓝 0) := by
    have hh : Tendsto hLp atTop (𝓝 q) := by simpa only [hLp, U] using happrox
    have hd : Tendsto (fun k => dist (hLp k) q) atTop (𝓝 0) := by
      simpa only [dist_self] using hh.dist
        (show Tendsto (fun _ : ℕ => q) atTop (𝓝 q) from tendsto_const_nhds)
    exact hd.congr' (Filter.Eventually.of_forall fun k =>
      (dist_comm (hLp k) q).trans (herr_eq k).symm)
  exact ae_exists_tendsto_stationarySkewAverage_of_tendsto_integral_norm_sub
    R hR letter T hT (fun x => q x) (fun k x => hLp k x)
    herr_meas herr_int herr_zero hcore_conv

/-- Terminal analytic theorem.  Once the `L¹` Cesàro averages have a weak
cluster point, the mean-ergodic decomposition, density of simple `L¹`
functions, the scalar maximal inequality, and the Banach closure principle
together give almost-everywhere convergence of the pointwise skew averages.

Thus the sole application-specific input is the displayed weak-cluster
certificate. -/
theorem ae_exists_tendsto_stationarySkewAverage_of_weak_mapClusterPt
    (R : A → E →L[ℝ] E) (hR : ∀ a, ‖R a‖ ≤ 1)
    (letter : Ω → A) (hletter : Measurable letter)
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (q a : Lp E 1 μ)
    (hcluster : MapClusterPt (toWeakSpace ℝ (Lp E 1 μ) a) atTop
      (fun N => toWeakSpace ℝ (Lp E 1 μ)
        (birkhoffAverage ℝ
          (stationarySkewL1CLM R hR letter hletter T hT) id N q))) :
    ∀ᵐ x ∂μ, ∃ z : E, Tendsto (fun N => birkhoffAverage ℝ
      (stationarySkewApply R letter T) id N (fun x => q x) x)
      atTop (𝓝 z) := by
  let U := stationarySkewL1CLM R hR letter hletter T hT
  have hLip : LipschitzWith 1 U :=
    stationarySkewL1CLM_lipschitz R hR letter hletter T hT
  have hmean : Tendsto (birkhoffAverage ℝ U id · q) atTop (𝓝 a) :=
    tendsto_birkhoffAverage_of_weak_mapClusterPt
      (E := Lp E 1 μ) U hLip q a hcluster
  obtain ⟨y, ha, hy⟩ :=
    exists_fixed_simple_coboundary_tendsto_sub_of_tendsto_birkhoffAverage
      U hLip q a hmean
  have happrox := tendsto_fixed_add_simple_coboundary_of_tendsto_sub
    U q a (fun k => (y k : Lp E 1 μ)) hy
  exact ae_exists_tendsto_stationarySkewAverage_of_fixed_simple_coboundary_approx
    R hR letter hletter T hT q a ha y happrox

end Terminal

section WordTerminal

variable {Ω A : Type*} [MeasurableSpace Ω]
  [TopologicalSpace A] [DiscreteTopology A]
  [Fintype A] [DecidableEq A] [MeasurableSpace A] [MeasurableSingletonClass A]
  {μ : Measure Ω} [IsFiniteMeasure μ]

/-- Word-valued endpoint of the stationary analytic argument.  A weak
cluster point for the Bochner `L¹` prefix averages implies almost-sure norm
convergence of the pathwise prefix-frequency functions.  Since the norm on
`BoundedWordFunction A` is the supremum norm, this is convergence uniformly
over every left context. -/
theorem ae_exists_tendsto_stationaryWordCesaro_of_weak_mapClusterPt
    (letter : Ω → A) (hletter : Measurable letter)
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (q : BoundedWordFunction A) (a : Lp (BoundedWordFunction A) 1 μ)
    (hcluster : MapClusterPt
      (toWeakSpace ℝ (Lp (BoundedWordFunction A) 1 μ) a) atTop
      (fun N => toWeakSpace ℝ (Lp (BoundedWordFunction A) 1 μ)
        (birkhoffAverage ℝ (stationaryWordSkewL1CLM letter hletter T hT)
          id N (Lp.const 1 μ q)))) :
    ∀ᵐ x ∂μ, ∃ h : BoundedWordFunction A,
      Tendsto (fun N => stationaryWordCesaro letter T q N x)
        atTop (𝓝 h) := by
  let q₁ : Lp (BoundedWordFunction A) 1 μ := Lp.const 1 μ q
  have hc := ae_exists_tendsto_stationarySkewAverage_of_weak_mapClusterPt
    (fun c => wordRightTranslateCLM (A := A) [c])
    (fun c => wordRightTranslateCLM_norm_le (A := A) [c])
    letter hletter T hT q₁ a hcluster
  have hq : (fun x => q₁ x) =ᵐ[μ] fun _ => q := by
    simpa only [q₁, Function.const_def] using
      (Lp.coeFn_const (α := Ω) (p := (1 : ℝ≥0∞)) μ q)
  have havg := ae_all_birkhoffAverage_stationarySkewApply_congr
    (fun c => wordRightTranslateCLM (A := A) [c]) letter T
    hT.quasiMeasurePreserving (fun x => q₁ x) (fun _ => q) hq
  filter_upwards [hc, havg] with x hcx havgx
  obtain ⟨h, hh⟩ := hcx
  refine ⟨h, hh.congr' (Filter.Eventually.of_forall fun N => ?_)⟩
  rw [havgx N]
  apply BoundedContinuousFunction.ext
  intro z
  exact (birkhoffAverage_stationaryWordSkew_const_apply letter T q N x z).trans
    (stationaryWordCesaro_apply letter T q N x z).symm

end WordTerminal

end IndependentZeroBlocks
