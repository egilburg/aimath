import SierpinskiFormal.StationarySkew
import SierpinskiFormal.StationaryCompactness
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# The finite-letter skew contraction on Bochner `L¹`

For a measurable letter map and a measure-preserving transformation, this
file constructs the skew operator

`(Ug)(x) = R_(letter x) (g(T x))`

as a continuous linear contraction on Bochner `L¹`.  The finite alphabet is
used to prove strong measurability of the operator-valued multiplier.
-/

noncomputable section

open Filter Finset Function Set MeasureTheory
open scoped ENNReal Topology BigOperators

namespace IndependentZeroBlocks

section Construction

variable {Ω A E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Fintype A] [DecidableEq A] [MeasurableSpace A] [MeasurableSingletonClass A]
  {μ : Measure Ω}

/-- A representative of the stationary skew action on Bochner `L¹`. -/
def stationarySkewL1Representative (R : A → E →L[ℝ] E)
    (letter : Ω → A) (T : Ω → Ω) (g : Lp E 1 μ) (x : Ω) : E :=
  R (letter x) (g (T x))

theorem stationarySkewL1Representative_aestronglyMeasurable
    (R : A → E →L[ℝ] E) (letter : Ω → A) (hletter : Measurable letter)
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (g : Lp E 1 μ) :
    AEStronglyMeasurable (stationarySkewL1Representative R letter T g) μ := by
  have hgT : AEStronglyMeasurable (fun x => g (T x)) μ :=
    ((Lp.memLp g).comp_measurePreserving hT).aestronglyMeasurable
  have hs : ∀ s : Finset A, AEStronglyMeasurable
      (fun x => ∑ a ∈ s, (letter ⁻¹' {a}).indicator
        (fun x => R a (g (T x))) x) μ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (aestronglyMeasurable_const :
        AEStronglyMeasurable (fun _ : Ω => (0 : E)) μ)
    | @insert a s ha ih =>
        have ha_meas := ((R a).continuous.comp_aestronglyMeasurable hgT).indicator
          (hletter (measurableSet_singleton a))
        simpa only [Finset.sum_insert ha] using ha_meas.fun_add ih
  have hsum : AEStronglyMeasurable
      (fun x => ∑ a : A, (letter ⁻¹' {a}).indicator
        (fun x => R a (g (T x))) x) μ := by
    simpa using hs Finset.univ
  apply hsum.congr
  filter_upwards [] with x
  rw [Finset.sum_eq_single (letter x)]
  · simp [stationarySkewL1Representative]
  · intro a _ ha
    simp [Set.indicator_apply, ha.symm]
  · simp

theorem stationarySkewL1Representative_memLp
    (R : A → E →L[ℝ] E) (hR : ∀ a, ‖R a‖ ≤ 1)
    (letter : Ω → A) (hletter : Measurable letter)
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (g : Lp E 1 μ) :
    MemLp (stationarySkewL1Representative R letter T g) 1 μ := by
  apply ((Lp.memLp g).comp_measurePreserving hT).of_le
    (stationarySkewL1Representative_aestronglyMeasurable
      R letter hletter T hT g)
  exact Filter.Eventually.of_forall fun x =>
    norm_stationarySkewApply_le R hR letter T g x

/-- The stationary skew action as an element of Bochner `L¹`. -/
def stationarySkewL1 (R : A → E →L[ℝ] E) (hR : ∀ a, ‖R a‖ ≤ 1)
    (letter : Ω → A) (hletter : Measurable letter)
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (g : Lp E 1 μ) :
    Lp E 1 μ :=
  (stationarySkewL1Representative_memLp R hR letter hletter T hT g).toLp
    (stationarySkewL1Representative R letter T g)

theorem stationarySkewL1_coeFn
    (R : A → E →L[ℝ] E) (hR : ∀ a, ‖R a‖ ≤ 1)
    (letter : Ω → A) (hletter : Measurable letter)
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (g : Lp E 1 μ) :
    stationarySkewL1 R hR letter hletter T hT g =ᵐ[μ]
      stationarySkewL1Representative R letter T g :=
  MemLp.coeFn_toLp _

theorem stationarySkewL1_add
    (R : A → E →L[ℝ] E) (hR : ∀ a, ‖R a‖ ≤ 1)
    (letter : Ω → A) (hletter : Measurable letter)
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (g h : Lp E 1 μ) :
    stationarySkewL1 R hR letter hletter T hT (g + h) =
      stationarySkewL1 R hR letter hletter T hT g +
        stationarySkewL1 R hR letter hletter T hT h := by
  apply Lp.ext
  filter_upwards [stationarySkewL1_coeFn R hR letter hletter T hT (g + h),
    stationarySkewL1_coeFn R hR letter hletter T hT g,
    stationarySkewL1_coeFn R hR letter hletter T hT h,
    hT.quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_add g h),
    Lp.coeFn_add (stationarySkewL1 R hR letter hletter T hT g)
      (stationarySkewL1 R hR letter hletter T hT h)] with x hx hgx hhx hghx hout
  rw [hx, hout]
  change stationarySkewL1Representative R letter T (g + h) x =
    stationarySkewL1 R hR letter hletter T hT g x +
      stationarySkewL1 R hR letter hletter T hT h x
  rw [hgx, hhx]
  simp only [stationarySkewL1Representative]
  have hghx' : (g + h) (T x) = g (T x) + h (T x) := by
    simpa [Function.comp_def, Pi.add_apply] using hghx
  rw [hghx', map_add]

theorem stationarySkewL1_smul
    (R : A → E →L[ℝ] E) (hR : ∀ a, ‖R a‖ ≤ 1)
    (letter : Ω → A) (hletter : Measurable letter)
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (c : ℝ) (g : Lp E 1 μ) :
    stationarySkewL1 R hR letter hletter T hT (c • g) =
      c • stationarySkewL1 R hR letter hletter T hT g := by
  apply Lp.ext
  filter_upwards [stationarySkewL1_coeFn R hR letter hletter T hT (c • g),
    stationarySkewL1_coeFn R hR letter hletter T hT g,
    hT.quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_smul c g),
    Lp.coeFn_smul c (stationarySkewL1 R hR letter hletter T hT g)] with x hx hgx hcg hout
  rw [hx, hout]
  change stationarySkewL1Representative R letter T (c • g) x =
    c • stationarySkewL1 R hR letter hletter T hT g x
  rw [hgx]
  simp only [stationarySkewL1Representative]
  have hcg' : (c • g) (T x) = c • g (T x) := by
    simpa [Function.comp_def, Pi.smul_apply] using hcg
  rw [hcg', map_smul]

theorem norm_stationarySkewL1_le
    (R : A → E →L[ℝ] E) (hR : ∀ a, ‖R a‖ ≤ 1)
    (letter : Ω → A) (hletter : Measurable letter)
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (g : Lp E 1 μ) :
    ‖stationarySkewL1 R hR letter hletter T hT g‖ ≤ ‖g‖ := by
  let gT := Lp.compMeasurePreserving T hT g
  have hpoint : ∀ᵐ x ∂μ,
      ‖stationarySkewL1 R hR letter hletter T hT g x‖ ≤ ‖gT x‖ := by
    filter_upwards [stationarySkewL1_coeFn R hR letter hletter T hT g,
      Lp.coeFn_compMeasurePreserving g hT] with x hx hgTx
    rw [hx, hgTx]
    exact norm_stationarySkewApply_le R hR letter T g x
  exact (Lp.norm_le_norm_of_ae_le hpoint).trans_eq
    (Lp.norm_compMeasurePreserving g hT)

/-- The finite-letter stationary skew action is a continuous linear
contraction on Bochner `L¹`. -/
def stationarySkewL1CLM
    (R : A → E →L[ℝ] E) (hR : ∀ a, ‖R a‖ ≤ 1)
    (letter : Ω → A) (hletter : Measurable letter)
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) :
    Lp E 1 μ →L[ℝ] Lp E 1 μ :=
  ({
    toFun := stationarySkewL1 R hR letter hletter T hT
    map_add' := stationarySkewL1_add R hR letter hletter T hT
    map_smul' := stationarySkewL1_smul R hR letter hletter T hT
  } : Lp E 1 μ →ₗ[ℝ] Lp E 1 μ).mkContinuous 1
    (fun g => by
      change ‖stationarySkewL1 R hR letter hletter T hT g‖ ≤ 1 * ‖g‖
      simpa only [one_mul] using
        (norm_stationarySkewL1_le R hR letter hletter T hT g))

@[simp] theorem stationarySkewL1CLM_apply
    (R : A → E →L[ℝ] E) (hR : ∀ a, ‖R a‖ ≤ 1)
    (letter : Ω → A) (hletter : Measurable letter)
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) (g : Lp E 1 μ) :
    stationarySkewL1CLM R hR letter hletter T hT g =
      stationarySkewL1 R hR letter hletter T hT g := rfl

theorem stationarySkewL1CLM_norm_le
    (R : A → E →L[ℝ] E) (hR : ∀ a, ‖R a‖ ≤ 1)
    (letter : Ω → A) (hletter : Measurable letter)
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) :
    ‖stationarySkewL1CLM R hR letter hletter T hT‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro g
  simpa using norm_stationarySkewL1_le R hR letter hletter T hT g

theorem stationarySkewL1CLM_lipschitz
    (R : A → E →L[ℝ] E) (hR : ∀ a, ‖R a‖ ≤ 1)
    (letter : Ω → A) (hletter : Measurable letter)
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) :
    LipschitzWith 1 (stationarySkewL1CLM R hR letter hletter T hT) := by
  apply LipschitzWith.mk_one
  intro g h
  simpa only [dist_eq_norm, map_sub, one_mul] using
    (stationarySkewL1CLM R hR letter hletter T hT).le_of_opNorm_le
      (stationarySkewL1CLM_norm_le R hR letter hletter T hT) (g - h)

/-- Representatives of the `L¹` iterates agree almost everywhere with
iterates of the pointwise skew action. -/
theorem iterate_stationarySkewL1CLM_coeFn
    (R : A → E →L[ℝ] E) (hR : ∀ a, ‖R a‖ ≤ 1)
    (letter : Ω → A) (hletter : Measurable letter)
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (g : Lp E 1 μ) (n : ℕ) :
    (stationarySkewL1CLM R hR letter hletter T hT)^[n] g =ᵐ[μ]
      (stationarySkewApply R letter T)^[n] (fun x => g x) := by
  induction n with
  | zero => exact Filter.Eventually.of_forall fun _ => rfl
  | succ n ih =>
      have ihT : (fun x =>
          ((stationarySkewL1CLM R hR letter hletter T hT)^[n] g) (T x)) =ᵐ[μ]
          (fun x => (((stationarySkewApply R letter T)^[n]
            (fun x => g x)) (T x))) :=
        hT.quasiMeasurePreserving.ae_eq_comp ih
      filter_upwards [stationarySkewL1_coeFn R hR letter hletter T hT
        ((stationarySkewL1CLM R hR letter hletter T hT)^[n] g), ihT] with x hx hix
      simp only [Function.iterate_succ_apply', stationarySkewL1CLM_apply] at hx ⊢
      rw [hx]
      exact congrArg (R (letter x)) hix

/-- Coercion of a finite sum in `Lp` agrees almost everywhere with the
pointwise finite sum. -/
theorem coeFn_finset_sum_Lp {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → Lp E 1 μ) :
    ⇑(∑ i ∈ s, f i : Lp E 1 μ) =ᵐ[μ] fun x => ∑ i ∈ s, f i x := by
  induction s using Finset.induction_on with
  | empty =>
      filter_upwards [Lp.coeFn_zero E (1 : ℝ≥0∞) μ] with x hx
      simpa using hx
  | @insert a s ha ih =>
      filter_upwards [Lp.coeFn_add (f a) (∑ i ∈ s, f i), ih] with x hadd hsum
      simp only [Finset.sum_insert ha]
      rw [hadd]
      change f a x + (∑ i ∈ s, f i) x = f a x + ∑ i ∈ s, f i x
      rw [hsum]

end Construction

section Words

variable {Ω A : Type*} [MeasurableSpace Ω]
  [TopologicalSpace A] [DiscreteTopology A]
  [Fintype A] [DecidableEq A] [MeasurableSpace A] [MeasurableSingletonClass A]
  {μ : Measure Ω}

/-- The right-translation skew contraction on word functions in Bochner
`L¹`. -/
def stationaryWordSkewL1CLM
    (letter : Ω → A) (hletter : Measurable letter)
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) :
    Lp (BoundedWordFunction A) 1 μ →L[ℝ]
      Lp (BoundedWordFunction A) 1 μ :=
  stationarySkewL1CLM
    (fun a => wordRightTranslateCLM (A := A) [a])
    (fun a => wordRightTranslateCLM_norm_le (A := A) [a])
    letter hletter T hT

theorem stationaryWordSkewL1CLM_coeFn
    (letter : Ω → A) (hletter : Measurable letter)
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (g : Lp (BoundedWordFunction A) 1 μ) :
    stationaryWordSkewL1CLM letter hletter T hT g =ᵐ[μ]
      fun x => wordRightTranslate [letter x] (g (T x)) := by
  change ⇑(stationarySkewL1
    (fun a => wordRightTranslateCLM (A := A) [a])
    (fun a => wordRightTranslateCLM_norm_le (A := A) [a])
    letter hletter T hT g) =ᵐ[μ] _
  exact stationarySkewL1_coeFn
      (fun a => wordRightTranslateCLM (A := A) [a])
      (fun a => wordRightTranslateCLM_norm_le (A := A) [a])
      letter hletter T hT g

/-- Almost-everywhere version of the chronological prefix identity for the
actual Bochner `L¹` skew contraction. -/
theorem iterate_stationaryWordSkewL1CLM_const_coeFn
    [IsFiniteMeasure μ]
    (letter : Ω → A) (hletter : Measurable letter)
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (q : BoundedWordFunction A) (n : ℕ) :
    (stationaryWordSkewL1CLM letter hletter T hT)^[n]
        (Lp.const 1 μ q) =ᵐ[μ]
      fun x => wordRightTranslate (stationaryPrefix letter T n x) q := by
  induction n with
  | zero =>
      filter_upwards [(Lp.coeFn_const (α := Ω) (p := (1 : ℝ≥0∞)) μ q)] with x hx
      simp only [Function.iterate_zero_apply]
      change (Lp.const 1 μ q) x = wordRightTranslate [] q
      rw [hx]
      ext z
      simp [wordRightTranslate_apply]
  | succ n ih =>
      have ihT : (fun x =>
          (((stationaryWordSkewL1CLM letter hletter T hT)^[n]
            (Lp.const 1 μ q)) (T x))) =ᵐ[μ]
          (fun x => wordRightTranslate
            (stationaryPrefix letter T n (T x)) q) :=
        hT.quasiMeasurePreserving.ae_eq_comp ih
      filter_upwards [stationaryWordSkewL1CLM_coeFn letter hletter T hT
        ((stationaryWordSkewL1CLM letter hletter T hT)^[n]
          (Lp.const 1 μ q)), ihT] with x hx hix
      simp only [Function.iterate_succ_apply'] at hx ⊢
      rw [hx, hix, stationaryPrefix_succ]
      exact wordRightTranslate_append [letter x]
        (stationaryPrefix letter T n (T x)) q

/-- The Bochner `L¹` Birkhoff average has the expected pointwise prefix
Cesaro representative. -/
theorem birkhoffAverage_stationaryWordSkewL1CLM_const_coeFn
    [IsFiniteMeasure μ]
    (letter : Ω → A) (hletter : Measurable letter)
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (q : BoundedWordFunction A) (N : ℕ) :
    (birkhoffAverage ℝ (stationaryWordSkewL1CLM letter hletter T hT)
        (id : Lp (BoundedWordFunction A) 1 μ →
          Lp (BoundedWordFunction A) 1 μ) N (Lp.const 1 μ q) :
      Lp (BoundedWordFunction A) 1 μ) =ᵐ[μ]
      stationaryWordCesaro letter T q N := by
  let U := stationaryWordSkewL1CLM letter hletter T hT
  let q₁ : Lp (BoundedWordFunction A) 1 μ := Lp.const 1 μ q
  have hall : ∀ s : Finset ℕ, ∀ᵐ x ∂μ, ∀ n ∈ s,
      (U^[n] q₁) x = wordRightTranslate (stationaryPrefix letter T n x) q := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert n s hn ih =>
        filter_upwards [iterate_stationaryWordSkewL1CLM_const_coeFn
          letter hletter T hT q n, ih] with x hnx hsx
        intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact hnx
        · exact hsx k hk
  rw [birkhoffAverage, birkhoffSum]
  simp only [id_eq]
  change ((N : ℝ)⁻¹ • ∑ n ∈ Finset.range N, U^[n] q₁) =ᵐ[μ]
    stationaryWordCesaro letter T q N
  filter_upwards [Lp.coeFn_smul (N : ℝ)⁻¹
      (∑ n ∈ Finset.range N, U^[n] q₁),
    coeFn_finset_sum_Lp (E := BoundedWordFunction A) (μ := μ)
      (Finset.range N) (fun n => U^[n] q₁),
    hall (Finset.range N)] with x hsmul hsum hiter
  rw [hsmul]
  change (N : ℝ)⁻¹ • (∑ n ∈ Finset.range N, U^[n] q₁) x =
    stationaryWordCesaro letter T q N x
  rw [hsum]
  simp only [id_eq, Pi.smul_apply, stationaryWordCesaro]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  exact hiter n hn

theorem stationaryWordCesaro_aestronglyMeasurable
    [IsFiniteMeasure μ]
    (letter : Ω → A) (hletter : Measurable letter)
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (q : BoundedWordFunction A) (N : ℕ) :
    AEStronglyMeasurable (stationaryWordCesaro letter T q N) μ := by
  let avg : Lp (BoundedWordFunction A) 1 μ :=
    birkhoffAverage ℝ (stationaryWordSkewL1CLM letter hletter T hT)
      (id : Lp (BoundedWordFunction A) 1 μ →
        Lp (BoundedWordFunction A) 1 μ) N (Lp.const 1 μ q)
  have havg : AEStronglyMeasurable (fun x => avg x) μ :=
    Lp.aestronglyMeasurable avg
  apply havg.congr
  simpa only [avg] using
    (birkhoffAverage_stationaryWordSkewL1CLM_const_coeFn
      letter hletter T hT q N)

theorem norm_stationaryWordCesaro_le
    (letter : Ω → A) (T : Ω → Ω) (q : BoundedWordFunction A)
    (N : ℕ) (x : Ω) :
    ‖stationaryWordCesaro letter T q N x‖ ≤ ‖q‖ := by
  by_cases hN : N = 0
  · simp [hN, stationaryWordCesaro]
  · let C : Set (BoundedWordFunction A) := Metric.closedBall 0 ‖q‖
    have hmem : stationaryWordCesaro letter T q N x ∈ C := by
      apply stationaryWordCesaro_mem letter T q C (convex_closedBall 0 ‖q‖)
      · simp [C]
      · intro a f hf
        change dist (wordRightTranslate [a] f) 0 ≤ ‖q‖
        rw [dist_zero_right]
        exact ((wordRightTranslateCLM (A := A) [a]).le_of_opNorm_le
          (wordRightTranslateCLM_norm_le (A := A) [a]) f).trans (by
            simpa [C, Metric.mem_closedBall, dist_zero_right] using hf)
      · exact hN
    simpa [C, Metric.mem_closedBall, dist_zero_right] using hmem

/-- The stationary prefix Cesaro representatives are uniformly integrable.
This verifies the uniform-integrability hypothesis in the specialized
Diestel compactness step. -/
theorem uniformIntegrable_one_stationaryWordCesaro
    [IsFiniteMeasure μ]
    (letter : Ω → A) (hletter : Measurable letter)
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (q : BoundedWordFunction A) :
    UniformIntegrable (stationaryWordCesaro letter T q) 1 μ := by
  apply uniformIntegrable_one_of_ae_norm_le
    (fun N => stationaryWordCesaro_aestronglyMeasurable
      letter hletter T hT q N) ‖q‖
  intro N
  exact Filter.Eventually.of_forall fun x =>
    norm_stationaryWordCesaro_le letter T q N x

end Words

end IndependentZeroBlocks
