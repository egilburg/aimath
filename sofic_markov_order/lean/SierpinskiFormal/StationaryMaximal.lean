import SierpinskiFormal.StationarySkew
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# A finite Hopf maximal lemma

This file proves the scalar finite maximal-ergodic estimate needed for the
pathwise stationary argument.  It applies to an arbitrary measure-preserving
self-map; neither invertibility nor reversibility is assumed.
-/

noncomputable section

open Function Set Filter Topology MeasureTheory

namespace IndependentZeroBlocks

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Deterministic closure lemma used by the Banach-principle argument.  A
sequence is Cauchy if it admits convergent approximants which are uniformly
close at all times, with errors tending to zero. -/
theorem cauchySeq_of_eventually_uniform_approx
    {Y : Type*} [PseudoMetricSpace Y]
    (a : ℕ → Y) (b : ℕ → ℕ → Y) (δ : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0)) (hb : ∀ k, CauchySeq (b k))
    (hclose : ∀ᶠ k in atTop, ∀ N, dist (a N) (b k N) ≤ δ k) :
    CauchySeq a := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hthird : 0 < ε / 3 := by positivity
  have hsmall : ∀ᶠ k in atTop, δ k < ε / 3 :=
    (tendsto_order.1 hδ).2 _ hthird
  obtain ⟨k, hkclose, hksmall⟩ := (hclose.and hsmall).exists
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 (hb k) (ε / 3) hthird
  refine ⟨N, fun m hm n hn => ?_⟩
  calc
    dist (a m) (a n) ≤
        dist (a m) (b k m) + dist (b k m) (b k n) +
          dist (b k n) (a n) := by
      calc
        dist (a m) (a n) ≤ dist (a m) (b k m) + dist (b k m) (a n) :=
          dist_triangle _ _ _
        _ ≤ dist (a m) (b k m) +
            (dist (b k m) (b k n) + dist (b k n) (a n)) :=
          add_le_add le_rfl (dist_triangle _ _ _)
        _ = _ := by ring
    _ ≤ δ k + dist (b k m) (b k n) + δ k := by
      exact add_le_add
        (add_le_add (hkclose m) le_rfl)
        (by simpa [dist_comm] using hkclose n)
    _ < ε := by
      have hmiddle := hN m hm n hn
      linarith

/-- The positive maximum of the first `n` Birkhoff partial sums, in its
recursive form. -/
def hopfPartialMax (T : Ω → Ω) (f : Ω → ℝ) : ℕ → Ω → ℝ
  | 0, _ => 0
  | n + 1, x => max 0 (f x + hopfPartialMax T f n (T x))

@[simp] theorem hopfPartialMax_zero (T : Ω → Ω) (f : Ω → ℝ) (x : Ω) :
    hopfPartialMax T f 0 x = 0 := rfl

@[simp] theorem hopfPartialMax_succ (T : Ω → Ω) (f : Ω → ℝ)
    (n : ℕ) (x : Ω) :
    hopfPartialMax T f (n + 1) x =
      max 0 (f x + hopfPartialMax T f n (T x)) := rfl

theorem hopfPartialMax_nonneg (T : Ω → Ω) (f : Ω → ℝ)
    (n : ℕ) (x : Ω) :
    0 ≤ hopfPartialMax T f n x := by
  cases n <;> simp [hopfPartialMax]

theorem hopfPartialMax_le_succ (T : Ω → Ω) (f : Ω → ℝ)
    (n : ℕ) (x : Ω) :
    hopfPartialMax T f n x ≤ hopfPartialMax T f (n + 1) x := by
  induction n generalizing x with
  | zero => exact hopfPartialMax_nonneg T f 1 x
  | succ n ih =>
      simp only [hopfPartialMax_succ]
      exact max_le_max_left 0 (add_le_add le_rfl (ih (T x)))

theorem monotone_hopfPartialMax (T : Ω → Ω) (f : Ω → ℝ) (x : Ω) :
    Monotone (fun n => hopfPartialMax T f n x) :=
  monotone_nat_of_le_succ (fun n => hopfPartialMax_le_succ T f n x)

theorem birkhoffSum_le_hopfPartialMax (T : Ω → Ω) (f : Ω → ℝ)
    (n : ℕ) (x : Ω) :
    birkhoffSum T f n x ≤ hopfPartialMax T f n x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [birkhoffSum_succ']
      exact (add_le_add le_rfl (ih (T x))).trans
        (le_max_right 0 (f x + hopfPartialMax T f n (T x)))

theorem birkhoffSum_sub_const (T : Ω → Ω) (r : Ω → ℝ)
    (ε : ℝ) (n : ℕ) (x : Ω) :
    birkhoffSum T (fun y => r y - ε) n x =
      birkhoffSum T r n x - (n : ℝ) * ε := by
  simp [birkhoffSum, Finset.sum_sub_distrib]

/-- Points where one of the first `m` positive-time Birkhoff averages is
larger than `ε`. -/
def finiteBirkhoffMaxSet (T : Ω → Ω) (r : Ω → ℝ)
    (ε : ℝ) (m : ℕ) : Set Ω :=
  {x | ∃ N, N ≤ m ∧ N ≠ 0 ∧ ε < birkhoffAverage ℝ T r N x}

theorem measurable_birkhoffSum (T : Ω → Ω) (hT : Measurable T)
    (r : Ω → ℝ) (hr : Measurable r) (n : ℕ) :
    Measurable (birkhoffSum T r n) := by
  exact Finset.measurable_sum (Finset.range n) fun i _ =>
    hr.comp (hT.iterate i)

theorem measurable_birkhoffAverage (T : Ω → Ω) (hT : Measurable T)
    (r : Ω → ℝ) (hr : Measurable r) (n : ℕ) :
    Measurable (birkhoffAverage ℝ T r n) := by
  exact (measurable_birkhoffSum T hT r hr n).const_smul (n : ℝ)⁻¹

theorem measurableSet_finiteBirkhoffMaxSet
    (T : Ω → Ω) (hT : Measurable T)
    (r : Ω → ℝ) (hr : Measurable r) (ε : ℝ) (m : ℕ) :
    MeasurableSet (finiteBirkhoffMaxSet T r ε m) := by
  rw [show finiteBirkhoffMaxSet T r ε m =
      ⋃ N : ℕ, if N ≤ m ∧ N ≠ 0
        then {x | ε < birkhoffAverage ℝ T r N x} else ∅ by
    ext x
    simp [finiteBirkhoffMaxSet, and_assoc]]
  apply MeasurableSet.iUnion
  intro N
  by_cases hN : N ≤ m ∧ N ≠ 0
  · simp only [if_pos hN]
    exact measurableSet_lt measurable_const
      (measurable_birkhoffAverage T hT r hr N)
  · simp [hN]

theorem monotone_finiteBirkhoffMaxSet (T : Ω → Ω) (r : Ω → ℝ)
    (ε : ℝ) : Monotone (finiteBirkhoffMaxSet T r ε) := by
  intro m k hmk x hx
  obtain ⟨N, hNm, hN, havg⟩ := hx
  exact ⟨N, hNm.trans hmk, hN, havg⟩

/-- Points where some positive-time Birkhoff average is larger than `ε`. -/
def birkhoffMaxSet (T : Ω → Ω) (r : Ω → ℝ) (ε : ℝ) : Set Ω :=
  {x | ∃ N, N ≠ 0 ∧ ε < birkhoffAverage ℝ T r N x}

theorem iUnion_finiteBirkhoffMaxSet (T : Ω → Ω) (r : Ω → ℝ) (ε : ℝ) :
    ⋃ m, finiteBirkhoffMaxSet T r ε m = birkhoffMaxSet T r ε := by
  ext x
  simp only [Set.mem_iUnion, finiteBirkhoffMaxSet, Set.mem_setOf_eq,
    birkhoffMaxSet]
  constructor
  · rintro ⟨_, N, _, hN, havg⟩
    exact ⟨N, hN, havg⟩
  · rintro ⟨N, hN, havg⟩
    exact ⟨N, N, le_rfl, hN, havg⟩

theorem finiteBirkhoffMaxSet_subset_hopfPartialMax_sub_const
    (T : Ω → Ω) (r : Ω → ℝ) (ε : ℝ) (m : ℕ) :
    finiteBirkhoffMaxSet T r ε m ⊆
      {x | 0 < hopfPartialMax T (fun y => r y - ε) m x} := by
  intro x hx
  obtain ⟨N, hNm, hN, havg⟩ := hx
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hmul := mul_lt_mul_of_pos_left havg hNpos
  have hsum : (N : ℝ) * ε < birkhoffSum T r N x := by
    simpa [birkhoffAverage, smul_eq_mul, mul_assoc, hN] using hmul
  have hpositive : 0 < birkhoffSum T (fun y => r y - ε) N x := by
    rw [birkhoffSum_sub_const]
    linarith
  exact hpositive.trans_le <|
    (birkhoffSum_le_hopfPartialMax T (fun y => r y - ε) N x).trans
      (monotone_hopfPartialMax T (fun y => r y - ε) x hNm)

theorem measurable_hopfPartialMax (T : Ω → Ω) (hT : Measurable T)
    (f : Ω → ℝ) (hf : Measurable f) (n : ℕ) :
    Measurable (hopfPartialMax T f n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      exact measurable_const.max (hf.add (ih.comp hT))

theorem integrable_comp_measurePreserving (T : Ω → Ω)
    (hT : MeasurePreserving T μ μ) {f : Ω → ℝ} (hf : Integrable f μ) :
    Integrable (f ∘ T) μ := by
  have hfm : Integrable f (Measure.map T μ) := by
    simpa only [hT.map_eq] using hf
  exact hfm.comp_measurable hT.measurable

theorem integral_comp_measurePreserving (T : Ω → Ω)
    (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : Integrable f μ) :
    (∫ x, f (T x) ∂μ) = ∫ x, f x ∂μ := by
  calc
    (∫ x, f (T x) ∂μ) = ∫ x, f x ∂Measure.map T μ :=
      (integral_map hT.measurable.aemeasurable
        (by simpa only [hT.map_eq] using hf.aestronglyMeasurable)).symm
    _ = ∫ x, f x ∂μ := by rw [hT.map_eq]

theorem integrable_hopfPartialMax (T : Ω → Ω)
    (hT : MeasurePreserving T μ μ) (f : Ω → ℝ) (hf : Integrable f μ)
    (n : ℕ) : Integrable (hopfPartialMax T f n) μ := by
  induction n with
  | zero => exact integrable_zero Ω ℝ μ
  | succ n ih =>
      exact Integrable.sup (integrable_zero Ω ℝ μ)
        (hf.add (integrable_comp_measurePreserving T hT ih))

/-- Finite Hopf maximal lemma: the integral of `f` over the set where one of
the first `n` partial sums is positive is nonnegative. -/
theorem integral_indicator_hopfPartialMax_pos_nonneg
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (f : Ω → ℝ) (hfmeas : Measurable f) (hf : Integrable f μ)
    (n : ℕ) :
    0 ≤ ∫ x, {x | 0 < hopfPartialMax T f n x}.indicator f x ∂μ := by
  cases n with
  | zero => simp
  | succ n =>
      let M : Ω → ℝ := hopfPartialMax T f (n + 1)
      let P : Ω → ℝ := fun x => hopfPartialMax T f n (T x)
      let E : Set Ω := {x | 0 < M x}
      have hM_meas : Measurable M :=
        measurable_hopfPartialMax T hT.measurable f hfmeas (n + 1)
      have hP_meas : Measurable P :=
        (measurable_hopfPartialMax T hT.measurable f hfmeas n).comp hT.measurable
      have hE : MeasurableSet E := hM_meas measurableSet_Ioi
      have hM_int : Integrable M μ := integrable_hopfPartialMax T hT f hf (n + 1)
      have hP_int : Integrable P μ := by
        exact integrable_comp_measurePreserving T hT
          (integrable_hopfPartialMax T hT f hf n)
      have hid : E.indicator f = M - E.indicator P := by
        funext x
        by_cases hx : x ∈ E
        · have hpos : 0 < f x + P x := by
            simpa only [E, M, P, Set.mem_setOf_eq, hopfPartialMax_succ, lt_max_iff,
              lt_self_iff_false, false_or] using hx
          simp [Set.indicator_of_mem hx, M, P, hopfPartialMax_succ,
            max_eq_right hpos.le]
        · have hzero : M x = 0 := by
            have hnpos : ¬ 0 < M x := by simpa only [E, Set.mem_setOf_eq] using hx
            exact le_antisymm (le_of_not_gt hnpos) (hopfPartialMax_nonneg T f _ x)
          simp [Set.indicator_of_notMem hx, hzero]
      have hindicator_le : E.indicator P ≤ P := by
        intro x
        by_cases hx : x ∈ E
        · simp [Set.indicator_of_mem hx]
        · simpa [Set.indicator_of_notMem hx, P] using
            hopfPartialMax_nonneg T f n (T x)
      have hP_integral : (∫ x, E.indicator P x ∂μ) ≤ ∫ x, P x ∂μ :=
        integral_mono (hP_int.indicator hE) hP_int hindicator_le
      have hPinv : (∫ x, P x ∂μ) = ∫ x, hopfPartialMax T f n x ∂μ :=
        integral_comp_measurePreserving T hT
          (integrable_hopfPartialMax T hT f hf n)
      have hmono : (∫ x, hopfPartialMax T f n x ∂μ) ≤ ∫ x, M x ∂μ :=
        integral_mono
          (integrable_hopfPartialMax T hT f hf n) hM_int
          (fun x => hopfPartialMax_le_succ T f n x)
      rw [hid]
      change 0 ≤ ∫ x, M x - E.indicator P x ∂μ
      rw [integral_sub hM_int (hP_int.indicator hE)]
      linarith

/-- Quantitative finite Hopf estimate, expressed using the recursive maximum.
For nonnegative `r`, the measure of the set where a partial sum of
`r - ε` is positive is controlled by the `L¹` mass of `r`. -/
theorem mul_measureReal_hopfPartialMax_sub_const_le_integral
    [IsFiniteMeasure μ]
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (r : Ω → ℝ) (hrmeas : Measurable r) (hr : Integrable r μ)
    (hr_nonneg : ∀ x, 0 ≤ r x) (ε : ℝ) (n : ℕ) :
    ε * μ.real {x | 0 < hopfPartialMax T (fun y => r y - ε) n x} ≤
      ∫ x, r x ∂μ := by
  let f : Ω → ℝ := fun x => r x - ε
  let E : Set Ω := {x | 0 < hopfPartialMax T f n x}
  have hfmeas : Measurable f := hrmeas.sub measurable_const
  have hf : Integrable f μ := hr.sub (integrable_const ε)
  have hE : MeasurableSet E :=
    (measurable_hopfPartialMax T hT.measurable f hfmeas n) measurableSet_Ioi
  have hhopf : 0 ≤ ∫ x, E.indicator f x ∂μ :=
    integral_indicator_hopfPartialMax_pos_nonneg T hT f hfmeas hf n
  have hid : E.indicator f = E.indicator r - E.indicator (fun _ => ε) := by
    funext x
    by_cases hx : x ∈ E <;> simp [f, hx]
  have hrE_int : Integrable (E.indicator r) μ := hr.indicator hE
  have hεE_int : Integrable (E.indicator (fun _ => ε)) μ :=
    (integrable_const ε).indicator hE
  have hrE_le : (∫ x, E.indicator r x ∂μ) ≤ ∫ x, r x ∂μ := by
    apply integral_mono hrE_int hr
    intro x
    by_cases hx : x ∈ E
    · simp [Set.indicator_of_mem hx]
    · simpa [Set.indicator_of_notMem hx] using hr_nonneg x
  rw [hid] at hhopf
  change 0 ≤ ∫ x, E.indicator r x - E.indicator (fun _ => ε) x ∂μ at hhopf
  rw [integral_sub hrE_int hεE_int,
    integral_indicator_const ε hE] at hhopf
  change 0 ≤ (∫ x, E.indicator r x ∂μ) - μ.real E * ε at hhopf
  change ε * μ.real E ≤ ∫ x, r x ∂μ
  nlinarith

/-- Finite scalar maximal ergodic inequality for a measure-preserving map.
The bound is stated with `Measure.real`, which is convenient on finite
measure spaces and avoids extended-real coercions. -/
theorem mul_measureReal_finiteBirkhoffMaxSet_le_integral
    [IsFiniteMeasure μ]
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (r : Ω → ℝ) (hrmeas : Measurable r) (hr : Integrable r μ)
    (hr_nonneg : ∀ x, 0 ≤ r x) (ε : ℝ) (hε : 0 < ε) (m : ℕ) :
    ε * μ.real (finiteBirkhoffMaxSet T r ε m) ≤ ∫ x, r x ∂μ := by
  let E : Set Ω := {x | 0 < hopfPartialMax T (fun y => r y - ε) m x}
  have hsub : finiteBirkhoffMaxSet T r ε m ⊆ E :=
    finiteBirkhoffMaxSet_subset_hopfPartialMax_sub_const T r ε m
  have hmeasure : μ.real (finiteBirkhoffMaxSet T r ε m) ≤ μ.real E := by
    apply ENNReal.toReal_mono (measure_ne_top μ E)
    exact measure_mono hsub
  exact (mul_le_mul_of_nonneg_left hmeasure hε.le).trans
    (mul_measureReal_hopfPartialMax_sub_const_le_integral
      T hT r hrmeas hr hr_nonneg ε m)

/-- Scalar maximal ergodic inequality over all positive averaging times. -/
theorem mul_measureReal_birkhoffMaxSet_le_integral
    [IsFiniteMeasure μ]
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (r : Ω → ℝ) (hrmeas : Measurable r) (hr : Integrable r μ)
    (hr_nonneg : ∀ x, 0 ≤ r x) (ε : ℝ) (hε : 0 < ε) :
    ε * μ.real (birkhoffMaxSet T r ε) ≤ ∫ x, r x ∂μ := by
  let S : ℕ → Set Ω := finiteBirkhoffMaxSet T r ε
  have hmono : Monotone S := monotone_finiteBirkhoffMaxSet T r ε
  have hμ : Tendsto (fun m => μ (S m)) atTop
      (𝓝 (μ (birkhoffMaxSet T r ε))) := by
    simpa only [Function.comp_def, S, iUnion_finiteBirkhoffMaxSet] using
      (tendsto_measure_iUnion_atTop (μ := μ) hmono)
  have hreal : Tendsto (fun m => μ.real (S m)) atTop
      (𝓝 (μ.real (birkhoffMaxSet T r ε))) :=
    (ENNReal.tendsto_toReal (measure_ne_top μ _)).comp hμ
  have hmul : Tendsto (fun m => ε * μ.real (S m)) atTop
      (𝓝 (ε * μ.real (birkhoffMaxSet T r ε))) :=
    tendsto_const_nhds.mul hreal
  apply isClosed_Iic.mem_of_tendsto hmul
  filter_upwards [] with m
  exact mul_measureReal_finiteBirkhoffMaxSet_le_integral
    T hT r hrmeas hr hr_nonneg ε hε m

/-- Extended-real form of the all-times scalar maximal inequality. -/
theorem measure_birkhoffMaxSet_le_ofReal_integral_div
    [IsFiniteMeasure μ]
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (r : Ω → ℝ) (hrmeas : Measurable r) (hr : Integrable r μ)
    (hr_nonneg : ∀ x, 0 ≤ r x) (ε : ℝ) (hε : 0 < ε) :
    μ (birkhoffMaxSet T r ε) ≤ ENNReal.ofReal ((∫ x, r x ∂μ) / ε) := by
  have hreal : μ.real (birkhoffMaxSet T r ε) ≤ (∫ x, r x ∂μ) / ε := by
    have h := mul_measureReal_birkhoffMaxSet_le_integral
      T hT r hrmeas hr hr_nonneg ε hε
    exact (le_div_iff₀ hε).2 (by simpa [mul_comm] using h)
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ (birkhoffMaxSet T r ε))]
  exact ENNReal.ofReal_le_ofReal hreal

/-- Borel--Cantelli consequence of the maximal inequality.  If the normalized
`L¹` errors are summable, then almost every point eventually has the desired
uniform-in-time scalar bound. -/
theorem ae_eventually_forall_birkhoffAverage_le_of_summable_integral_div
    [IsFiniteMeasure μ]
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (r : ℕ → Ω → ℝ) (hrmeas : ∀ k, Measurable (r k))
    (hr : ∀ k, Integrable (r k) μ) (hr_nonneg : ∀ k x, 0 ≤ r k x)
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k)
    (hsum : Summable (fun k => (∫ x, r k x ∂μ) / ε k)) :
    ∀ᵐ x ∂μ, ∀ᶠ k in atTop, ∀ N, N ≠ 0 →
      birkhoffAverage ℝ T (r k) N x ≤ ε k := by
  let q : ℕ → ℝ := fun k => (∫ x, r k x ∂μ) / ε k
  let S : ℕ → Set Ω := fun k => birkhoffMaxSet T (r k) (ε k)
  have hq_nonneg : ∀ k, 0 ≤ q k := by
    intro k
    exact div_nonneg (integral_nonneg (hr_nonneg k)) (hε k).le
  have hmeasure : ∀ k, μ (S k) ≤ ENNReal.ofReal (q k) := by
    intro k
    exact measure_birkhoffMaxSet_le_ofReal_integral_div
      T hT (r k) (hrmeas k) (hr k) (hr_nonneg k) (ε k) (hε k)
  have hq_tsum : (∑' k, ENNReal.ofReal (q k)) ≠ ⊤ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hq_nonneg hsum]
    exact ENNReal.ofReal_ne_top
  have hS_tsum : (∑' k, μ (S k)) ≠ ⊤ :=
    ne_top_of_le_ne_top hq_tsum (ENNReal.tsum_le_tsum hmeasure)
  filter_upwards [ae_eventually_notMem hS_tsum] with x hx
  filter_upwards [hx] with k hk
  intro N hN
  by_contra hle
  exact hk ⟨N, hN, lt_of_not_ge hle⟩

section SkewMaximal

variable {A E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem stationarySkewApply_sub (R : A → E →L[ℝ] E)
    (letter : Ω → A) (T : Ω → Ω) (g h : Ω → E) :
    stationarySkewApply R letter T (g - h) =
      stationarySkewApply R letter T g - stationarySkewApply R letter T h := by
  funext x
  exact map_sub (R (letter x)) _ _

theorem iterate_stationarySkewApply_sub (R : A → E →L[ℝ] E)
    (letter : Ω → A) (T : Ω → Ω) (g h : Ω → E) (n : ℕ) :
    (stationarySkewApply R letter T)^[n] (g - h) =
      (stationarySkewApply R letter T)^[n] g -
        (stationarySkewApply R letter T)^[n] h := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [Function.iterate_succ_apply']
      rw [ih, stationarySkewApply_sub]

theorem birkhoffAverage_stationarySkewApply_sub
    (R : A → E →L[ℝ] E) (letter : Ω → A) (T : Ω → Ω)
    (g h : Ω → E) (N : ℕ) :
    birkhoffAverage ℝ (stationarySkewApply R letter T) id N (g - h) =
      birkhoffAverage ℝ (stationarySkewApply R letter T) id N g -
        birkhoffAverage ℝ (stationarySkewApply R letter T) id N h := by
  simp only [birkhoffAverage, birkhoffSum, id_eq, ← Finset.smul_sum,
    iterate_stationarySkewApply_sub, Finset.sum_sub_distrib, smul_sub]

theorem iterate_stationarySkewApply_add (R : A → E →L[ℝ] E)
    (letter : Ω → A) (T : Ω → Ω) (g h : Ω → E) (n : ℕ) :
    (stationarySkewApply R letter T)^[n] (g + h) =
      (stationarySkewApply R letter T)^[n] g +
        (stationarySkewApply R letter T)^[n] h := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [Function.iterate_succ_apply']
      rw [ih, stationarySkewApply_add]

theorem birkhoffAverage_stationarySkewApply_add
    (R : A → E →L[ℝ] E) (letter : Ω → A) (T : Ω → Ω)
    (g h : Ω → E) (N : ℕ) :
    birkhoffAverage ℝ (stationarySkewApply R letter T) id N (g + h) =
      birkhoffAverage ℝ (stationarySkewApply R letter T) id N g +
        birkhoffAverage ℝ (stationarySkewApply R letter T) id N h := by
  simp only [birkhoffAverage, birkhoffSum, id_eq, ← Finset.smul_sum,
    iterate_stationarySkewApply_add, Finset.sum_add_distrib, smul_add]

/-- A pointwise skew coboundary has the usual telescoping average. -/
theorem birkhoffAverage_stationarySkewApply_coboundary
    (R : A → E →L[ℝ] E) (letter : Ω → A) (T : Ω → Ω)
    (y : Ω → E) (N : ℕ) (x : Ω) :
    birkhoffAverage ℝ (stationarySkewApply R letter T) id N
        (stationarySkewApply R letter T y - y) x =
      (N : ℝ)⁻¹ •
        (((stationarySkewApply R letter T)^[N] y) x - y x) := by
  rw [birkhoffAverage_stationarySkewApply_sub]
  exact congrFun
    (birkhoffAverage_apply_sub_birkhoffAverage (R := ℝ)
      (stationarySkewApply R letter T) id N y) x

/-- An almost-everywhere fixed representative remains fixed under every
iterate on one common conull set. -/
theorem ae_iterate_stationarySkewApply_eq_of_ae_fixed
    (R : A → E →L[ℝ] E) (letter : Ω → A) (T : Ω → Ω)
    (hT : Measure.QuasiMeasurePreserving T μ μ) (p : Ω → E)
    (hp : stationarySkewApply R letter T p =ᵐ[μ] p) :
    ∀ n, (stationarySkewApply R letter T)^[n] p =ᵐ[μ] p := by
  intro n
  induction n with
  | zero => exact Filter.Eventually.of_forall fun _ => rfl
  | succ n ih =>
      have ihT : (fun x => ((stationarySkewApply R letter T)^[n] p) (T x)) =ᵐ[μ]
          fun x => p (T x) := hT.ae_eq_comp ih
      filter_upwards [ihT, hp] with x hix hpx
      simp only [Function.iterate_succ_apply', stationarySkewApply]
      rw [hix]
      exact hpx

/-- Almost-everywhere equality is preserved by every iterate of a skew
operator over a quasi-measure-preserving base. -/
theorem ae_iterate_stationarySkewApply_congr
    (R : A → E →L[ℝ] E) (letter : Ω → A) (T : Ω → Ω)
    (hT : Measure.QuasiMeasurePreserving T μ μ) (g h : Ω → E)
    (hgh : g =ᵐ[μ] h) :
    ∀ n, (stationarySkewApply R letter T)^[n] g =ᵐ[μ]
      (stationarySkewApply R letter T)^[n] h := by
  intro n
  induction n with
  | zero => exact hgh
  | succ n ih =>
      have ihT := hT.ae_eq_comp ih
      filter_upwards [ihT] with x hx
      simp only [Function.iterate_succ_apply', stationarySkewApply]
      exact congrArg (R (letter x)) hx

/-- Almost-everywhere equal inputs have almost-everywhere equal skew Cesàro
averages, simultaneously at all times. -/
theorem ae_all_birkhoffAverage_stationarySkewApply_congr
    (R : A → E →L[ℝ] E) (letter : Ω → A) (T : Ω → Ω)
    (hT : Measure.QuasiMeasurePreserving T μ μ) (g h : Ω → E)
    (hgh : g =ᵐ[μ] h) :
    ∀ᵐ x ∂μ, ∀ N, birkhoffAverage ℝ
      (stationarySkewApply R letter T) id N g x =
        birkhoffAverage ℝ (stationarySkewApply R letter T) id N h x := by
  have hi : ∀ᵐ x ∂μ, ∀ n,
      ((stationarySkewApply R letter T)^[n] g) x =
        ((stationarySkewApply R letter T)^[n] h) x :=
    ae_all_iff.2 (ae_iterate_stationarySkewApply_congr
      R letter T hT g h hgh)
  filter_upwards [hi] with x hx
  intro N
  simp only [birkhoffAverage, birkhoffSum, id_eq, Pi.smul_apply,
    Finset.sum_apply]
  congr 1
  exact Finset.sum_congr rfl fun n _ => hx n

/-- Pointwise dense-core convergence under the local hypotheses naturally
produced after discarding one null set: all iterates of `p` are fixed at the
chosen point, and `y` is bounded along its `T`-orbit. -/
theorem tendsto_birkhoffAverage_fixed_add_bounded_coboundary_of_iterates
    (R : A → E →L[ℝ] E) (hR : ∀ a, ‖R a‖ ≤ 1)
    (letter : Ω → A) (T : Ω → Ω) (p y : Ω → E)
    (C : ℝ) (x : Ω)
    (hp : ∀ n, ((stationarySkewApply R letter T)^[n] p) x = p x)
    (hy : ∀ n, ‖y (T^[n] x)‖ ≤ C) :
    Tendsto (fun N => birkhoffAverage ℝ
      (stationarySkewApply R letter T) id N
        (p + (stationarySkewApply R letter T y - y)) x)
      atTop (𝓝 (p x)) := by
  let U := stationarySkewApply R letter T
  let d : ℕ → E := fun N => (U^[N] y) x - y x
  have hd : ∀ N, ‖d N‖ ≤ 2 * C := by
    intro N
    calc
      ‖d N‖ ≤ ‖(U^[N] y) x‖ + ‖y x‖ := norm_sub_le _ _
      _ ≤ C + C := add_le_add
        ((norm_iterate_stationarySkewApply_le R hR letter T y N x).trans
          (hy N)) (by simpa using hy 0)
      _ = 2 * C := by ring
  have hdbounded : IsBoundedUnder (· ≤ ·) atTop (norm ∘ d) :=
    isBoundedUnder_of ⟨2 * C, fun N => hd N⟩
  have hzero : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ • d N) atTop (𝓝 0) :=
    NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded
      tendsto_inv_atTop_nhds_zero_nat hdbounded
  have htarget : Tendsto (fun N : ℕ => p x + (N : ℝ)⁻¹ • d N)
      atTop (𝓝 (p x)) := by
    simpa using tendsto_const_nhds.add hzero
  apply htarget.congr'
  filter_upwards [eventually_ne_atTop 0] with N hN
  rw [birkhoffAverage_stationarySkewApply_add]
  have hfixedAverage : birkhoffAverage ℝ U id N p x = p x := by
    simp only [birkhoffAverage, birkhoffSum, id_eq, Pi.smul_apply,
      Finset.sum_apply]
    simp only [U]
    simp_rw [hp]
    rw [Finset.sum_const, Finset.card_range,
      ← Nat.cast_smul_eq_nsmul ℝ,
      inv_smul_smul₀ (show (N : ℝ) ≠ 0 from Nat.cast_ne_zero.mpr hN)]
  simp only [Pi.add_apply]
  rw [hfixedAverage]
  change p x + (N : ℝ)⁻¹ • d N =
    p x + birkhoffAverage ℝ U id N (U y - y) x
  rw [birkhoffAverage_stationarySkewApply_coboundary]

/-- Almost-everywhere dense-core convergence.  Both fixedness and boundedness
may hold only almost everywhere; quasi-invariance transports those facts
simultaneously along every forward orbit. -/
theorem ae_tendsto_birkhoffAverage_fixed_add_bounded_coboundary
    (R : A → E →L[ℝ] E) (hR : ∀ a, ‖R a‖ ≤ 1)
    (letter : Ω → A) (T : Ω → Ω)
    (hT : Measure.QuasiMeasurePreserving T μ μ)
    (p y : Ω → E)
    (hp : stationarySkewApply R letter T p =ᵐ[μ] p)
    (C : ℝ) (hy : ∀ᵐ x ∂μ, ‖y x‖ ≤ C) :
    ∀ᵐ x ∂μ, Tendsto (fun N => birkhoffAverage ℝ
      (stationarySkewApply R letter T) id N
        (p + (stationarySkewApply R letter T y - y)) x)
      atTop (𝓝 (p x)) := by
  have hpiter : ∀ᵐ x ∂μ, ∀ n,
      ((stationarySkewApply R letter T)^[n] p) x = p x :=
    ae_all_iff.2 (ae_iterate_stationarySkewApply_eq_of_ae_fixed
      R letter T hT p hp)
  have hyiter : ∀ᵐ x ∂μ, ∀ n, ‖y (T^[n] x)‖ ≤ C :=
    ae_all_iff.2 fun n => (hT.iterate n).ae hy
  filter_upwards [hpiter, hyiter] with x hpx hyx
  exact tendsto_birkhoffAverage_fixed_add_bounded_coboundary_of_iterates
    R hR letter T p y C x hpx hyx

/-- A fixed point plus a bounded skew coboundary has pointwise convergent
averages.  This is the dense core in the stationary Banach principle. -/
theorem tendsto_birkhoffAverage_fixed_add_bounded_coboundary
    (R : A → E →L[ℝ] E) (hR : ∀ a, ‖R a‖ ≤ 1)
    (letter : Ω → A) (T : Ω → Ω) (p y : Ω → E)
    (hp : stationarySkewApply R letter T p = p)
    (C : ℝ) (hy : ∀ x, ‖y x‖ ≤ C) (x : Ω) :
    Tendsto (fun N => birkhoffAverage ℝ
      (stationarySkewApply R letter T) id N
        (p + (stationarySkewApply R letter T y - y)) x)
      atTop (𝓝 (p x)) := by
  let U := stationarySkewApply R letter T
  let d : ℕ → E := fun N => (U^[N] y) x - y x
  have hd : ∀ N, ‖d N‖ ≤ 2 * C := by
    intro N
    calc
      ‖d N‖ ≤ ‖(U^[N] y) x‖ + ‖y x‖ := norm_sub_le _ _
      _ ≤ C + C := add_le_add
        ((norm_iterate_stationarySkewApply_le R hR letter T y N x).trans
          (hy (T^[N] x))) (hy x)
      _ = 2 * C := by ring
  have hdbounded : IsBoundedUnder (· ≤ ·) atTop (norm ∘ d) :=
    isBoundedUnder_of ⟨2 * C, fun N => hd N⟩
  have hzero : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ • d N) atTop (𝓝 0) :=
    NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded
      tendsto_inv_atTop_nhds_zero_nat hdbounded
  have htarget : Tendsto (fun N : ℕ => p x + (N : ℝ)⁻¹ • d N)
      atTop (𝓝 (p x)) := by
    simpa using tendsto_const_nhds.add hzero
  apply htarget.congr'
  filter_upwards [eventually_ne_atTop 0] with N hN
  rw [birkhoffAverage_stationarySkewApply_add]
  have hfixed : Function.IsFixedPt U p := hp
  rw [hfixed.birkhoffAverage_eq ℝ id (Nat.cast_ne_zero.mpr hN)]
  change p x + (N : ℝ)⁻¹ • d N =
    p x + birkhoffAverage ℝ U id N (U y - y) x
  rw [birkhoffAverage_stationarySkewApply_coboundary]

/-- The all-times deviation set between the skew averages of two functions. -/
def stationarySkewMaxErrorSet (R : A → E →L[ℝ] E)
    (letter : Ω → A) (T : Ω → Ω) (g h : Ω → E) (ε : ℝ) : Set Ω :=
  {x | ∃ N, N ≠ 0 ∧ ε < ‖birkhoffAverage ℝ
    (stationarySkewApply R letter T) id N g x -
      birkhoffAverage ℝ (stationarySkewApply R letter T) id N h x‖}

theorem stationarySkewMaxErrorSet_subset_birkhoffMaxSet_norm_sub
    (R : A → E →L[ℝ] E) (hR : ∀ a, ‖R a‖ ≤ 1)
    (letter : Ω → A) (T : Ω → Ω) (g h : Ω → E) (ε : ℝ) :
    stationarySkewMaxErrorSet R letter T g h ε ⊆
      birkhoffMaxSet T (fun x => ‖g x - h x‖) ε := by
  intro x hx
  obtain ⟨N, hN, havg⟩ := hx
  refine ⟨N, hN, havg.trans_le ?_⟩
  rw [← Pi.sub_apply, ← birkhoffAverage_stationarySkewApply_sub]
  exact norm_birkhoffAverage_stationarySkewApply_le
    R hR letter T (g - h) N x

/-- Maximal inequality for deviations of two vector-valued skew averages. -/
theorem measure_stationarySkewMaxErrorSet_le_ofReal_integral_norm_sub_div
    [IsFiniteMeasure μ]
    (R : A → E →L[ℝ] E) (hR : ∀ a, ‖R a‖ ≤ 1)
    (letter : Ω → A) (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (g h : Ω → E) (hghmeas : Measurable (fun x => ‖g x - h x‖))
    (hgh : Integrable (fun x => ‖g x - h x‖) μ)
    (ε : ℝ) (hε : 0 < ε) :
    μ (stationarySkewMaxErrorSet R letter T g h ε) ≤
      ENNReal.ofReal ((∫ x, ‖g x - h x‖ ∂μ) / ε) := by
  exact (measure_mono
    (stationarySkewMaxErrorSet_subset_birkhoffMaxSet_norm_sub
      R hR letter T g h ε)).trans
    (measure_birkhoffMaxSet_le_ofReal_integral_div T hT
      (fun x => ‖g x - h x‖) hghmeas hgh
      (fun x => norm_nonneg _) ε hε)

/-- Borel--Cantelli uniform approximation for vector-valued skew averages. -/
theorem ae_eventually_forall_norm_stationarySkewAverage_sub_le
    [IsFiniteMeasure μ]
    (R : A → E →L[ℝ] E) (hR : ∀ a, ‖R a‖ ≤ 1)
    (letter : Ω → A) (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (g : Ω → E) (h : ℕ → Ω → E)
    (hghmeas : ∀ k, Measurable (fun x => ‖g x - h k x‖))
    (hgh : ∀ k, Integrable (fun x => ‖g x - h k x‖) μ)
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k)
    (hsum : Summable (fun k => (∫ x, ‖g x - h k x‖ ∂μ) / ε k)) :
    ∀ᵐ x ∂μ, ∀ᶠ k in atTop, ∀ N,
      ‖birkhoffAverage ℝ (stationarySkewApply R letter T) id N g x -
        birkhoffAverage ℝ (stationarySkewApply R letter T) id N (h k) x‖ ≤ ε k := by
  have hscalar :=
    ae_eventually_forall_birkhoffAverage_le_of_summable_integral_div
      T hT (fun k x => ‖g x - h k x‖) hghmeas hgh
      (fun _ _ => norm_nonneg _) ε hε hsum
  filter_upwards [hscalar] with x hx
  filter_upwards [hx] with k hk
  intro N
  by_cases hN : N = 0
  · simp [hN, (hε k).le]
  · have hdom :
        ‖birkhoffAverage ℝ (stationarySkewApply R letter T) id N g x -
          birkhoffAverage ℝ (stationarySkewApply R letter T) id N (h k) x‖ ≤
          birkhoffAverage ℝ T (fun y => ‖(g - h k) y‖) N x := by
      rw [← Pi.sub_apply, ← birkhoffAverage_stationarySkewApply_sub]
      exact norm_birkhoffAverage_stationarySkewApply_le
        R hR letter T (g - h k) N x
    exact hdom.trans (hk N hN)

/-- Banach-principle closure for the pointwise skew averages, in the exact
summable-approximation form supplied by the maximal inequality. -/
theorem ae_exists_tendsto_stationarySkewAverage_of_approx
    [IsFiniteMeasure μ] [CompleteSpace E]
    (R : A → E →L[ℝ] E) (hR : ∀ a, ‖R a‖ ≤ 1)
    (letter : Ω → A) (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (g : Ω → E) (h : ℕ → Ω → E)
    (hghmeas : ∀ k, Measurable (fun x => ‖g x - h k x‖))
    (hgh : ∀ k, Integrable (fun x => ‖g x - h k x‖) μ)
    (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k) (hε0 : Tendsto ε atTop (𝓝 0))
    (hsum : Summable (fun k => (∫ x, ‖g x - h k x‖ ∂μ) / ε k))
    (hconv : ∀ k, ∀ᵐ x ∂μ, ∃ a : E, Tendsto
      (fun N => birkhoffAverage ℝ (stationarySkewApply R letter T)
        id N (h k) x) atTop (𝓝 a)) :
    ∀ᵐ x ∂μ, ∃ a : E, Tendsto
      (fun N => birkhoffAverage ℝ (stationarySkewApply R letter T)
        id N g x) atTop (𝓝 a) := by
  rw [← ae_all_iff] at hconv
  filter_upwards [hconv,
    ae_eventually_forall_norm_stationarySkewAverage_sub_le
      R hR letter T hT g h hghmeas hgh ε hε hsum] with x hxconv hxclose
  let u : ℕ → E := fun N =>
    birkhoffAverage ℝ (stationarySkewApply R letter T) id N g x
  let v : ℕ → ℕ → E := fun k N =>
    birkhoffAverage ℝ (stationarySkewApply R letter T) id N (h k) x
  have hv : ∀ k, CauchySeq (v k) := by
    intro k
    exact (hxconv k).choose_spec.cauchySeq
  have hu : CauchySeq u :=
    cauchySeq_of_eventually_uniform_approx u v ε hε0 hv (by
      simpa only [u, v, dist_eq_norm] using hxclose)
  exact cauchySeq_tendsto_of_complete hu

/-- Closedness form of the Banach principle.  Pointwise convergence passes
from any sequence of approximants converging to `g` in the scalar `L¹` norm.
The proof selects a quadratically fast subsequence and applies the preceding
summable-approximation theorem. -/
theorem ae_exists_tendsto_stationarySkewAverage_of_tendsto_integral_norm_sub
    [IsFiniteMeasure μ] [CompleteSpace E]
    (R : A → E →L[ℝ] E) (hR : ∀ a, ‖R a‖ ≤ 1)
    (letter : Ω → A) (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (g : Ω → E) (h : ℕ → Ω → E)
    (hghmeas : ∀ j, Measurable (fun x => ‖g x - h j x‖))
    (hgh : ∀ j, Integrable (fun x => ‖g x - h j x‖) μ)
    (hL1 : Tendsto (fun j => ∫ x, ‖g x - h j x‖ ∂μ) atTop (𝓝 0))
    (hconv : ∀ j, ∀ᵐ x ∂μ, ∃ a : E, Tendsto
      (fun N => birkhoffAverage ℝ (stationarySkewApply R letter T)
        id N (h j) x) atTop (𝓝 a)) :
    ∀ᵐ x ∂μ, ∃ a : E, Tendsto
      (fun N => birkhoffAverage ℝ (stationarySkewApply R letter T)
        id N g x) atTop (𝓝 a) := by
  let c : ℝ := (2 : ℝ)⁻¹
  have hcpos : 0 < c := by norm_num [c]
  have hclt : |c| < 1 := by norm_num [c, abs_of_nonneg]
  have hextract : ∀ k : ℕ, ∃ j : ℕ,
      (∫ x, ‖g x - h j x‖ ∂μ) < c ^ (2 * k) := by
    intro k
    have hpow : 0 < c ^ (2 * k) := pow_pos hcpos _
    exact ((tendsto_order.1 hL1).2 _ hpow).exists
  choose φ hφ using hextract
  let h' : ℕ → Ω → E := fun k => h (φ k)
  let ε : ℕ → ℝ := fun k => c ^ k
  have hε : ∀ k, 0 < ε k := fun k => pow_pos hcpos _
  have hε0 : Tendsto ε atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one hclt
  have hsum : Summable (fun k =>
      (∫ x, ‖g x - h' k x‖ ∂μ) / ε k) := by
    apply Summable.of_nonneg_of_le (fun k =>
      div_nonneg (integral_nonneg fun _ => norm_nonneg _) (hε k).le)
      (fun k => ?_) (summable_geometric_of_norm_lt_one hclt)
    apply (div_le_iff₀ (hε k)).2
    have hk := (hφ k).le
    simpa only [h', ε, c, ← pow_add, two_mul] using hk
  exact ae_exists_tendsto_stationarySkewAverage_of_approx
    R hR letter T hT g h'
    (fun k => hghmeas (φ k)) (fun k => hgh (φ k))
    ε hε hε0 hsum (fun k => hconv (φ k))

/-- Terminal dense-core form: if `g` is approximated in `L¹` by one fixed
point plus bounded skew coboundaries, then its skew averages converge almost
everywhere.  The maximal inequality supplies the closure; boundedness is used
only to telescope the core averages pointwise. -/
theorem ae_exists_tendsto_stationarySkewAverage_of_fixed_bounded_coboundary_approx
    [IsFiniteMeasure μ] [CompleteSpace E]
    (R : A → E →L[ℝ] E) (hR : ∀ a, ‖R a‖ ≤ 1)
    (letter : Ω → A) (T : Ω → Ω) (hT : MeasurePreserving T μ μ)
    (g p : Ω → E) (y : ℕ → Ω → E) (C : ℕ → ℝ)
    (hp : stationarySkewApply R letter T p = p)
    (hy : ∀ k x, ‖y k x‖ ≤ C k)
    (herr_meas : ∀ k, Measurable (fun x =>
      ‖g x - (p + (stationarySkewApply R letter T (y k) - y k)) x‖))
    (herr_int : ∀ k, Integrable (fun x =>
      ‖g x - (p + (stationarySkewApply R letter T (y k) - y k)) x‖) μ)
    (herr_zero : Tendsto (fun k => ∫ x,
      ‖g x - (p + (stationarySkewApply R letter T (y k) - y k)) x‖ ∂μ)
      atTop (𝓝 0)) :
    ∀ᵐ x ∂μ, ∃ a : E, Tendsto
      (fun N => birkhoffAverage ℝ (stationarySkewApply R letter T)
        id N g x) atTop (𝓝 a) := by
  let h : ℕ → Ω → E := fun k =>
    p + (stationarySkewApply R letter T (y k) - y k)
  apply ae_exists_tendsto_stationarySkewAverage_of_tendsto_integral_norm_sub
    R hR letter T hT g h
  · exact herr_meas
  · exact herr_int
  · exact herr_zero
  · intro k
    exact Filter.Eventually.of_forall fun x =>
      ⟨p x, tendsto_birkhoffAverage_fixed_add_bounded_coboundary
        R hR letter T p (y k) hp (C k) (hy k) x⟩

end SkewMaximal

end IndependentZeroBlocks
