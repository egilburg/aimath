import SierpinskiFormal.StationarySkew
import SierpinskiFormal.StationaryMean
import SierpinskiFormal.StationaryPairedCompacta
import SierpinskiFormal.StationaryGraphWeakCluster
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Canonical one-sided digit source

An arbitrary finite-valued stationary process factors measurably through its
one-sided itinerary.  This file constructs that factor, proves invariance of
the pushed-forward law under the left shift, identifies every finite prefix,
and transfers almost-everywhere convergence back to the original source.
-/

noncomputable section

set_option maxSynthPendingDepth 3

open Function Filter Topology MeasureTheory

namespace IndependentZeroBlocks

/-- Removing or inserting the zeroth term does not change the cluster points
of a sequence.  This reconciles graph averages indexed by `N` but containing
`N+1` terms with the positive-length Birkhoff-average convention. -/
theorem mapClusterPt_atTop_succ_iff {Y : Type*} [TopologicalSpace Y]
    (y : Y) (u : ℕ → Y) :
    MapClusterPt y atTop (fun n => u (n + 1)) ↔
      MapClusterPt y atTop u := by
  simp only [mapClusterPt_iff_frequently]
  constructor
  · intro h s hs
    rw [frequently_atTop]
    intro N
    obtain ⟨n, hn, hns⟩ := frequently_atTop.1 (h s hs) N
    exact ⟨n + 1, hn.trans (Nat.le_succ n), hns⟩
  · intro h s hs
    rw [frequently_atTop]
    intro N
    obtain ⟨m, hm, hms⟩ := frequently_atTop.1 (h s hs) (N + 1)
    have hmpos : 0 < m := lt_of_lt_of_le (Nat.zero_lt_succ N) hm
    refine ⟨m - 1, ?_, ?_⟩
    · omega
    · simpa [Nat.sub_add_cancel hmpos] using hms

section Canonical

variable {A : Type*}

/-- The left shift on one-sided digit sequences. -/
def digitShift (s : ℕ → A) : ℕ → A := fun n => s (n + 1)

/-- The zeroth digit on the canonical sequence space. -/
def digitHead (s : ℕ → A) : A := s 0

@[simp] theorem digitShift_apply (s : ℕ → A) (n : ℕ) :
    digitShift s n = s (n + 1) := rfl

@[simp] theorem digitHead_apply (s : ℕ → A) : digitHead s = s 0 := rfl

variable [MeasurableSpace A]

 theorem measurable_digitShift : Measurable (digitShift : (ℕ → A) → ℕ → A) := by
  apply measurable_pi_lambda
  intro n
  exact measurable_pi_apply (n + 1)

 theorem measurable_digitHead : Measurable (digitHead : (ℕ → A) → A) :=
  measurable_pi_apply 0

variable [TopologicalSpace A]

 theorem continuous_digitShift : Continuous (digitShift : (ℕ → A) → ℕ → A) := by
  apply continuous_pi
  intro n
  exact continuous_apply (n + 1)

 theorem continuous_digitHead : Continuous (digitHead : (ℕ → A) → A) :=
  continuous_apply 0

end Canonical

section Itinerary

variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
  {μ : Measure Ω}

/-- The one-sided digit itinerary of a point in a stationary source. -/
def stationaryItinerary (letter : Ω → A) (T : Ω → Ω) (x : Ω) : ℕ → A :=
  fun n => letter (T^[n] x)

@[simp] theorem stationaryItinerary_apply (letter : Ω → A) (T : Ω → Ω)
    (x : Ω) (n : ℕ) :
    stationaryItinerary letter T x n = letter (T^[n] x) := rfl

 theorem measurable_stationaryItinerary
    (letter : Ω → A) (hletter : Measurable letter)
    (T : Ω → Ω) (hT : Measurable T) :
    Measurable (stationaryItinerary letter T) := by
  apply measurable_pi_lambda
  intro n
  exact hletter.comp (hT.iterate n)

@[simp] theorem digitHead_stationaryItinerary
    (letter : Ω → A) (T : Ω → Ω) (x : Ω) :
    digitHead (stationaryItinerary letter T x) = letter x := rfl

/-- The itinerary map semiconjugates the original dynamics to the one-sided
left shift. -/
theorem stationaryItinerary_semiconj
    (letter : Ω → A) (T : Ω → Ω) :
    Function.Semiconj (stationaryItinerary letter T) T digitShift := by
  intro x
  funext n
  simp only [stationaryItinerary_apply, digitShift_apply, Function.comp_apply]
  rw [Function.iterate_succ_apply]

 theorem iterate_digitShift_stationaryItinerary
    (letter : Ω → A) (T : Ω → Ω) (n : ℕ) (x : Ω) :
    digitShift^[n] (stationaryItinerary letter T x) =
      stationaryItinerary letter T (T^[n] x) := by
  exact (stationaryItinerary_semiconj letter T).iterate_right n x |>.symm

/-- The law of the one-sided itinerary of a measure-preserving source is
shift-invariant. -/
theorem measurePreserving_digitShift_map_stationaryItinerary
    (letter : Ω → A) (hletter : Measurable letter)
    (T : Ω → Ω) (hT : MeasurePreserving T μ μ) :
    MeasurePreserving digitShift
      (μ.map (stationaryItinerary letter T))
      (μ.map (stationaryItinerary letter T)) := by
  refine ⟨measurable_digitShift, ?_⟩
  rw [Measure.map_map measurable_digitShift
    (measurable_stationaryItinerary letter hletter T hT.measurable)]
  rw [show digitShift ∘ stationaryItinerary letter T =
      stationaryItinerary letter T ∘ T by
    funext x
    exact (stationaryItinerary_semiconj letter T x).symm]
  rw [← Measure.map_map
    (measurable_stationaryItinerary letter hletter T hT.measurable)
    hT.measurable, hT.map_eq]

/-- Canonical and original finite prefixes agree exactly under the itinerary
map. -/
theorem stationaryPrefix_digit_itinerary
    (letter : Ω → A) (T : Ω → Ω) (n : ℕ) (x : Ω) :
    stationaryPrefix digitHead digitShift n
        (stationaryItinerary letter T x) =
      stationaryPrefix letter T n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [stationaryPrefix_succ, stationaryPrefix_succ,
        digitHead_stationaryItinerary,
        ← stationaryItinerary_semiconj letter T]
      exact congrArg (List.cons (letter x)) (ih (T x))

/-- Every word-valued prefix average on the canonical digit source pulls back
exactly to the corresponding prefix average on the original source. -/
theorem stationaryWordCesaro_digit_itinerary
    [TopologicalSpace A] [DiscreteTopology A]
    (letter : Ω → A) (T : Ω → Ω) (q : BoundedWordFunction A)
    (N : ℕ) (x : Ω) :
    stationaryWordCesaro digitHead digitShift q N
        (stationaryItinerary letter T x) =
      stationaryWordCesaro letter T q N x := by
  apply BoundedContinuousFunction.ext
  intro z
  simp only [stationaryWordCesaro_apply,
    stationaryPrefix_digit_itinerary]

/-- Pull back almost-everywhere convergence of canonical word-valued prefix
averages through the itinerary map. -/
theorem ae_tendsto_stationaryWordCesaro_of_map_stationaryItinerary
    [TopologicalSpace A] [DiscreteTopology A]
    (letter : Ω → A) (hletter : Measurable letter)
    (T : Ω → Ω) (hT : Measurable T) (q : BoundedWordFunction A)
    (hcanon : ∀ᵐ s ∂μ.map (stationaryItinerary letter T),
      ∃ h : BoundedWordFunction A,
        Tendsto (fun N => stationaryWordCesaro digitHead digitShift q N s)
          atTop (𝓝 h)) :
    ∀ᵐ x ∂μ, ∃ h : BoundedWordFunction A,
      Tendsto (fun N => stationaryWordCesaro letter T q N x)
        atTop (𝓝 h) := by
  have hpull := ae_of_ae_map
    (measurable_stationaryItinerary letter hletter T hT).aemeasurable hcanon
  filter_upwards [hpull] with x hx
  obtain ⟨h, hh⟩ := hx
  refine ⟨h, hh.congr' (Filter.Eventually.of_forall fun N => ?_)⟩
  exact stationaryWordCesaro_digit_itinerary letter T q N x

end Itinerary

section ContinuousRawFlow

variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
  [Fintype A] [Nonempty A] [DecidableEq A]
  [MeasurableSpace A] [MeasurableSingletonClass A]

/-- On the canonical sequence space, every finite prefix is a continuous
function of the sequence. -/
def stationaryPrefixContinuousMap (n : ℕ) : C((ℕ → A), List A) := by
  refine ⟨stationaryPrefix digitHead digitShift n, ?_⟩
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
      have hcons : Continuous (fun p : A × List A => p.1 :: p.2) :=
        continuous_of_discreteTopology
      exact hcons.comp
        (continuous_digitHead.prodMk (ih.comp continuous_digitShift))

@[simp] theorem stationaryPrefixContinuousMap_apply (n : ℕ) (s : ℕ → A) :
    stationaryPrefixContinuousMap (A := A) n s =
      stationaryPrefix digitHead digitShift n s := rfl

/-- The `n`th prefix row as a continuous map into the raw, countable Boolean
right compactum used by the graph-state construction. -/
def stationaryBooleanRawRightContinuousMap (q : List A → Bool) (n : ℕ) :
    C((ℕ → A), BooleanWordRawRightCompactum q) := by
  let f : (ℕ → A) → (List A → Bool) := fun s =>
    booleanWordRow q (stationaryPrefix digitHead digitShift n s)
  have hf : Continuous f := by
    have hw : Continuous (booleanWordRow q) := continuous_of_discreteTopology
    exact hw.comp (stationaryPrefixContinuousMap (A := A) n).continuous
  have hmem : ∀ s, f s ∈ booleanWordRowClosure q := fun s =>
    subset_closure ⟨stationaryPrefix digitHead digitShift n s, rfl⟩
  exact ⟨fun s => ⟨f s, hmem s⟩, hf.subtype_mk hmem⟩

@[simp] theorem stationaryBooleanRawRightContinuousMap_val
    (q : List A → Bool) (n : ℕ) (s : ℕ → A) :
    (stationaryBooleanRawRightContinuousMap q n s).val =
      booleanWordRow q (stationaryPrefix digitHead digitShift n s) := rfl

/-- The paired-compactum lift of an actual prefix row is exactly the
corresponding right translate. -/
theorem booleanWordRawRightOrbitLift_stationaryRawRightContinuousMap
    [Countable A] (q : List A → Bool)
    (hDLP : HasBooleanDoubleLimitProperty (fun w z ↦ q (z ++ w)))
    (n : ℕ) (s : ℕ → A) :
    (booleanWordRawRightOrbitLift q hDLP
        (stationaryBooleanRawRightContinuousMap q n s) :
      BoundedWordFunction A) =
      wordRightTranslate (stationaryPrefix digitHead digitShift n s)
        (booleanWordIndicator q) := by
  apply BoundedContinuousFunction.ext
  intro z
  simp [booleanWordRow, wordRightTranslate_apply]

/-- Every lifted raw Boolean row has norm at most one. -/
theorem norm_booleanWordRawRightOrbitLift_le_one
    [Countable A] (q : List A → Bool)
    (hDLP : HasBooleanDoubleLimitProperty (fun w z ↦ q (z ++ w)))
    (g : BooleanWordRawRightCompactum q) :
    ‖booleanWordRawRightOrbitLift q hDLP g‖ ≤ 1 := by
  change ‖booleanWordRawRightEmbedding q g‖ ≤ 1
  rw [BoundedContinuousFunction.norm_le zero_le_one]
  intro z
  rw [booleanWordRawRightEmbedding_apply]
  cases g.val z <;> norm_num [boolIndicator]

/-- Under the double-limit property, the raw right-row compactum is
countable. -/
theorem booleanWordRawRightCompactum_countable
    [Countable A] (q : List A → Bool)
    (hDLP : HasBooleanDoubleLimitProperty (fun w z ↦ q (z ++ w))) :
    Countable (BooleanWordRawRightCompactum q) := by
  let B : List A → List A → Bool := booleanWordRow q
  have hB : HasBooleanDoubleLimitProperty B := by
    change HasBooleanDoubleLimitProperty (fun w z ↦ q (z ++ w))
    exact hDLP
  have hext : (booleanRowExtensionClosure B).Countable :=
    booleanRowExtensionClosure_countable B hB
  have hpre :
      booleanUltrafilterExtension ⁻¹' booleanRowExtensionClosure B =
        closure (Set.range B) := by
    ext g
    simp only [booleanRowExtensionClosure, Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨h, hh, heq⟩
      have : h = g := booleanUltrafilterExtension_injective heq
      simpa [this] using hh
    · intro hg
      exact ⟨g, hg, rfl⟩
  have hclosure : (closure (Set.range B)).Countable := by
    rw [← hpre]
    exact hext.preimage booleanUltrafilterExtension_injective
  exact Set.countable_coe_iff.mpr (by
    simpa only [BooleanWordRawRightCompactum, booleanWordRowClosure, B]
      using hclosure)

/-- The graph-state `L¹` average for the canonical raw right compactum,
embedded back into ambient bounded word functions. -/
def stationaryBooleanRawRightGraphCesaroLp
    [Countable A] {μ : Measure (ℕ → A)} [IsFiniteMeasure μ]
    (q : List A → Bool)
    (hDLP : HasBooleanDoubleLimitProperty (fun w z ↦ q (z ++ w)))
    (N : ℕ) : Lp (BoundedWordFunction A) 1 μ :=
  letI : Countable (BooleanWordRawRightCompactum q) :=
    booleanWordRawRightCompactum_countable q hDLP
  ContinuousLinearMap.compLpL (𝕜 := ℝ) 1 μ
    (Submodule.subtypeL (R := ℝ) (BooleanWordRightOrbitSpan q))
    (graphCesaroLp (μ := μ) (booleanWordRawRightOrbitLift q hDLP) 1
      (norm_booleanWordRawRightOrbitLift_le_one q hDLP)
      (stationaryBooleanRawRightContinuousMap q) N)

/-- The canonical graph-state average with graph index `N` is exactly the
Bochner skew average with positive length `N+1`. -/
theorem stationaryBooleanRawRightGraphCesaroLp_eq_birkhoffAverage
    [Countable A] {μ : Measure (ℕ → A)} [IsFiniteMeasure μ]
    (q : List A → Bool)
    (hDLP : HasBooleanDoubleLimitProperty (fun w z ↦ q (z ++ w)))
    (hshift : MeasurePreserving digitShift μ μ)
    (N : ℕ) :
    stationaryBooleanRawRightGraphCesaroLp (μ := μ) q hDLP N =
      birkhoffAverage ℝ
        (stationaryWordSkewL1CLM digitHead measurable_digitHead
          digitShift hshift)
        id (N + 1)
        (Lp.const 1 μ (booleanWordIndicator q)) := by
  letI : Countable (BooleanWordRawRightCompactum q) :=
    booleanWordRawRightCompactum_countable q hDLP
  let j : BooleanWordRawRightCompactum q → BooleanWordRightOrbitSpan q :=
    booleanWordRawRightOrbitLift q hDLP
  let g : ℕ → C((ℕ → A), BooleanWordRawRightCompactum q) :=
    stationaryBooleanRawRightContinuousMap q
  let S : Lp (BooleanWordRightOrbitSpan q) 1 μ :=
    graphCesaroLp (μ := μ) j 1
      (norm_booleanWordRawRightOrbitLift_le_one q hDLP) g N
  let ιE : BooleanWordRightOrbitSpan q →L[ℝ] BoundedWordFunction A :=
    Submodule.subtypeL (R := ℝ) (BooleanWordRightOrbitSpan q)
  have hall : ∀ᵐ s ∂μ, ∀ n,
      (graphRangeLp (μ := μ) j 1
        (norm_booleanWordRawRightOrbitLift_le_one q hDLP) (g n)) s =
        j (g n s) := ae_all_iff.2 fun n =>
      graphRangeLp_coeFn (μ := μ) j 1
        (norm_booleanWordRawRightOrbitLift_le_one q hDLP) (g n)
  have hright := birkhoffAverage_stationaryWordSkewL1CLM_const_coeFn
    digitHead measurable_digitHead digitShift hshift
      (booleanWordIndicator q) (N + 1)
  change ContinuousLinearMap.compLpL (𝕜 := ℝ) 1 μ ιE S = _
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (𝕜 := ℝ) ιE S,
    Lp.coeFn_smul (𝕜 := ℝ) (N + 1 : ℝ)⁻¹
      (∑ n ∈ Finset.range (N + 1),
        graphRangeLp (μ := μ) j 1
          (norm_booleanWordRawRightOrbitLift_le_one q hDLP) (g n)),
    coeFn_finset_sum_Lp (E := BooleanWordRightOrbitSpan q) (μ := μ)
      (Finset.range (N + 1)) (fun n =>
        graphRangeLp (μ := μ) j 1
          (norm_booleanWordRawRightOrbitLift_le_one q hDLP) (g n)),
    hall, hright] with s hcomp hsmul hsum hterms hr
  rw [hcomp]
  change ιE (S s) = _
  have hS : S s = (N + 1 : ℝ)⁻¹ • ∑ n ∈ Finset.range (N + 1),
      (graphRangeLp (μ := μ) j 1
        (norm_booleanWordRawRightOrbitLift_le_one q hDLP) (g n)) s := by
    change ((N + 1 : ℝ)⁻¹ • ∑ n ∈ Finset.range (N + 1),
      graphRangeLp (μ := μ) j 1
        (norm_booleanWordRawRightOrbitLift_le_one q hDLP) (g n)) s = _
    rw [hsmul, Pi.smul_apply, hsum]
  rw [hS]
  simp only [map_smul, map_sum, Finset.sum_apply]
  simp_rw [hterms]
  rw [hr]
  change (N + 1 : ℝ)⁻¹ • ∑ n ∈ Finset.range (N + 1),
      ((j (g n s) : BooleanWordRightOrbitSpan q) : BoundedWordFunction A) =
    stationaryWordCesaro digitHead digitShift (booleanWordIndicator q) (N + 1) s
  simp only [j, g,
    booleanWordRawRightOrbitLift_stationaryRawRightContinuousMap]
  simp only [stationaryWordCesaro, Nat.cast_add, Nat.cast_one]

/-- The first `N` lifted raw rows have exactly the canonical Boolean prefix
Cesàro barycenter. -/
theorem stationaryBooleanRawRightOrbitLift_average_eq_stationaryWordCesaro
    [Countable A] (q : List A → Bool)
    (hDLP : HasBooleanDoubleLimitProperty (fun w z ↦ q (z ++ w)))
    (N : ℕ) (s : ℕ → A) :
    (N : ℝ)⁻¹ • ∑ n ∈ Finset.range N,
        ((booleanWordRawRightOrbitLift q hDLP
          (stationaryBooleanRawRightContinuousMap q n s) :
            BooleanWordRightOrbitSpan q) : BoundedWordFunction A) =
      stationaryWordCesaro digitHead digitShift (booleanWordIndicator q) N s := by
  simp only [booleanWordRawRightOrbitLift_stationaryRawRightContinuousMap]
  rfl

/-- The `n`th raw Boolean word-translation flow, as a continuous map into
the common compact convex range hull. -/
def stationaryBooleanRawFlowContinuousMap (q : List A → Bool) (n : ℕ) :
    C((ℕ → A), booleanWordCompactHull q) := by
  let f : (ℕ → A) → BoundedWordFunction A := fun s =>
    wordRightTranslate (stationaryPrefix digitHead digitShift n s)
      (booleanWordIndicator q)
  have hf : Continuous f := by
    have hw : Continuous (fun w : List A =>
        wordRightTranslate w (booleanWordIndicator q)) :=
      continuous_of_discreteTopology
    exact hw.comp (stationaryPrefixContinuousMap (A := A) n).continuous
  have hmem : ∀ s, f s ∈ booleanWordCompactHull q := by
    intro s
    exact mapsTo_wordRightTranslate_of_mapsTo_letters
      (booleanWordCompactHull q)
      (mapsTo_wordRightTranslate_booleanWordCompactHull q)
      (stationaryPrefix digitHead digitShift n s)
      (booleanWordIndicator_mem_compactHull q)
  exact ⟨fun s => ⟨f s, hmem s⟩, hf.subtype_mk hmem⟩

@[simp] theorem stationaryBooleanRawFlowContinuousMap_apply
    (q : List A → Bool) (n : ℕ) (s : ℕ → A) :
    (stationaryBooleanRawFlowContinuousMap q n s : BoundedWordFunction A) =
      wordRightTranslate (stationaryPrefix digitHead digitShift n s)
        (booleanWordIndicator q) := rfl

/-- The barycentric average of the continuous raw-flow maps is exactly the
canonical pathwise Boolean prefix average. -/
theorem stationaryBooleanRawFlow_average_eq_stationaryWordCesaro
    (q : List A → Bool) (N : ℕ) (s : ℕ → A) :
    (N : ℝ)⁻¹ • ∑ n ∈ Finset.range N,
        ((stationaryBooleanRawFlowContinuousMap q n s :
          booleanWordCompactHull q) : BoundedWordFunction A) =
      stationaryWordCesaro digitHead digitShift (booleanWordIndicator q) N s := by
  rfl

end ContinuousRawFlow

end IndependentZeroBlocks
