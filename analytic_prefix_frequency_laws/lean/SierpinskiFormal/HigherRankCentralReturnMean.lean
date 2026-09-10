import SierpinskiFormal.RenewalWordGenerating
import SierpinskiFormal.RealWordGenerating
import SierpinskiFormal.FieldReturnGroup
import SierpinskiFormal.CountableAbelGroupMean
import SierpinskiFormal.CountableGroupMoments
import SierpinskiFormal.CountableGroupCanonicalMean
import SierpinskiFormal.CesaroAbelTransfer
import SierpinskiFormal.WeightedWordEnumeration

/-!
# Rational central means from minimum-rank returns

The exact-length central word average first has a Cesaro limit by the stable
finite-dimensional matrix coefficient theorem.  Splitting the same word at
internal reset markers identifies its physical-length Abel mean with a
geometrically discounted countable return-group orbit.  The latter has a
rational limit, forcing the already-existing Cesaro limit to be rational.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Filter Set Topology
open scoped BigOperators Topology

namespace IndependentZeroBlocks

variable {F C ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
variable [Fintype C] [Nonempty C] [DecidableEq C]
variable [TopologicalSpace C] [DiscreteTopology C]

/-- A fixed sequence of Abel parameters approaching one from below. -/
def canonicalAbelParameter (n : ℕ) : ℝ :=
  1 - (((n + 2 : ℕ) : ℝ))⁻¹

theorem canonicalAbelParameter_nonneg (n : ℕ) :
    0 ≤ canonicalAbelParameter n := by
  unfold canonicalAbelParameter
  have htwo : (2 : ℝ) ≤ (n + 2 : ℕ) := by exact_mod_cast Nat.le_add_left 2 n
  have hinv : (((n + 2 : ℕ) : ℝ))⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by positivity : (0 : ℝ) < (n + 2 : ℕ))]
    exact le_trans (by norm_num : (1 : ℝ) ≤ 2) htwo
  linarith

theorem canonicalAbelParameter_lt_one (n : ℕ) :
    canonicalAbelParameter n < 1 := by
  unfold canonicalAbelParameter
  have : (0 : ℝ) < (((n + 2 : ℕ) : ℝ))⁻¹ := by positivity
  linarith

theorem tendsto_canonicalAbelParameter :
    Tendsto canonicalAbelParameter atTop (nhds 1) := by
  have htop : Tendsto (fun n : ℕ ↦ ((n + 2 : ℕ) : ℝ)) atTop atTop := by
    have hn : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have htwo : Tendsto (fun _ : ℕ ↦ (2 : ℝ)) atTop (nhds 2) :=
      tendsto_const_nhds
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hn.atTop_add htwo
  have hinv : Tendsto (fun n : ℕ ↦ (((n + 2 : ℕ) : ℝ))⁻¹)
      atTop (nhds 0) := htop.inv_tendsto_atTop
  have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hsub : Tendsto
      (fun n : ℕ ↦ 1 - (((n + 2 : ℕ) : ℝ))⁻¹) atTop (nhds 1) := by
    simpa only [sub_zero] using hone.sub hinv
  change Tendsto (fun n : ℕ ↦ 1 - (((n + 2 : ℕ) : ℝ))⁻¹)
    atTop (nhds 1)
  exact hsub

/-- Boolean scalar observation of one compressed return word. -/
def centralReturnPredicate {r : ℕ}
    (M : C → Matrix ι ι F) (U : Matrix ι (Fin r) F)
    (V : Matrix (Fin r) ι F)
    (left : Module.Dual F (Fin r → F)) (seed : Fin r → F)
    (w : List C) : Bool :=
  nonzeroBool (left ((returnMatrix M U V w).mulVec seed))

/-- Exact-support free-group predicate associated with the central return
observation. -/
def centralReturnGroupPredicate {r : ℕ}
    (M : C → Matrix ι ι F) (U : Matrix ι (Fin r) F)
    (V : Matrix (Fin r) ι F)
    (hunit : ∀ y : List C, IsUnit (returnMatrix M U V y))
    (e : C) (left : Module.Dual F (Fin r → F)) (seed : Fin r → F) :
    FreeGroup (GapWords e) → Bool :=
  encodedReturnGroupScalarPredicate M U V hunit
    (fun g : GapWords e ↦ g.1) left seed

/-- Send marker-free words to their exact-support generator; values outside
the support are irrelevant to the canonical marker-gap factorization. -/
def gapFreeGroupLetter (e : C) (y : List C) : FreeGroup (GapWords e) :=
  if hy : e ∉ y then FreeGroup.of ⟨y, hy⟩ else 1

@[simp] theorem gapFreeGroupLetter_gap (e : C) (g : GapWords e) :
    gapFreeGroupLetter e g.1 = FreeGroup.of g := by
  simp [gapFreeGroupLetter, g.2]

/-- Canonical marker gaps, carrying their marker-free proofs. -/
def typedMarkerGaps (e : C) (w : List C) : List (GapWords e) :=
  ((markerGapListsEquivNonemptyGapWords e) (markerGapEquiv e w)).1

theorem typedMarkerGaps_map_val (e : C) (w : List C) :
    (typedMarkerGaps e w).map Subtype.val = markerGaps e w := by
  simp [typedMarkerGaps, markerGapListsEquivNonemptyGapWords, markerGapEquiv]

theorem positiveFreeGroupWord_typedMarkerGaps (e : C) (w : List C) :
    positiveFreeGroupWord (typedMarkerGaps e w) =
      ((markerGaps e w).map (gapFreeGroupLetter e)).prod := by
  unfold positiveFreeGroupWord
  rw [← typedMarkerGaps_map_val e w, List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro g hg
  simp

/-- A positive list of actual gaps evaluates to the return of the word
formed by inserting the marker between consecutive gaps. -/
theorem centralReturnGroupPredicate_positiveGapWord {r : ℕ}
    (M : C → Matrix ι ι F) (e : C)
    (U : Matrix ι (Fin r) F) (V : Matrix (Fin r) ι F)
    (hfac : matrixWord M [e] = U * V)
    (hunit : ∀ y : List C, IsUnit (returnMatrix M U V y))
    (left : Module.Dual F (Fin r → F)) (seed : Fin r → F)
    (g : GapWords e) (gs : List (GapWords e)) :
    centralReturnGroupPredicate M U V hunit e left seed
        (positiveFreeGroupWord (g :: gs)) =
      centralReturnPredicate M U V left seed
        ([e].intercalate ((g :: gs).map Subtype.val)) := by
  unfold centralReturnGroupPredicate centralReturnPredicate
    encodedReturnGroupScalarPredicate
  rw [encodedReturnFreeGroupLinearAction_positiveWord]
  congr 2
  change (List.map (fun d : GapWords e ↦ returnMatrix M U V d.1)
      (g :: gs)).prod.mulVec seed =
    (returnMatrix M U V
      ([e].intercalate (g.1 :: gs.map Subtype.val))).mulVec seed
  rw [← returnMatrix_prod_intercalate_marker M e U V hfac]
  have hmaps : gs.map (fun d ↦ returnMatrix M U V d.1) =
      (gs.map Subtype.val).map (returnMatrix M U V) := by
    rw [List.map_map]
    rfl
  simp only [List.map_cons]
  rw [hmaps]

/-- The canonical positive free-group word attached to all marker gaps of a
word evaluates to the original central return predicate. -/
theorem centralReturnGroupPredicate_typedMarkerGaps {r : ℕ}
    (M : C → Matrix ι ι F) (e : C)
    (U : Matrix ι (Fin r) F) (V : Matrix (Fin r) ι F)
    (hfac : matrixWord M [e] = U * V)
    (hunit : ∀ y : List C, IsUnit (returnMatrix M U V y))
    (left : Module.Dual F (Fin r → F)) (seed : Fin r → F)
    (w : List C) :
    centralReturnGroupPredicate M U V hunit e left seed
        (positiveFreeGroupWord (typedMarkerGaps e w)) =
      centralReturnPredicate M U V left seed w := by
  have hne : typedMarkerGaps e w ≠ [] := by
    intro hnil
    have hmap := congrArg (List.map Subtype.val) hnil
    rw [typedMarkerGaps_map_val] at hmap
    exact markerGaps_ne_nil e w (by simpa using hmap)
  cases hgs : typedMarkerGaps e w with
  | nil => exact (hne hgs).elim
  | cons g gs =>
      rw [centralReturnGroupPredicate_positiveGapWord
        M e U V hfac hunit left seed g gs]
      have hmap := congrArg (List.map Subtype.val) hgs
      rw [typedMarkerGaps_map_val] at hmap
      simpa [hmap] using congrArg
        (centralReturnPredicate M U V left seed)
        (intercalate_markerGaps e w)

/-- Exact-length IID expectation of the central return predicate. -/
def centralReturnExactAverage {r : ℕ}
    (M : C → Matrix ι ι F) (U : Matrix ι (Fin r) F)
    (V : Matrix (Fin r) ι F)
    (left : Module.Dual F (Fin r → F)) (seed : Fin r → F)
    (p : C → ℝ) (n : ℕ) : ℝ :=
  weightedWordExtensionAverage p
    (booleanWordIndicator (centralReturnPredicate M U V left seed)) n []

def centralReturnGapLaw (p : C → ℝ) (e : C) (s : ℝ) : GapWords e → ℝ :=
  tiltedGapLaw (realNonMarkerMass p e) s p e

def centralReturnDiscount (p : C → ℝ) (e : C) (s : ℝ) : ℝ :=
  renewalMarkerDiscount (realNonMarkerMass p e) s

/-- A compressed return observation is still an ordinary finite-dimensional
matrix-word coefficient, hence has the Boolean double-limit property even
before invertibility of the return matrices is used. -/
theorem centralReturnPredicate_hasBooleanDoubleLimitProperty {r : ℕ}
    (M : C → Matrix ι ι F) (U : Matrix ι (Fin r) F)
    (V : Matrix (Fin r) ι F)
    (left : Module.Dual F (Fin r → F)) (seed : Fin r → F) :
    HasBooleanDoubleLimitProperty (fun w z : List C ↦
      centralReturnPredicate M U V left seed (z ++ w)) := by
  let left' : Module.Dual F (ι → F) := left.comp V.mulVecLin
  let seed' : ι → F := U.mulVec seed
  have h := field_matrixWord_rightKernel_hasBooleanDoubleLimitProperty M left' seed'
  simpa only [centralReturnPredicate, returnMatrix, matrixWord_append,
    Matrix.mulVec_mulVec, LinearMap.comp_apply, Matrix.mulVecLin_apply,
    Matrix.mul_assoc, left', seed'] using h

/-- The physical word-length central averages always have a Cesaro limit for
an arbitrary finite probability law. -/
theorem exists_tendsto_centralReturnCesaro {r : ℕ}
    (M : C → Matrix ι ι F) (U : Matrix ι (Fin r) F)
    (V : Matrix (Fin r) ι F)
    (left : Module.Dual F (Fin r → F)) (seed : Fin r → F)
    (p : C → ℝ) (hp : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1) :
    ∃ L : ℝ, Tendsto
      (realCesaroMean (centralReturnExactAverage M U V left seed p))
      atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := exists_tendsto_boolean_weighted_iid_word_cesaro
    p hp hp1 (centralReturnPredicate M U V left seed)
    (centralReturnPredicate_hasBooleanDoubleLimitProperty M U V left seed)
  refine ⟨L, ?_⟩
  have heq : realCesaroMean
      (centralReturnExactAverage M U V left seed p) =
      weightedIidWordCesaro p
        (booleanWordIndicator (centralReturnPredicate M U V left seed)) := by
    funext N
    unfold realCesaroMean weightedIidWordCesaro centralReturnExactAverage
    rw [div_eq_mul_inv]
    ring
  rw [heq]
  exact hL

/-- The central exact-length average is bounded between zero and one. -/
theorem centralReturnExactAverage_mem_Icc {r : ℕ}
    (M : C → Matrix ι ι F) (U : Matrix ι (Fin r) F)
    (V : Matrix (Fin r) ι F)
    (left : Module.Dual F (Fin r → F)) (seed : Fin r → F)
    (p : C → ℝ) (hp : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1)
    (n : ℕ) :
    centralReturnExactAverage M U V left seed p n ∈ Set.Icc (0 : ℝ) 1 := by
  rw [centralReturnExactAverage, weightedWordExtensionAverage_eq_tuple_sum]
  constructor
  · exact Finset.sum_nonneg fun x hx ↦ mul_nonneg
      (wordWeight_nonneg p hp (List.ofFn x)) (by
        simp only [booleanWordIndicator_apply]
        cases hq : centralReturnPredicate M U V left seed (List.ofFn x) <;>
          simp [boolIndicator, hq])
  · calc
      (∑ x : Fin n → C, wordWeight p (List.ofFn x) *
          booleanWordIndicator (centralReturnPredicate M U V left seed)
            (List.ofFn x)) ≤
          ∑ x : Fin n → C, wordWeight p (List.ofFn x) := by
        apply Finset.sum_le_sum
        intro x hx
        have hw := wordWeight_nonneg p hp (List.ofFn x)
        apply mul_le_of_le_one_right hw
        cases hq : centralReturnPredicate M U V left seed (List.ofFn x) <;>
          simp [boolIndicator, hq]
      _ = 1 := sum_tuple_wordWeight_eq_one p hp1 n

/-- Exact physical-length Abel renewal identity for the central return
predicate.  The right side is the normalized tilted gap law and uses
`k+1` gaps for a word with `k` reset markers. -/
theorem centralReturnNormalizedAbelMean_eq_geometricGapMoments {r : ℕ}
    (M : C → Matrix ι ι F) (e : C)
    (U : Matrix ι (Fin r) F) (V : Matrix (Fin r) ι F)
    (hfac : matrixWord M [e] = U * V)
    (hunit : ∀ y : List C, IsUnit (returnMatrix M U V y))
    (left : Module.Dual F (Fin r → F)) (seed : Fin r → F)
    (p : C → ℝ) (hp : ∀ c, 0 < p c) (hp1 : ∑ c, p c = 1)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    realNormalizedAbelMean
        (centralReturnExactAverage M U V left seed p) s =
      (1 - centralReturnDiscount p e s) *
        ∑' k : ℕ, centralReturnDiscount p e s ^ k *
          countableGroupTupleMoment
            (centralReturnGroupPredicate M U V hunit e left seed)
            (FreeGroup.of : GapWords e → FreeGroup (GapWords e))
            (centralReturnGapLaw p e s) 1 1 (k + 1) := by
  let qG : FreeGroup (GapWords e) → Bool :=
    centralReturnGroupPredicate M U V hunit e left seed
  let code : List C → FreeGroup (GapWords e) := fun w ↦
    positiveFreeGroupWord (typedMarkerGaps e w)
  have hcode : ∀ w, code w =
      ((markerGaps e w).map (gapFreeGroupLetter e)).prod := by
    intro w
    exact positiveFreeGroupWord_typedMarkerGaps e w
  have hpredicate : (fun w ↦ qG (code w)) =
      centralReturnPredicate M U V left seed := by
    funext w
    exact centralReturnGroupPredicate_typedMarkerGaps
      M e U V hfac hunit left seed w
  have hp0 : ∀ c, 0 ≤ p c := fun c ↦ (hp c).le
  have hrlt : realNonMarkerMass p e < 1 := by
    rw [realNonMarkerMass_eq_one_sub p e hp1]
    linarith [hp e]
  letI : TopologicalSpace (FreeGroup (GapWords e)) := ⊥
  letI : DiscreteTopology (FreeGroup (GapWords e)) := ⟨rfl⟩
  have hrenewal := realNormalizedAbelMean_eq_geometricGapMoments
    e (realNonMarkerMass p e) s p hp0 hp1 rfl hrlt hs0 hs1
      (gapFreeGroupLetter e) code qG hcode
  rw [hpredicate] at hrenewal
  unfold centralReturnExactAverage
  simpa only [centralReturnDiscount,
    centralReturnGapLaw, qG, gapFreeGroupLetter_gap] using hrenewal

/-- Once the exact renewal regrouping has identified the physical Abel mean
with the normalized `(k+1)`-gap tuple series, countable return-group
rationality forces the already-existing physical Cesaro mean to be rational. -/
theorem exists_rational_tendsto_centralReturnCesaro_of_abel_eq {r : ℕ}
    (M : C → Matrix ι ι F) (e : C)
    (U : Matrix ι (Fin r) F) (V : Matrix (Fin r) ι F)
    (hunit : ∀ y : List C, IsUnit (returnMatrix M U V y))
    (left : Module.Dual F (Fin r → F)) (seed : Fin r → F)
    (p : C → ℝ) (hp : ∀ c, 0 < p c) (hp1 : ∑ c, p c = 1)
    (habel : ∀ n,
      realNormalizedAbelMean
          (centralReturnExactAverage M U V left seed p)
          (canonicalAbelParameter n) =
        (1 - centralReturnDiscount p e (canonicalAbelParameter n)) *
          ∑' k : ℕ,
            centralReturnDiscount p e (canonicalAbelParameter n) ^ k *
              countableGroupTupleMoment
                (centralReturnGroupPredicate M U V hunit e left seed)
                (FreeGroup.of : GapWords e → FreeGroup (GapWords e))
                (centralReturnGapLaw p e (canonicalAbelParameter n))
                1 1 (k + 1)) :
    ∃ q : ℚ, Tendsto
      (realCesaroMean (centralReturnExactAverage M U V left seed p))
      atTop (nhds (q : ℝ)) := by
  let r₀ := realNonMarkerMass p e
  have hp0 : ∀ c, 0 ≤ p c := fun c ↦ (hp c).le
  have hr₀_nonneg : 0 ≤ r₀ := by
    dsimp [r₀, realNonMarkerMass]
    exact Finset.sum_nonneg fun c hc ↦ by
      by_cases hce : c = e <;> simp [hce, hp0 c]
  have hr₀_lt : r₀ < 1 := by
    dsimp [r₀]
    rw [realNonMarkerMass_eq_one_sub p e hp1]
    linarith [hp e]
  let qG : FreeGroup (GapWords e) → Bool :=
    centralReturnGroupPredicate M U V hunit e left seed
  let step : GapWords e → FreeGroup (GapWords e) := FreeGroup.of
  let weight : ℕ → GapWords e → ℝ := fun n ↦
    centralReturnGapLaw p e (canonicalAbelParameter n)
  let weightLim : GapWords e → ℝ := centralReturnGapLaw p e 1
  let discount : ℕ → ℝ := fun n ↦
    centralReturnDiscount p e (canonicalAbelParameter n)
  letI : Countable (GapWords e) := Subtype.val_injective.countable
  letI : TopologicalSpace (FreeGroup (GapWords e)) := ⊥
  letI : DiscreteTopology (FreeGroup (GapWords e)) := ⟨rfl⟩
  letI : Countable (FreeGroup (GapWords e)) :=
    (encodedReturnFreeGroup_countable_and_generated_of_injective
      (fun g : GapWords e ↦ g.1) Subtype.val_injective).1
  have hDLP : HasBooleanDoubleLimitProperty (booleanGroupRightRow qG) := by
    exact encodedReturnGroupScalarPredicate_hasBooleanDoubleLimitProperty
      M U V hunit (fun g : GapWords e ↦ g.1) left seed
  have hweight : ∀ n g, 0 ≤ weight n g := by
    intro n g
    exact tiltedGapLaw_nonneg r₀ (canonicalAbelParameter n) p e hp0
      hr₀_nonneg hr₀_lt.le (canonicalAbelParameter_nonneg n)
      (canonicalAbelParameter_lt_one n).le g
  have hweight_sum : ∀ n, HasSum (weight n) 1 := by
    intro n
    exact hasSum_tiltedGapLaw_one r₀ (canonicalAbelParameter n) p e hp0 rfl
      hr₀_lt (canonicalAbelParameter_nonneg n)
      (canonicalAbelParameter_lt_one n).le
  have hweightLim : ∀ g, 0 < weightLim g := by
    intro g
    exact tiltedGapLaw_pos_at_one r₀ p e hp hr₀_lt g
  have hweightLim_sum : HasSum weightLim 1 :=
    hasSum_tiltedGapLaw_one r₀ 1 p e hp0 rfl hr₀_lt zero_le_one le_rfl
  have hgenerate : Subgroup.closure (Set.range step) = ⊤ := by
    exact (encodedReturnFreeGroup_countable_and_generated_of_injective
      (fun g : GapWords e ↦ g.1) Subtype.val_injective).2
  have hdiff : ∀ n, Summable fun g ↦ |weight n g - weightLim g| := by
    intro n
    exact ((hweight_sum n).summable.sub hweightLim_sum.summable).abs
  have hsWithin : Tendsto canonicalAbelParameter atTop
      (nhdsWithin (1 : ℝ) (Set.Icc 0 1)) := by
    apply tendsto_nhdsWithin_iff.2
    exact ⟨tendsto_canonicalAbelParameter, Eventually.of_forall fun n ↦
      ⟨canonicalAbelParameter_nonneg n,
        (canonicalAbelParameter_lt_one n).le⟩⟩
  have hl1 : Tendsto
      (fun n ↦ ∑' g, |weight n g - weightLim g|) atTop (nhds 0) := by
    exact (tendsto_tiltedGapLaw_discreteL1_of_nonMarkerMass_lt_one
      p e hp0 hr₀_lt).comp hsWithin
  have hdiscount : ∀ n, 0 ≤ discount n := by
    intro n
    exact renewalMarkerDiscount_nonneg r₀ (canonicalAbelParameter n)
      hr₀_nonneg hr₀_lt.le (canonicalAbelParameter_nonneg n)
      (canonicalAbelParameter_lt_one n).le
  have hdiscount_lt : ∀ n, discount n < 1 := by
    intro n
    exact renewalMarkerDiscount_lt_one r₀ (canonicalAbelParameter n)
      hr₀_nonneg hr₀_lt (canonicalAbelParameter_nonneg n)
      (canonicalAbelParameter_lt_one n)
  have hdiscount_one : Tendsto discount atTop (nhds 1) :=
    tendsto_renewalMarkerDiscount_one r₀ canonicalAbelParameter
      hr₀_lt tendsto_canonicalAbelParameter
  obtain ⟨q, hq⟩ := exists_rational_tendsto_countableGroupTupleAbel_succ
    qG hDLP step weight weightLim hweight hweight_sum hweightLim
      hweightLim_sum hgenerate hdiff hl1 discount hdiscount hdiscount_lt
      hdiscount_one (1 : FreeGroup (GapWords e))
  have hqPhysical : Tendsto (fun n ↦
      realNormalizedAbelMean
        (centralReturnExactAverage M U V left seed p)
        (canonicalAbelParameter n)) atTop (nhds (q : ℝ)) := by
    apply hq.congr'
    exact Eventually.of_forall fun n ↦ by
      simpa [qG, step, weight, discount, centralReturnGapLaw,
        centralReturnDiscount] using (habel n).symm
  obtain ⟨L, hL⟩ := exists_tendsto_centralReturnCesaro
    M U V left seed p hp0 hp1
  have hbound : ∀ n,
      |centralReturnExactAverage M U V left seed p n| ≤ 1 := by
    intro n
    have hn := centralReturnExactAverage_mem_Icc
      M U V left seed p hp0 hp1 n
    rw [abs_of_nonneg hn.1]
    exact hn.2
  have hAbel := tendsto_realNormalizedAbelMean_of_tendsto_realCesaroMean
    (centralReturnExactAverage M U V left seed p) 1 L hbound hL
  have hsBelow : Tendsto canonicalAbelParameter atTop
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) := by
    apply tendsto_nhdsWithin_iff.2
    exact ⟨tendsto_canonicalAbelParameter,
      Eventually.of_forall canonicalAbelParameter_lt_one⟩
  have hLPhysical := hAbel.comp hsBelow
  have hLq : L = (q : ℝ) := tendsto_nhds_unique hLPhysical hqPhysical
  exact ⟨q, hLq ▸ hL⟩

/-- For a positive finite IID law, a reset factorization whose return
matrices are units forces the physical word-length central Cesaro mean to be
rational.  The renewal identity needed by the group argument is discharged
here from the canonical marker-gap decomposition. -/
theorem exists_rational_tendsto_centralReturnCesaro {r : ℕ}
    (M : C → Matrix ι ι F) (e : C)
    (U : Matrix ι (Fin r) F) (V : Matrix (Fin r) ι F)
    (hfac : matrixWord M [e] = U * V)
    (hunit : ∀ y : List C, IsUnit (returnMatrix M U V y))
    (left : Module.Dual F (Fin r → F)) (seed : Fin r → F)
    (p : C → ℝ) (hp : ∀ c, 0 < p c) (hp1 : ∑ c, p c = 1) :
    ∃ q : ℚ, Tendsto
      (realCesaroMean (centralReturnExactAverage M U V left seed p))
      atTop (nhds (q : ℝ)) := by
  apply exists_rational_tendsto_centralReturnCesaro_of_abel_eq
    M e U V hunit left seed p hp hp1
  intro n
  exact centralReturnNormalizedAbelMean_eq_geometricGapMoments
    M e U V hfac hunit left seed p hp hp1 (canonicalAbelParameter n)
      (canonicalAbelParameter_nonneg n) (canonicalAbelParameter_lt_one n)

/-- For fixed return matrices and fixed boundary vectors, the rational
central Cesaro mean is independent of the strictly positive IID letter law.
Only the speed of convergence and the renewal clock depend on the law. -/
theorem exists_rational_forall_tendsto_centralReturnCesaro {r : ℕ}
    (M : C → Matrix ι ι F) (e : C)
    (U : Matrix ι (Fin r) F) (V : Matrix (Fin r) ι F)
    (hfac : matrixWord M [e] = U * V)
    (hunit : ∀ y : List C, IsUnit (returnMatrix M U V y))
    (left : Module.Dual F (Fin r → F)) (seed : Fin r → F) :
    ∃ q : ℚ, ∀ (p : C → ℝ), (∀ c, 0 < p c) → (∑ c, p c = 1) →
      Tendsto (realCesaroMean
        (centralReturnExactAverage M U V left seed p))
        atTop (nhds (q : ℝ)) := by
  let qG : FreeGroup (GapWords e) → Bool :=
    centralReturnGroupPredicate M U V hunit e left seed
  let step : GapWords e → FreeGroup (GapWords e) := FreeGroup.of
  let pRef : C → ℝ := uniformAlphabetWeight
  let rRef : ℝ := realNonMarkerMass pRef e
  let referenceWeight : GapWords e → ℝ := centralReturnGapLaw pRef e 1
  letI : Countable (GapWords e) := Subtype.val_injective.countable
  letI : TopologicalSpace (FreeGroup (GapWords e)) := ⊥
  letI : DiscreteTopology (FreeGroup (GapWords e)) := ⟨rfl⟩
  letI : Countable (FreeGroup (GapWords e)) :=
    (encodedReturnFreeGroup_countable_and_generated_of_injective
      (fun g : GapWords e ↦ g.1) Subtype.val_injective).1
  have hDLP : HasBooleanDoubleLimitProperty (booleanGroupRightRow qG) := by
    exact encodedReturnGroupScalarPredicate_hasBooleanDoubleLimitProperty
      M U V hunit (fun g : GapWords e ↦ g.1) left seed
  have hpRefPos : ∀ c, 0 < pRef c := by
    intro c
    exact uniformAlphabetWeight_pos c
  have hpRef0 : ∀ c, 0 ≤ pRef c := fun c ↦ (hpRefPos c).le
  have hpRef1 : ∑ c, pRef c = 1 := sum_uniformAlphabetWeight
  have hrRefLt : rRef < 1 := by
    dsimp [rRef]
    rw [realNonMarkerMass_eq_one_sub pRef e hpRef1]
    linarith [hpRefPos e]
  have href_pos : ∀ d, 0 < referenceWeight d := by
    intro d
    exact tiltedGapLaw_pos_at_one rRef pRef e hpRefPos hrRefLt d
  have href_sum : HasSum referenceWeight 1 := by
    exact hasSum_tiltedGapLaw_one rRef 1 pRef e hpRef0 rfl hrRefLt
      zero_le_one le_rfl
  have hgenerate : Subgroup.closure (Set.range step) = ⊤ := by
    exact (encodedReturnFreeGroup_countable_and_generated_of_injective
      (fun g : GapWords e ↦ g.1) Subtype.val_injective).2
  obtain ⟨q, hq⟩ :=
    exists_canonical_rational_tendsto_all_countableGroupTupleAbel_succ
      qG hDLP step referenceWeight href_pos href_sum hgenerate
  refine ⟨q, ?_⟩
  intro p hp hp1
  let r₀ := realNonMarkerMass p e
  let weight : ℕ → GapWords e → ℝ := fun n ↦
    centralReturnGapLaw p e (canonicalAbelParameter n)
  let weightLim : GapWords e → ℝ := centralReturnGapLaw p e 1
  let discount : ℕ → ℝ := fun n ↦
    centralReturnDiscount p e (canonicalAbelParameter n)
  have hp0 : ∀ c, 0 ≤ p c := fun c ↦ (hp c).le
  have hr₀_nonneg : 0 ≤ r₀ := by
    dsimp [r₀, realNonMarkerMass]
    exact Finset.sum_nonneg fun c hc ↦ by
      by_cases hce : c = e <;> simp [hce, hp0 c]
  have hr₀_lt : r₀ < 1 := by
    dsimp [r₀]
    rw [realNonMarkerMass_eq_one_sub p e hp1]
    linarith [hp e]
  have hweight : ∀ n g, 0 ≤ weight n g := by
    intro n g
    exact tiltedGapLaw_nonneg r₀ (canonicalAbelParameter n) p e hp0
      hr₀_nonneg hr₀_lt.le (canonicalAbelParameter_nonneg n)
      (canonicalAbelParameter_lt_one n).le g
  have hweight_sum : ∀ n, HasSum (weight n) 1 := by
    intro n
    exact hasSum_tiltedGapLaw_one r₀ (canonicalAbelParameter n) p e hp0 rfl
      hr₀_lt (canonicalAbelParameter_nonneg n)
      (canonicalAbelParameter_lt_one n).le
  have hweightLim : ∀ g, 0 < weightLim g := by
    intro g
    exact tiltedGapLaw_pos_at_one r₀ p e hp hr₀_lt g
  have hweightLim_sum : HasSum weightLim 1 :=
    hasSum_tiltedGapLaw_one r₀ 1 p e hp0 rfl hr₀_lt zero_le_one le_rfl
  have hdiff : ∀ n, Summable fun g ↦ |weight n g - weightLim g| := by
    intro n
    exact ((hweight_sum n).summable.sub hweightLim_sum.summable).abs
  have hsWithin : Tendsto canonicalAbelParameter atTop
      (nhdsWithin (1 : ℝ) (Set.Icc 0 1)) := by
    apply tendsto_nhdsWithin_iff.2
    exact ⟨tendsto_canonicalAbelParameter, Eventually.of_forall fun n ↦
      ⟨canonicalAbelParameter_nonneg n,
        (canonicalAbelParameter_lt_one n).le⟩⟩
  have hl1 : Tendsto
      (fun n ↦ ∑' g, |weight n g - weightLim g|) atTop (nhds 0) := by
    exact (tendsto_tiltedGapLaw_discreteL1_of_nonMarkerMass_lt_one
      p e hp0 hr₀_lt).comp hsWithin
  have hdiscount : ∀ n, 0 ≤ discount n := by
    intro n
    exact renewalMarkerDiscount_nonneg r₀ (canonicalAbelParameter n)
      hr₀_nonneg hr₀_lt.le (canonicalAbelParameter_nonneg n)
      (canonicalAbelParameter_lt_one n).le
  have hdiscount_lt : ∀ n, discount n < 1 := by
    intro n
    exact renewalMarkerDiscount_lt_one r₀ (canonicalAbelParameter n)
      hr₀_nonneg hr₀_lt (canonicalAbelParameter_nonneg n)
      (canonicalAbelParameter_lt_one n)
  have hdiscount_one : Tendsto discount atTop (nhds 1) :=
    tendsto_renewalMarkerDiscount_one r₀ canonicalAbelParameter
      hr₀_lt tendsto_canonicalAbelParameter
  have htuple := hq weight weightLim hweight hweight_sum hweightLim
    hweightLim_sum hdiff hl1 discount hdiscount hdiscount_lt
      hdiscount_one (1 : FreeGroup (GapWords e))
  have hqPhysical : Tendsto (fun n ↦
      realNormalizedAbelMean
        (centralReturnExactAverage M U V left seed p)
        (canonicalAbelParameter n)) atTop (nhds (q : ℝ)) := by
    apply htuple.congr'
    exact Eventually.of_forall fun n ↦ by
      simpa [qG, step, weight, discount, centralReturnGapLaw,
        centralReturnDiscount] using
        (centralReturnNormalizedAbelMean_eq_geometricGapMoments
          M e U V hfac hunit left seed p hp hp1 (canonicalAbelParameter n)
            (canonicalAbelParameter_nonneg n)
            (canonicalAbelParameter_lt_one n)).symm
  obtain ⟨L, hL⟩ := exists_tendsto_centralReturnCesaro
    M U V left seed p hp0 hp1
  have hbound : ∀ n,
      |centralReturnExactAverage M U V left seed p n| ≤ 1 := by
    intro n
    have hn := centralReturnExactAverage_mem_Icc
      M U V left seed p hp0 hp1 n
    rw [abs_of_nonneg hn.1]
    exact hn.2
  have hAbel := tendsto_realNormalizedAbelMean_of_tendsto_realCesaroMean
    (centralReturnExactAverage M U V left seed p) 1 L hbound hL
  have hsBelow : Tendsto canonicalAbelParameter atTop
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) := by
    apply tendsto_nhdsWithin_iff.2
    exact ⟨tendsto_canonicalAbelParameter,
      Eventually.of_forall canonicalAbelParameter_lt_one⟩
  have hLPhysical := hAbel.comp hsBelow
  have hLq : L = (q : ℝ) := tendsto_nhds_unique hLPhysical hqPhysical
  exact hLq ▸ hL

end IndependentZeroBlocks
