import SierpinskiFormal.ModuleCentralReturnMean
import SierpinskiFormal.BooleanDoubleLimitClosure

/-!
# Finite Boolean central return means over modules

Finite Boolean operations on scalar rows of one module action remain stable
both on physical words and on the reversible return group.  The existing
marker-gap renewal argument therefore gives one law-independent rational
central mean for the whole Boolean observation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Filter Set Topology
open scoped BigOperators Topology

namespace IndependentZeroBlocks

variable {R C X B : Type*} [CommRing R]
variable [AddCommGroup X] [Module R X] [AddCommGroup B] [Module R B]
variable [IsNoetherian R X] [IsNoetherian R (Module.Dual R X)]
variable [IsNoetherian R B] [IsNoetherian R (Module.Dual R B)]
variable [Fintype C] [Nonempty C] [DecidableEq C]
variable [TopologicalSpace C] [DiscreteTopology C]

/-- A finite Boolean operation on scalar observations of one compressed
return action, with a common seed. -/
def moduleBooleanCentralReturnPredicate {d : ℕ}
    (op : (Fin d → Bool) → Bool)
    (T : C → Module.End R X) (U : B →ₗ[R] X) (V : X →ₗ[R] B)
    (left : Fin d → Module.Dual R B) (seed : B) (w : List C) : Bool :=
  op (fun j ↦ moduleCentralReturnPredicate T U V (left j) seed w)

/-- Exact-length IID expectation of the finite Boolean central predicate. -/
def moduleBooleanCentralReturnExactAverage {d : ℕ}
    (op : (Fin d → Bool) → Bool)
    (T : C → Module.End R X) (U : B →ₗ[R] X) (V : X →ₗ[R] B)
    (left : Fin d → Module.Dual R B) (seed : B)
    (p : C → ℝ) (n : ℕ) : ℝ :=
  weightedWordExtensionAverage p
    (booleanWordIndicator
      (moduleBooleanCentralReturnPredicate op T U V left seed)) n []

/-- The corresponding Boolean operation on scalar observations of the
reversible return-group action. -/
def moduleBooleanCentralReturnGroupPredicate {d : ℕ}
    (op : (Fin d → Bool) → Bool)
    (K : List C → (B ≃ₗ[R] B)) (e : C)
    (left : Fin d → Module.Dual R B) (seed : B)
    (g : FreeGroup (GapWords e)) : Bool :=
  op (fun j ↦ moduleCentralReturnGroupPredicate K e (left j) seed g)

/-- The physical Boolean central observation has the double-limit property. -/
theorem moduleBooleanCentralReturnPredicate_hasBooleanDoubleLimitProperty
    {d : ℕ} (op : (Fin d → Bool) → Bool)
    (T : C → Module.End R X) (U : B →ₗ[R] X) (V : X →ₗ[R] B)
    (left : Fin d → Module.Dual R B) (seed : B) :
    HasBooleanDoubleLimitProperty (fun w z : List C ↦
      moduleBooleanCentralReturnPredicate op T U V left seed (z ++ w)) := by
  change HasBooleanDoubleLimitProperty
    (booleanCombine op (fun j (w z : List C) ↦
      moduleCentralReturnPredicate T U V (left j) seed (z ++ w)))
  exact hasBooleanDoubleLimitProperty_booleanCombine op
      (fun j (w z : List C) ↦
        moduleCentralReturnPredicate T U V (left j) seed (z ++ w))
      (fun j ↦ moduleCentralReturnPredicate_hasBooleanDoubleLimitProperty
        T U V (left j) seed)

/-- The return-group Boolean observation has the double-limit property. -/
theorem moduleBooleanCentralReturnGroupPredicate_hasBooleanDoubleLimitProperty
    {d : ℕ} (op : (Fin d → Bool) → Bool)
    (K : List C → (B ≃ₗ[R] B)) (e : C)
    (left : Fin d → Module.Dual R B) (seed : B) :
    HasBooleanDoubleLimitProperty
      (booleanGroupRightRow
        (moduleBooleanCentralReturnGroupPredicate op K e left seed)) := by
  change HasBooleanDoubleLimitProperty
    (booleanCombine op (fun j (g h : FreeGroup (GapWords e)) ↦
      moduleCentralReturnGroupPredicate K e (left j) seed (h * g)))
  exact hasBooleanDoubleLimitProperty_booleanCombine op
      (fun j (g h : FreeGroup (GapWords e)) ↦
        moduleCentralReturnGroupPredicate K e (left j) seed (h * g))
      (fun j ↦ moduleReturnGroupPredicate_hasBooleanDoubleLimitProperty
        (fun g : GapWords e ↦ K g.1) (left j) seed)

/-- The canonical marker-gap word evaluates the original Boolean central
predicate, simultaneously for all rows. -/
theorem moduleBooleanCentralReturnGroupPredicate_typedMarkerGaps
    {d : ℕ} (op : (Fin d → Bool) → Bool)
    (T : C → Module.End R X) (e : C)
    (U : B →ₗ[R] X) (V : X →ₗ[R] B)
    (hfac : endoWord T [e] = U.comp V)
    (K : List C → (B ≃ₗ[R] B))
    (hK : ∀ y, (K y).toLinearMap = compressedReturn T U V y)
    (left : Fin d → Module.Dual R B) (seed : B) (w : List C) :
    moduleBooleanCentralReturnGroupPredicate op K e left seed
        (positiveFreeGroupWord (moduleTypedMarkerGaps e w)) =
      moduleBooleanCentralReturnPredicate op T U V left seed w := by
  apply congrArg op
  funext j
  exact moduleCentralReturnGroupPredicate_typedMarkerGaps
    T e U V hfac K hK (left j) seed w

/-- The Boolean central exact averages have a Cesaro limit under every
nonnegative normalized finite letter law. -/
theorem exists_tendsto_moduleBooleanCentralReturnCesaro
    {d : ℕ} (op : (Fin d → Bool) → Bool)
    (T : C → Module.End R X) (U : B →ₗ[R] X) (V : X →ₗ[R] B)
    (left : Fin d → Module.Dual R B) (seed : B)
    (p : C → ℝ) (hp : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1) :
    ∃ L : ℝ, Tendsto
      (realCesaroMean
        (moduleBooleanCentralReturnExactAverage op T U V left seed p))
      atTop (nhds L) := by
  obtain ⟨L, hL⟩ := exists_tendsto_boolean_weighted_iid_word_cesaro
    p hp hp1 (moduleBooleanCentralReturnPredicate op T U V left seed)
    (moduleBooleanCentralReturnPredicate_hasBooleanDoubleLimitProperty
      op T U V left seed)
  refine ⟨L, ?_⟩
  have heq : realCesaroMean
      (moduleBooleanCentralReturnExactAverage op T U V left seed p) =
      weightedIidWordCesaro p
        (booleanWordIndicator
          (moduleBooleanCentralReturnPredicate op T U V left seed)) := by
    funext N
    unfold realCesaroMean weightedIidWordCesaro
      moduleBooleanCentralReturnExactAverage
    rw [div_eq_mul_inv]
    ring
  rw [heq]
  exact hL

/-- Boolean central exact averages lie in the probability interval. -/
theorem moduleBooleanCentralReturnExactAverage_mem_Icc
    {d : ℕ} (op : (Fin d → Bool) → Bool)
    (T : C → Module.End R X) (U : B →ₗ[R] X) (V : X →ₗ[R] B)
    (left : Fin d → Module.Dual R B) (seed : B)
    (p : C → ℝ) (hp : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1)
    (n : ℕ) :
    moduleBooleanCentralReturnExactAverage op T U V left seed p n ∈
      Set.Icc (0 : ℝ) 1 := by
  apply weightedWordExtensionAverage_mem_Icc p hp hp1
  · intro w
    simp only [booleanWordIndicator_apply, boolIndicator]
    split <;> norm_num
  · intro w
    simp only [booleanWordIndicator_apply, boolIndicator]
    split <;> norm_num

/-- Any Cesaro limit of the Boolean central exact averages is a probability
value. -/
theorem moduleBooleanCentralReturnCesaroLimit_mem_Icc
    {d : ℕ} (op : (Fin d → Bool) → Bool)
    (T : C → Module.End R X) (U : B →ₗ[R] X) (V : X →ₗ[R] B)
    (left : Fin d → Module.Dual R B) (seed : B)
    (p : C → ℝ) (hp : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1)
    (L : ℝ)
    (hL : Tendsto (realCesaroMean
      (moduleBooleanCentralReturnExactAverage op T U V left seed p))
      atTop (nhds L)) : L ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · apply ge_of_tendsto hL
    exact Eventually.of_forall fun N ↦ realCesaroMean_nonneg
      (fun n ↦ (moduleBooleanCentralReturnExactAverage_mem_Icc
        op T U V left seed p hp hp1 n).1) N
  · apply le_of_tendsto hL
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact realCesaroMean_le_one
      (fun n ↦ (moduleBooleanCentralReturnExactAverage_mem_Icc
        op T U V left seed p hp hp1 n).2) hN

/-- Exact normalized Abel identity for the whole finite Boolean central
observation. -/
theorem moduleBooleanCentralReturnNormalizedAbelMean_eq_geometricGapMoments
    {d : ℕ} (op : (Fin d → Bool) → Bool)
    (T : C → Module.End R X) (e : C)
    (U : B →ₗ[R] X) (V : X →ₗ[R] B)
    (hfac : endoWord T [e] = U.comp V)
    (K : List C → (B ≃ₗ[R] B))
    (hK : ∀ y, (K y).toLinearMap = compressedReturn T U V y)
    (left : Fin d → Module.Dual R B) (seed : B)
    (p : C → ℝ) (hp : ∀ c, 0 < p c) (hp1 : ∑ c, p c = 1)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    realNormalizedAbelMean
        (moduleBooleanCentralReturnExactAverage op T U V left seed p) s =
      (1 - moduleCentralReturnDiscount p e s) *
        ∑' k : ℕ, moduleCentralReturnDiscount p e s ^ k *
          countableGroupTupleMoment
            (moduleBooleanCentralReturnGroupPredicate op K e left seed)
            (FreeGroup.of : GapWords e → FreeGroup (GapWords e))
            (moduleCentralReturnGapLaw p e s) 1 1 (k + 1) := by
  let qG : FreeGroup (GapWords e) → Bool :=
    moduleBooleanCentralReturnGroupPredicate op K e left seed
  let code : List C → FreeGroup (GapWords e) := fun w ↦
    positiveFreeGroupWord (moduleTypedMarkerGaps e w)
  have hcode : ∀ w, code w =
      ((markerGaps e w).map (moduleGapFreeGroupLetter e)).prod := by
    intro w
    exact positiveFreeGroupWord_moduleTypedMarkerGaps e w
  have hpredicate : (fun w ↦ qG (code w)) =
      moduleBooleanCentralReturnPredicate op T U V left seed := by
    funext w
    exact moduleBooleanCentralReturnGroupPredicate_typedMarkerGaps
      op T e U V hfac K hK left seed w
  have hp0 : ∀ c, 0 ≤ p c := fun c ↦ (hp c).le
  have hrlt : realNonMarkerMass p e < 1 := by
    rw [realNonMarkerMass_eq_one_sub p e hp1]
    linarith [hp e]
  letI : TopologicalSpace (FreeGroup (GapWords e)) := ⊥
  letI : DiscreteTopology (FreeGroup (GapWords e)) := ⟨rfl⟩
  have hrenewal := realNormalizedAbelMean_eq_geometricGapMoments
    e (realNonMarkerMass p e) s p hp0 hp1 rfl hrlt hs0 hs1
      (moduleGapFreeGroupLetter e) code qG hcode
  rw [hpredicate] at hrenewal
  unfold moduleBooleanCentralReturnExactAverage
  simpa only [
    moduleCentralReturnDiscount, moduleCentralReturnGapLaw, qG,
    moduleGapFreeGroupLetter_gap] using hrenewal

/-- One rational number is the Boolean central Cesaro mean for every
strictly positive normalized finite letter law.  The number and the return
data are fixed before the law is chosen. -/
theorem exists_rational_forall_tendsto_moduleBooleanCentralReturnCesaro
    {d : ℕ} (op : (Fin d → Bool) → Bool)
    (T : C → Module.End R X) (e : C)
    (U : B →ₗ[R] X) (V : X →ₗ[R] B)
    (hfac : endoWord T [e] = U.comp V)
    (K : List C → (B ≃ₗ[R] B))
    (hK : ∀ y, (K y).toLinearMap = compressedReturn T U V y)
    (left : Fin d → Module.Dual R B) (seed : B) :
    ∃ q : ℚ, ∀ (p : C → ℝ), (∀ c, 0 < p c) → (∑ c, p c = 1) →
      Tendsto (realCesaroMean
        (moduleBooleanCentralReturnExactAverage op T U V left seed p))
        atTop (nhds (q : ℝ)) := by
  let qG : FreeGroup (GapWords e) → Bool :=
    moduleBooleanCentralReturnGroupPredicate op K e left seed
  let step : GapWords e → FreeGroup (GapWords e) := FreeGroup.of
  let pRef : C → ℝ := uniformAlphabetWeight
  let rRef : ℝ := realNonMarkerMass pRef e
  let referenceWeight : GapWords e → ℝ :=
    moduleCentralReturnGapLaw pRef e 1
  letI : Countable (GapWords e) := Subtype.val_injective.countable
  letI : TopologicalSpace (FreeGroup (GapWords e)) := ⊥
  letI : DiscreteTopology (FreeGroup (GapWords e)) := ⟨rfl⟩
  letI : Countable (FreeGroup (GapWords e)) :=
    (moduleReturnFreeGroup_countable_and_generated (GapWords e)).1
  have hDLP : HasBooleanDoubleLimitProperty (booleanGroupRightRow qG) := by
    exact moduleBooleanCentralReturnGroupPredicate_hasBooleanDoubleLimitProperty
      op K e left seed
  have hpRefPos : ∀ c, 0 < pRef c := by
    intro c
    exact uniformAlphabetWeight_pos c
  have hpRef0 : ∀ c, 0 ≤ pRef c := fun c ↦ (hpRefPos c).le
  have hpRef1 : ∑ c, pRef c = 1 := sum_uniformAlphabetWeight
  have hrRefLt : rRef < 1 := by
    dsimp [rRef]
    rw [realNonMarkerMass_eq_one_sub pRef e hpRef1]
    linarith [hpRefPos e]
  have href_pos : ∀ g, 0 < referenceWeight g := by
    intro g
    exact tiltedGapLaw_pos_at_one rRef pRef e hpRefPos hrRefLt g
  have href_sum : HasSum referenceWeight 1 := by
    exact hasSum_tiltedGapLaw_one rRef 1 pRef e hpRef0 rfl hrRefLt
      zero_le_one le_rfl
  have hgenerate : Subgroup.closure (Set.range step) = ⊤ := by
    exact (moduleReturnFreeGroup_countable_and_generated (GapWords e)).2
  obtain ⟨q, hq⟩ :=
    exists_canonical_rational_tendsto_all_countableGroupTupleAbel_succ
      qG hDLP step referenceWeight href_pos href_sum hgenerate
  refine ⟨q, ?_⟩
  intro p hp hp1
  let r₀ := realNonMarkerMass p e
  let weight : ℕ → GapWords e → ℝ := fun n ↦
    moduleCentralReturnGapLaw p e (moduleCanonicalAbelParameter n)
  let weightLim : GapWords e → ℝ := moduleCentralReturnGapLaw p e 1
  let discount : ℕ → ℝ := fun n ↦
    moduleCentralReturnDiscount p e (moduleCanonicalAbelParameter n)
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
    exact tiltedGapLaw_nonneg r₀ (moduleCanonicalAbelParameter n) p e hp0
      hr₀_nonneg hr₀_lt.le (moduleCanonicalAbelParameter_nonneg n)
      (moduleCanonicalAbelParameter_lt_one n).le g
  have hweight_sum : ∀ n, HasSum (weight n) 1 := by
    intro n
    exact hasSum_tiltedGapLaw_one r₀ (moduleCanonicalAbelParameter n) p e
      hp0 rfl hr₀_lt (moduleCanonicalAbelParameter_nonneg n)
      (moduleCanonicalAbelParameter_lt_one n).le
  have hweightLim : ∀ g, 0 < weightLim g := by
    intro g
    exact tiltedGapLaw_pos_at_one r₀ p e hp hr₀_lt g
  have hweightLim_sum : HasSum weightLim 1 :=
    hasSum_tiltedGapLaw_one r₀ 1 p e hp0 rfl hr₀_lt zero_le_one le_rfl
  have hdiff : ∀ n, Summable fun g ↦ |weight n g - weightLim g| := by
    intro n
    exact ((hweight_sum n).summable.sub hweightLim_sum.summable).abs
  have hsWithin : Tendsto moduleCanonicalAbelParameter atTop
      (nhdsWithin (1 : ℝ) (Set.Icc 0 1)) := by
    apply tendsto_nhdsWithin_iff.2
    exact ⟨tendsto_moduleCanonicalAbelParameter,
      Eventually.of_forall fun n ↦
        ⟨moduleCanonicalAbelParameter_nonneg n,
          (moduleCanonicalAbelParameter_lt_one n).le⟩⟩
  have hl1 : Tendsto
      (fun n ↦ ∑' g, |weight n g - weightLim g|) atTop (nhds 0) := by
    exact (tendsto_tiltedGapLaw_discreteL1_of_nonMarkerMass_lt_one
      p e hp0 hr₀_lt).comp hsWithin
  have hdiscount : ∀ n, 0 ≤ discount n := by
    intro n
    exact renewalMarkerDiscount_nonneg r₀ (moduleCanonicalAbelParameter n)
      hr₀_nonneg hr₀_lt.le (moduleCanonicalAbelParameter_nonneg n)
      (moduleCanonicalAbelParameter_lt_one n).le
  have hdiscount_lt : ∀ n, discount n < 1 := by
    intro n
    exact renewalMarkerDiscount_lt_one r₀ (moduleCanonicalAbelParameter n)
      hr₀_nonneg hr₀_lt (moduleCanonicalAbelParameter_nonneg n)
      (moduleCanonicalAbelParameter_lt_one n)
  have hdiscount_one : Tendsto discount atTop (nhds 1) :=
    tendsto_renewalMarkerDiscount_one r₀ moduleCanonicalAbelParameter
      hr₀_lt tendsto_moduleCanonicalAbelParameter
  have htuple := hq weight weightLim hweight hweight_sum hweightLim
    hweightLim_sum hdiff hl1 discount hdiscount hdiscount_lt
      hdiscount_one (1 : FreeGroup (GapWords e))
  have hqPhysical : Tendsto (fun n ↦
      realNormalizedAbelMean
        (moduleBooleanCentralReturnExactAverage op T U V left seed p)
        (moduleCanonicalAbelParameter n)) atTop (nhds (q : ℝ)) := by
    apply htuple.congr'
    exact Eventually.of_forall fun n ↦ by
      simpa [qG, step, weight, discount, moduleCentralReturnGapLaw,
        moduleCentralReturnDiscount] using
        (moduleBooleanCentralReturnNormalizedAbelMean_eq_geometricGapMoments
          op T e U V hfac K hK left seed p hp hp1
            (moduleCanonicalAbelParameter n)
            (moduleCanonicalAbelParameter_nonneg n)
            (moduleCanonicalAbelParameter_lt_one n)).symm
  obtain ⟨L, hL⟩ := exists_tendsto_moduleBooleanCentralReturnCesaro
    op T U V left seed p hp0 hp1
  have hbound : ∀ n,
      |moduleBooleanCentralReturnExactAverage op T U V left seed p n| ≤ 1 := by
    intro n
    have hn := moduleBooleanCentralReturnExactAverage_mem_Icc
      op T U V left seed p hp0 hp1 n
    rw [abs_of_nonneg hn.1]
    exact hn.2
  have hAbel := tendsto_realNormalizedAbelMean_of_tendsto_realCesaroMean
    (moduleBooleanCentralReturnExactAverage op T U V left seed p) 1 L hbound hL
  have hsBelow : Tendsto moduleCanonicalAbelParameter atTop
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) := by
    apply tendsto_nhdsWithin_iff.2
    exact ⟨tendsto_moduleCanonicalAbelParameter,
      Eventually.of_forall moduleCanonicalAbelParameter_lt_one⟩
  have hLPhysical := hAbel.comp hsBelow
  have hLq : L = (q : ℝ) := tendsto_nhds_unique hLPhysical hqPhysical
  exact hLq ▸ hL

/-- The canonical Boolean central rational mean can be chosen with its
probability bound. -/
theorem exists_rational_mem_Icc_forall_tendsto_moduleBooleanCentralReturnCesaro
    {d : ℕ} (op : (Fin d → Bool) → Bool)
    (T : C → Module.End R X) (e : C)
    (U : B →ₗ[R] X) (V : X →ₗ[R] B)
    (hfac : endoWord T [e] = U.comp V)
    (K : List C → (B ≃ₗ[R] B))
    (hK : ∀ y, (K y).toLinearMap = compressedReturn T U V y)
    (left : Fin d → Module.Dual R B) (seed : B) :
    ∃ q : ℚ, (q : ℝ) ∈ Set.Icc (0 : ℝ) 1 ∧
      ∀ (p : C → ℝ), (∀ c, 0 < p c) → (∑ c, p c = 1) →
        Tendsto (realCesaroMean
          (moduleBooleanCentralReturnExactAverage op T U V left seed p))
          atTop (nhds (q : ℝ)) := by
  obtain ⟨q, hq⟩ :=
    exists_rational_forall_tendsto_moduleBooleanCentralReturnCesaro
      op T e U V hfac K hK left seed
  let pRef : C → ℝ := uniformAlphabetWeight
  have hpRefPos : ∀ c, 0 < pRef c := fun c ↦ uniformAlphabetWeight_pos c
  have hpRef1 : ∑ c, pRef c = 1 := sum_uniformAlphabetWeight
  have hbound := moduleBooleanCentralReturnCesaroLimit_mem_Icc
    op T U V left seed pRef (fun c ↦ (hpRefPos c).le) hpRef1 (q : ℝ)
      (hq pRef hpRefPos hpRef1)
  exact ⟨q, hbound, hq⟩

end IndependentZeroBlocks
