import SierpinskiFormal.ModuleBooleanReturnMean

/-! # A common physical mean under every completed return translation

The same rational mean controls all left translations of the compressed
return action. This is the algebraic invariance needed after a fixed observed
prefix in the full-law conditional-average argument.
-/

noncomputable section
open Filter Set Topology
open scoped BigOperators
namespace IndependentZeroBlocks

variable {R C X B : Type*} [CommRing R]
  [AddCommGroup X] [Module R X] [AddCommGroup B] [Module R B]
  [IsNoetherian R X] [IsNoetherian R (Module.Dual R X)]
  [IsNoetherian R B] [IsNoetherian R (Module.Dual R B)]
  [Fintype C] [Nonempty C] [DecidableEq C]
  [TopologicalSpace C] [DiscreteTopology C]

/-- Translate all observation rows by the same completed return. -/
def moduleTranslatedReturnLeft {d : ℕ}
    (K : List C → (B ≃ₗ[R] B)) (e : C)
    (left : Fin d → Module.Dual R B) (z : FreeGroup (GapWords e)) :
    Fin d → Module.Dual R B :=
  fun j ↦ (left j).comp
    (moduleReturnFreeGroupAction (fun g : GapWords e ↦ K g.1) z).toLinearMap

@[simp] theorem moduleTranslatedReturnGroup_predicate {d : ℕ}
    (op : (Fin d → Bool) → Bool) (K : List C → (B ≃ₗ[R] B)) (e : C)
    (left : Fin d → Module.Dual R B) (seed : B)
    (z x : FreeGroup (GapWords e)) :
    moduleBooleanCentralReturnGroupPredicate op K e
      (moduleTranslatedReturnLeft K e left z) seed x =
    moduleBooleanCentralReturnGroupPredicate op K e left seed (z * x) := by
  simp [moduleBooleanCentralReturnGroupPredicate, moduleCentralReturnGroupPredicate,
    moduleReturnGroupPredicate, moduleTranslatedReturnLeft, map_mul,
    LinearEquiv.mul_apply]

@[simp] theorem moduleTranslatedReturnGroup_moment {d : ℕ}
    (op : (Fin d → Bool) → Bool) (K : List C → (B ≃ₗ[R] B)) (e : C)
    (left : Fin d → Module.Dual R B) (seed : B)
    (z : FreeGroup (GapWords e)) (weight : GapWords e → ℝ) (n : ℕ) :
    countableGroupTupleMoment
      (moduleBooleanCentralReturnGroupPredicate op K e
        (moduleTranslatedReturnLeft K e left z) seed)
      FreeGroup.of weight 1 1 n =
    countableGroupTupleMoment (moduleBooleanCentralReturnGroupPredicate op K e left seed)
      FreeGroup.of weight z 1 n := by
  simp [countableGroupTupleMoment]

/-- One rational value works for every translated boundary row and every
positive law. The translation is quantified after the common value. -/
theorem exists_rational_forall_translated_moduleBooleanCentralReturnCesaro
    {d : ℕ} (op : (Fin d → Bool) → Bool)
    (T : C → Module.End R X) (e : C)
    (U : B →ₗ[R] X) (V : X →ₗ[R] B)
    (hfac : endoWord T [e] = U.comp V)
    (K : List C → (B ≃ₗ[R] B))
    (hK : ∀ y, (K y).toLinearMap = compressedReturn T U V y)
    (left : Fin d → Module.Dual R B) (seed : B) :
    ∃ q : ℚ, ∀ (z : FreeGroup (GapWords e)) (p : C → ℝ), (∀ c, 0 < p c) → (∑ c, p c = 1) →
      Tendsto (realCesaroMean
        (moduleBooleanCentralReturnExactAverage op T U V
          (moduleTranslatedReturnLeft K e left z) seed p))
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
  intro z p hp hp1
  let leftZ := moduleTranslatedReturnLeft K e left z
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
      hdiscount_one z
  have hqPhysical : Tendsto (fun n ↦
      realNormalizedAbelMean
        (moduleBooleanCentralReturnExactAverage op T U V leftZ seed p)
        (moduleCanonicalAbelParameter n)) atTop (nhds (q : ℝ)) := by
    apply htuple.congr'
    exact Eventually.of_forall fun n ↦ by
      simpa [qG, step, weight, discount, moduleCentralReturnGapLaw,
        moduleCentralReturnDiscount, leftZ, moduleTranslatedReturnGroup_moment] using
        (moduleBooleanCentralReturnNormalizedAbelMean_eq_geometricGapMoments
          op T e U V hfac K hK leftZ seed p hp hp1
            (moduleCanonicalAbelParameter n)
            (moduleCanonicalAbelParameter_nonneg n)
            (moduleCanonicalAbelParameter_lt_one n)).symm
  obtain ⟨L, hL⟩ := exists_tendsto_moduleBooleanCentralReturnCesaro
    op T U V leftZ seed p hp0 hp1
  have hbound : ∀ n,
      |moduleBooleanCentralReturnExactAverage op T U V leftZ seed p n| ≤ 1 := by
    intro n
    have hn := moduleBooleanCentralReturnExactAverage_mem_Icc
      op T U V leftZ seed p hp0 hp1 n
    rw [abs_of_nonneg hn.1]
    exact hn.2
  have hAbel := tendsto_realNormalizedAbelMean_of_tendsto_realCesaroMean
    (moduleBooleanCentralReturnExactAverage op T U V leftZ seed p) 1 L hbound hL
  have hsBelow : Tendsto moduleCanonicalAbelParameter atTop
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) := by
    apply tendsto_nhdsWithin_iff.2
    exact ⟨tendsto_moduleCanonicalAbelParameter,
      Eventually.of_forall moduleCanonicalAbelParameter_lt_one⟩
  have hLPhysical := hAbel.comp hsBelow
  have hLq : L = (q : ℝ) := tendsto_nhds_unique hLPhysical hqPhysical
  exact hLq ▸ hL


end IndependentZeroBlocks
