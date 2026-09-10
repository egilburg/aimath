import SierpinskiFormal.CesaroAbelTransfer
import SierpinskiFormal.WeightedWordEnumeration
import SierpinskiFormal.RenewalWordGenerating
import SierpinskiFormal.CountableGroupMoments
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Real generating functions for weighted finite words

This file identifies the normalized Abel series of the exact-length IID word
averages with a single absolutely convergent sum over all finite words.  It is
the real-valued analytic bridge into the nonnegative renewal regrouping.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators ENNReal

namespace IndependentZeroBlocks

variable {C : Type*} [TopologicalSpace C] [DiscreteTopology C]
variable [Fintype C] [Nonempty C] [DecidableEq C]

/-- The real tilted sum over all finite words. -/
def realTiltedWordSum (s : ℝ) (p : C → ℝ) (f : List C → ℝ) : ℝ :=
  ∑' w : List C, s ^ w.length * wordWeight p w * f w

theorem weightedWordExtensionAverage_mem_Icc
    (p : C → ℝ) (hp : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1)
    (f : BoundedWordFunction C) (hf0 : ∀ w, 0 ≤ f w)
    (hf1 : ∀ w, f w ≤ 1) (n : ℕ) (z : List C) :
    weightedWordExtensionAverage p f n z ∈ Set.Icc (0 : ℝ) 1 := by
  rw [weightedWordExtensionAverage_eq_tuple_sum]
  constructor
  · exact Finset.sum_nonneg fun x hx ↦
      mul_nonneg (wordWeight_nonneg p hp (List.ofFn x)) (hf0 _)
  · calc
      (∑ x : Fin n → C,
          wordWeight p (List.ofFn x) * f (z ++ List.ofFn x)) ≤
          ∑ x : Fin n → C, wordWeight p (List.ofFn x) := by
        apply Finset.sum_le_sum
        intro x hx
        exact mul_le_of_le_one_right
          (wordWeight_nonneg p hp (List.ofFn x)) (hf1 _)
      _ = 1 := sum_tuple_wordWeight_eq_one p hp1 n

theorem summable_realTiltedWord
    (p : C → ℝ) (hp : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1)
    (f : BoundedWordFunction C) (hf0 : ∀ w, 0 ≤ f w)
    (hf1 : ∀ w, f w ≤ 1) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    Summable (fun w : List C ↦ s ^ w.length * wordWeight p w * f w) := by
  let term : (Σ n : ℕ, Fin n → C) → ℝ := fun x ↦
    s ^ x.1 * wordWeight p (List.ofFn x.2) * f (List.ofFn x.2)
  have hterm0 : ∀ x, 0 ≤ term x := by
    intro x
    exact mul_nonneg
      (mul_nonneg (pow_nonneg hs0 _) (wordWeight_nonneg p hp _)) (hf0 _)
  have hfiber (n : ℕ) :
      (∑' x : Fin n → C, term ⟨n, x⟩) =
        s ^ n * weightedWordExtensionAverage p f n [] := by
    rw [tsum_fintype, weightedWordExtensionAverage_eq_tuple_sum]
    simp_rw [List.nil_append, term, Finset.mul_sum]
    ring
  have houter : Summable (fun n : ℕ ↦ ∑' x : Fin n → C, term ⟨n, x⟩) := by
    rw [show (fun n : ℕ ↦ ∑' x : Fin n → C, term ⟨n, x⟩) =
        fun n ↦ s ^ n * weightedWordExtensionAverage p f n [] by
      funext n
      exact hfiber n]
    apply Summable.of_nonneg_of_le
    · intro n
      exact mul_nonneg (pow_nonneg hs0 _)
        (weightedWordExtensionAverage_mem_Icc p hp hp1 f hf0 hf1 n []).1
    · intro n
      exact mul_le_of_le_one_right (pow_nonneg hs0 _)
        (weightedWordExtensionAverage_mem_Icc p hp hp1 f hf0 hf1 n []).2
    · exact summable_geometric_of_norm_lt_one (by
        simpa [Real.norm_eq_abs, abs_of_nonneg hs0] using hs1)
  have hsigma : Summable term :=
    (summable_sigma_of_nonneg hterm0).2
      ⟨fun n ↦ (hasSum_fintype _).summable, houter⟩
  have hcomp :
      (term ∘ (List.equivSigmaTuple (α := C))) =
        fun w : List C ↦ s ^ w.length * wordWeight p w * f w := by
    funext w
    simp [term, Function.comp_def, List.equivSigmaTuple, List.ofFn_get]
  rw [← hcomp]
  exact ((List.equivSigmaTuple (α := C)).summable_iff).2 hsigma

/-- The normalized Abel series of exact-length weighted word averages is the
single length-tilted sum over all words. -/
theorem realNormalizedAbelMean_weightedWordExtensionAverage
    (p : C → ℝ) (hp : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1)
    (f : BoundedWordFunction C) (hf0 : ∀ w, 0 ≤ f w)
    (hf1 : ∀ w, f w ≤ 1) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    realNormalizedAbelMean
        (fun n ↦ weightedWordExtensionAverage p f n []) s =
      (1 - s) * realTiltedWordSum s p f := by
  have hword := summable_realTiltedWord p hp hp1 f hf0 hf1 s hs0 hs1
  let term : (Σ n : ℕ, Fin n → C) → ℝ := fun x ↦
    s ^ x.1 * wordWeight p (List.ofFn x.2) * f (List.ofFn x.2)
  have hsigma : Summable term := by
    apply ((List.equivSigmaTuple (α := C)).summable_iff).1
    simpa [term, Function.comp_def, List.equivSigmaTuple, List.ofFn_get] using hword
  have hregroup :
      (∑' w : List C, s ^ w.length * wordWeight p w * f w) =
        ∑' n : ℕ, s ^ n * weightedWordExtensionAverage p f n [] := by
    calc
      (∑' w : List C, s ^ w.length * wordWeight p w * f w) =
          ∑' w : List C, term (List.equivSigmaTuple w) := by
            apply tsum_congr
            intro w
            simp [term, List.equivSigmaTuple, List.ofFn_get]
      _ = ∑' x : Σ n : ℕ, Fin n → C, term x :=
        (List.equivSigmaTuple (α := C)).tsum_eq term
      _ = ∑' n : ℕ, ∑' x : Fin n → C, term ⟨n, x⟩ :=
        hsigma.tsum_sigma
      _ = ∑' n : ℕ, s ^ n * weightedWordExtensionAverage p f n [] := by
        apply tsum_congr
        intro n
        rw [tsum_fintype, weightedWordExtensionAverage_eq_tuple_sum]
        simp_rw [List.nil_append, term, Finset.mul_sum]
        ring
  unfold realNormalizedAbelMean realTiltedWordSum
  rw [hregroup]

section RenewalNormalization

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

/-- The unnormalized real length-tilted mass of a marker-free gap. -/
def realRawTiltedGapWeight (s : ℝ) (p : C → ℝ) (e : C) : GapWords e → ℝ :=
  fun g ↦ s ^ g.1.length * wordWeight p g.1

theorem realRawTiltedGapWeight_nonneg
    (s : ℝ) (p : C → ℝ) (e : C)
    (hs0 : 0 ≤ s) (hp : ∀ c, 0 ≤ p c) (g : GapWords e) :
    0 ≤ realRawTiltedGapWeight s p e g :=
  mul_nonneg (pow_nonneg hs0 _) (wordWeight_nonneg p hp _)

private theorem toReal_tiltedWordWeight_ofReal
    (s : ℝ) (p : C → ℝ) (hs0 : 0 ≤ s) (hp : ∀ c, 0 ≤ p c)
    (w : List C) :
    (tiltedWordWeight (ENNReal.ofReal s)
      (fun c ↦ ENNReal.ofReal (p c)) w).toReal =
      s ^ w.length * wordWeight p w := by
  rw [show tiltedWordWeight (ENNReal.ofReal s)
      (fun c ↦ ENNReal.ofReal (p c)) w =
      ENNReal.ofReal (s ^ w.length * wordWeight p w) by
    unfold tiltedWordWeight
    rw [← ENNReal.ofReal_pow hs0, ← ofReal_wordWeight p hp,
      ← ENNReal.ofReal_mul (pow_nonneg hs0 _)]]
  exact ENNReal.toReal_ofReal
    (mul_nonneg (pow_nonneg hs0 _) (wordWeight_nonneg p hp w))

private theorem tiltedWordWeight_ofReal_eq
    (s : ℝ) (p : C → ℝ) (hs0 : 0 ≤ s) (hp : ∀ c, 0 ≤ p c)
    (w : List C) :
    tiltedWordWeight (ENNReal.ofReal s)
      (fun c ↦ ENNReal.ofReal (p c)) w =
      ENNReal.ofReal (s ^ w.length * wordWeight p w) := by
  unfold tiltedWordWeight
  rw [← ENNReal.ofReal_pow hs0, ← ofReal_wordWeight p hp,
    ← ENNReal.ofReal_mul (pow_nonneg hs0 _)]

private theorem toReal_gapWeight_list_prod
    (s : ℝ) (p : C → ℝ) (e : C)
    (hs0 : 0 ≤ s) (hp : ∀ c, 0 ≤ p c) (l : List (GapWords e)) :
    ((l.map (fun g ↦ tiltedWordWeight (ENNReal.ofReal s)
      (fun c ↦ ENNReal.ofReal (p c)) g.1)).prod).toReal =
      (l.map (realRawTiltedGapWeight s p e)).prod := by
  induction l with
  | nil => simp
  | cons g l ih =>
      simp only [List.map_cons, List.prod_cons, ENNReal.toReal_mul,
        toReal_tiltedWordWeight_ofReal s p hs0 hp g.1, ih,
        realRawTiltedGapWeight]

private theorem ofReal_gapWeight_list_prod
    (s : ℝ) (p : C → ℝ) (e : C)
    (hs0 : 0 ≤ s) (hp : ∀ c, 0 ≤ p c) (l : List (GapWords e)) :
    (l.map (fun g ↦ tiltedWordWeight (ENNReal.ofReal s)
      (fun c ↦ ENNReal.ofReal (p c)) g.1)).prod =
      ENNReal.ofReal ((l.map (realRawTiltedGapWeight s p e)).prod) := by
  induction l with
  | nil => simp
  | cons g l ih =>
      simp only [List.map_cons, List.prod_cons,
        tiltedWordWeight_ofReal_eq s p hs0 hp g.1, ih]
      change ENNReal.ofReal (realRawTiltedGapWeight s p e g) *
          ENNReal.ofReal ((l.map (realRawTiltedGapWeight s p e)).prod) =
        ENNReal.ofReal (realRawTiltedGapWeight s p e g *
          (l.map (realRawTiltedGapWeight s p e)).prod)
      rw [← ENNReal.ofReal_mul]
      exact realRawTiltedGapWeight_nonneg s p e hs0 hp g

private theorem summable_countableTupleWeight_of_summable
    {D : Type*} (weight : D → ℝ) (hweight : ∀ d, 0 ≤ weight d)
    (hsum : Summable weight) (n : ℕ) :
    Summable (countableTupleWeight weight : (Fin n → D) → ℝ) := by
  induction n with
  | zero => exact (hasSum_fintype _).summable
  | succ n ih =>
      have hprod : Summable (fun p : D × (Fin n → D) ↦
          weight p.1 * countableTupleWeight weight p.2) :=
        hsum.mul_of_nonneg ih hweight
          (fun a ↦ countableTupleWeight_nonneg weight hweight a)
      apply ((Fin.consEquiv (fun _ : Fin (n + 1) ↦ D)).summable_iff).1
      have heq :
          countableTupleWeight weight ∘
              (Fin.consEquiv (fun _ : Fin (n + 1) ↦ D)) =
            fun p : D × (Fin n → D) ↦
              weight p.1 * countableTupleWeight weight p.2 := by
        funext p
        exact countableTupleWeight_cons weight p.1 p.2
      rw [heq]
      exact hprod

private theorem summable_countableGroupTupleMoment_term_of_summable
    {D : Type*} (q : G → Bool) (step : D → G) (weight : D → ℝ)
    (hweight : ∀ d, 0 ≤ weight d) (hsum : Summable weight)
    (n : ℕ) :
    Summable (fun a : Fin n → D ↦ countableTupleWeight weight a *
      boolIndicator (q (countableTupleProduct step a))) := by
  apply Summable.of_nonneg_of_le
      (f := countableTupleWeight weight)
  · intro a
    exact mul_nonneg (countableTupleWeight_nonneg weight hweight a) (by
      cases q (countableTupleProduct step a) <;> simp [boolIndicator])
  · intro a
    apply mul_le_of_le_one_right
      (countableTupleWeight_nonneg weight hweight a)
    cases q (countableTupleProduct step a) <;> simp [boolIndicator]
  · exact summable_countableTupleWeight_of_summable weight hweight hsum n

/-- Real form of the exact noncommutative renewal regrouping.  The term with
index `k` contains exactly `k+1` marker-free gaps, in chronological order. -/
theorem realTiltedWordSum_eq_geometricGapMoments
    (e : C) (s : ℝ) (p : C → ℝ)
    (hp : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1)
    (hs0 : 0 ≤ s) (hs1 : s < 1)
    (κ : List C → G) (code : List C → G) (q : G → Bool)
    (hcode : ∀ w, code w = ((markerGaps e w).map κ).prod) :
    realTiltedWordSum s p (fun w ↦ boolIndicator (q (code w))) =
      ∑' k : ℕ, (s * p e) ^ k *
        countableGroupTupleMoment q (fun g : GapWords e ↦ κ g.1)
          (realRawTiltedGapWeight s p e) 1 1 (k + 1) := by
  let pE : C → ℝ≥0∞ := fun c ↦ ENNReal.ofReal (p c)
  let fE : G → ℝ≥0∞ := fun g ↦ ENNReal.ofReal (boolIndicator (q g))
  have hbool (g : G) : 0 ≤ boolIndicator (q g) := by
    cases hq : q g <;> simp [boolIndicator, hq]
  have hENN := tsum_tiltedWords_eq_geometricReturnMoments
    e (ENNReal.ofReal s) pE κ code fE hcode
  have hleft :
      ((∑' w : List C,
        tiltedWordWeight (ENNReal.ofReal s) pE w * fE (code w))).toReal =
        realTiltedWordSum s p (fun w ↦ boolIndicator (q (code w))) := by
    rw [ENNReal.tsum_toReal_eq]
    · apply tsum_congr
      intro w
      rw [ENNReal.toReal_mul]
      simp only [pE, fE]
      rw [toReal_tiltedWordWeight_ofReal s p hs0 hp w]
      rw [ENNReal.toReal_ofReal (hbool (code w))]
    · intro w
      exact ENNReal.mul_ne_top
        (by rw [tiltedWordWeight_ofReal_eq s p hs0 hp w]
            exact ENNReal.ofReal_ne_top)
        ENNReal.ofReal_ne_top
  have hr0 : 0 ≤ realNonMarkerMass p e := by
    unfold realNonMarkerMass
    exact Finset.sum_nonneg fun c hc ↦ by
      by_cases hce : c = e <;> simp [hce, hp c]
  have hr1 : realNonMarkerMass p e ≤ 1 := by
    rw [realNonMarkerMass_eq_one_sub p e hp1]
    exact sub_le_self 1 (hp e)
  have hsrlt : s * realNonMarkerMass p e < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right hs0 hr1) hs1
  have hrawSummable : Summable (realRawTiltedGapWeight s p e) := by
    have h := summable_gapWordWeight (fun c ↦ s * p c) e
      (fun c ↦ mul_nonneg hs0 (hp c)) (by
        rw [realNonMarkerMass_mul_left]
        exact hsrlt)
    change Summable (fun g : GapWords e ↦ s ^ g.1.length * wordWeight p g.1)
    simpa only [wordWeight_mul_left] using h
  have hraw0 : ∀ g, 0 ≤ realRawTiltedGapWeight s p e g :=
    realRawTiltedGapWeight_nonneg s p e hs0 hp
  have hmomentENN (k : ℕ) :
      gapConvolutionMoment e
          (tiltedWordWeight (ENNReal.ofReal s) pE) κ fE k =
        ENNReal.ofReal
          (countableGroupTupleMoment q (fun g : GapWords e ↦ κ g.1)
            (realRawTiltedGapWeight s p e) 1 1 (k + 1)) := by
    rw [gapConvolutionMoment_eq_tupleTsum]
    unfold countableGroupTupleMoment
    rw [ENNReal.ofReal_tsum_of_nonneg]
    · apply tsum_congr
      intro a
      rw [ofReal_gapWeight_list_prod s p e hs0 hp (List.ofFn a)]
      simp only [pE, fE, countableTupleWeight, countableTupleProduct]
      rw [← ENNReal.ofReal_mul]
      · congr 2
        simp
      · exact countableTupleWeight_nonneg
          (realRawTiltedGapWeight s p e) hraw0 a
    · intro a
      exact mul_nonneg
        (countableTupleWeight_nonneg
          (realRawTiltedGapWeight s p e) hraw0 a) (hbool _)
    · simpa using
        (summable_countableGroupTupleMoment_term_of_summable q
          (fun g : GapWords e ↦ κ g.1) (realRawTiltedGapWeight s p e)
          hraw0 hrawSummable (k + 1))
  have hmoment (k : ℕ) :
      (gapConvolutionMoment e
        (tiltedWordWeight (ENNReal.ofReal s) pE) κ fE k).toReal =
        countableGroupTupleMoment q (fun g : GapWords e ↦ κ g.1)
          (realRawTiltedGapWeight s p e) 1 1 (k + 1) := by
    rw [hmomentENN k]
    apply ENNReal.toReal_ofReal
    exact tsum_nonneg fun a ↦ mul_nonneg
      (countableTupleWeight_nonneg
        (realRawTiltedGapWeight s p e) hraw0 a) (hbool _)
  have hright :
      ((∑' k : ℕ, tiltedWordWeight (ENNReal.ofReal s) pE [e] ^ k *
        gapConvolutionMoment e
          (tiltedWordWeight (ENNReal.ofReal s) pE) κ fE k)).toReal =
        ∑' k : ℕ, (s * p e) ^ k *
          countableGroupTupleMoment q (fun g : GapWords e ↦ κ g.1)
            (realRawTiltedGapWeight s p e) 1 1 (k + 1) := by
    rw [ENNReal.tsum_toReal_eq]
    · apply tsum_congr
      intro k
      rw [ENNReal.toReal_mul, ENNReal.toReal_pow, hmoment k]
      congr 2
      simpa [pE] using
        toReal_tiltedWordWeight_ofReal s p hs0 hp [e]
    · intro k
      apply ENNReal.mul_ne_top
      · exact ENNReal.pow_ne_top (by
          rw [tiltedWordWeight_ofReal_eq s p hs0 hp [e]]
          exact ENNReal.ofReal_ne_top)
      · rw [hmomentENN k]
        exact ENNReal.ofReal_ne_top
  rw [← hleft, ← hright]
  exact congrArg ENNReal.toReal hENN

private theorem list_prod_map_mul_left
    {D : Type*} (a : ℝ) (weight : D → ℝ) (l : List D) :
    (l.map (fun d ↦ a * weight d)).prod =
      a ^ l.length * (l.map weight).prod := by
  induction l with
  | nil => simp
  | cons d l ih =>
      simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ, ih]
      ring

private theorem countableGroupTupleMoment_tiltedGapLaw
    (e : C) (r s : ℝ) (p : C → ℝ) (q : G → Bool)
    (κ : List C → G) (n : ℕ) :
    countableGroupTupleMoment q (fun g : GapWords e ↦ κ g.1)
        (tiltedGapLaw r s p e) 1 1 n =
      (1 - s * r) ^ n *
        countableGroupTupleMoment q (fun g : GapWords e ↦ κ g.1)
          (realRawTiltedGapWeight s p e) 1 1 n := by
  unfold countableGroupTupleMoment
  rw [← tsum_mul_left]
  apply tsum_congr
  intro x
  simp only [countableTupleWeight]
  have hweight : tiltedGapLaw r s p e =
      fun g ↦ (1 - s * r) * realRawTiltedGapWeight s p e g := by
    funext g
    simp [tiltedGapLaw, realRawTiltedGapWeight, mul_assoc]
  rw [hweight]
  rw [list_prod_map_mul_left]
  rw [List.length_ofFn]
  ring

/-- Fully normalized real renewal formula.  Physical word length appears on
the left, while the right is a geometric Abel series in the number of return
gaps, using the normalized tilted gap probability law. -/
theorem realNormalizedAbelMean_eq_geometricGapMoments
    (e : C) (r s : ℝ) (p : C → ℝ)
    (hp : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1)
    (hr : r = realNonMarkerMass p e) (hrlt : r < 1)
    (hs0 : 0 ≤ s) (hs1 : s < 1)
    (κ : List C → G) (code : List C → G) (q : G → Bool)
    (hcode : ∀ w, code w = ((markerGaps e w).map κ).prod) :
    realNormalizedAbelMean
        (fun n ↦ weightedWordExtensionAverage p
          (booleanWordIndicator (fun w ↦ q (code w))) n []) s =
      (1 - renewalMarkerDiscount r s) *
        ∑' k : ℕ, renewalMarkerDiscount r s ^ k *
          countableGroupTupleMoment q (fun g : GapWords e ↦ κ g.1)
            (tiltedGapLaw r s p e) 1 1 (k + 1) := by
  have hbool0 (w : List C) :
      0 ≤ booleanWordIndicator (fun v ↦ q (code v)) w := by
    simp only [booleanWordIndicator_apply]
    cases hq : q (code w) <;> simp [boolIndicator, hq]
  have hbool1 (w : List C) :
      booleanWordIndicator (fun v ↦ q (code v)) w ≤ 1 := by
    simp only [booleanWordIndicator_apply]
    cases hq : q (code w) <;> simp [boolIndicator, hq]
  rw [realNormalizedAbelMean_weightedWordExtensionAverage
    p hp hp1 (booleanWordIndicator (fun w ↦ q (code w)))
      hbool0 hbool1 s hs0 hs1]
  change (1 - s) *
      realTiltedWordSum s p (fun w ↦ boolIndicator (q (code w))) = _
  rw [realTiltedWordSum_eq_geometricGapMoments
    e s p hp hp1 hs0 hs1 κ code q hcode]
  have hr0 : 0 ≤ r := by
    rw [hr]
    unfold realNonMarkerMass
    exact Finset.sum_nonneg fun c hc ↦ by
      by_cases hce : c = e <;> simp [hce, hp c]
  have hpmarker : p e = 1 - r := by
    rw [hr, realNonMarkerMass_eq_one_sub p e hp1]
    ring
  have hsrlt : s * r < 1 :=
    mul_lt_one_of_nonneg_of_lt_one_right hs1.le hr0 hrlt
  have hden : 1 - s * r ≠ 0 := (sub_pos.mpr hsrlt).ne'
  have hcden : renewalMarkerDiscount r s * (1 - s * r) = s * p e := by
    rw [hpmarker]
    unfold renewalMarkerDiscount
    field_simp
  have honeden :
      (1 - renewalMarkerDiscount r s) * (1 - s * r) = 1 - s := by
    rw [one_sub_renewalMarkerDiscount r s hden]
    field_simp
  rw [← tsum_mul_left, ← tsum_mul_left]
  apply tsum_congr
  intro k
  rw [countableGroupTupleMoment_tiltedGapLaw e r s p q κ (k + 1)]
  calc
    (1 - s) * ((s * p e) ^ k *
        countableGroupTupleMoment q (fun g : GapWords e ↦ κ g.1)
          (realRawTiltedGapWeight s p e) 1 1 (k + 1)) =
      (1 - renewalMarkerDiscount r s) *
        (renewalMarkerDiscount r s ^ k *
          ((1 - s * r) ^ (k + 1) *
            countableGroupTupleMoment q (fun g : GapWords e ↦ κ g.1)
              (realRawTiltedGapWeight s p e) 1 1 (k + 1))) := by
        rw [pow_succ]
        have hpow : renewalMarkerDiscount r s ^ k * (1 - s * r) ^ k =
            (s * p e) ^ k := by rw [← mul_pow, hcden]
        symm
        calc
          (1 - renewalMarkerDiscount r s) *
              (renewalMarkerDiscount r s ^ k *
                ((1 - s * r) ^ k * (1 - s * r) *
                  countableGroupTupleMoment q
                    (fun g : GapWords e ↦ κ g.1)
                    (realRawTiltedGapWeight s p e) 1 1 (k + 1))) =
            ((1 - renewalMarkerDiscount r s) * (1 - s * r)) *
              ((renewalMarkerDiscount r s ^ k * (1 - s * r) ^ k) *
                countableGroupTupleMoment q
                  (fun g : GapWords e ↦ κ g.1)
                  (realRawTiltedGapWeight s p e) 1 1 (k + 1)) := by ring
          _ = (1 - s) * ((s * p e) ^ k *
                countableGroupTupleMoment q
                  (fun g : GapWords e ↦ κ g.1)
                  (realRawTiltedGapWeight s p e) 1 1 (k + 1)) := by
            rw [honeden, hpow]

end RenewalNormalization

end IndependentZeroBlocks
