import SierpinskiFormal.RenewalWordDecomposition
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false
noncomputable section

open Filter Topology
open scoped BigOperators ENNReal

namespace IndependentZeroBlocks

section GapMass

variable {C : Type*} [Fintype C] [DecidableEq C]

/-- Words containing no distinguished marker. -/
def GapWords (e : C) := {w : List C // e ∉ w}

/-- Total one-letter mass away from the marker. -/
def nonMarkerMass (p : C → ℝ≥0∞) (e : C) : ℝ≥0∞ :=
  ∑ c, if c = e then 0 else p c

theorem tsum_wordWeight_eq_tsum_letterMass_pow (q : C → ℝ≥0∞) :
    (∑' w : List C, wordWeight q w) =
      ∑' n : ℕ, (∑ c, q c) ^ n := by
  rw [← (List.equivSigmaTuple (α := C)).symm.tsum_eq
    (fun w : List C ↦ wordWeight q w)]
  change (∑' c : Σ n, Fin n → C, wordWeight q (List.ofFn c.2)) = _
  rw [ENNReal.tsum_sigma (fun n x ↦ wordWeight q (List.ofFn x))]
  apply tsum_congr
  intro n
  rw [tsum_fintype]
  simpa [wordWeight, List.prod_ofFn] using (Fintype.sum_pow q n).symm

theorem tsum_wordWeight (q : C → ℝ≥0∞) :
    (∑' w : List C, wordWeight q w) =
      (1 - ∑ c, q c)⁻¹ := by
  rw [tsum_wordWeight_eq_tsum_letterMass_pow]
  exact ENNReal.tsum_geometric _

theorem wordWeight_eraseMarker (p : C → ℝ≥0∞) (e : C) (w : List C) :
    wordWeight (fun c ↦ if c = e then 0 else p c) w =
      if e ∈ w then 0 else wordWeight p w := by
  induction w with
  | nil => simp
  | cons a w ih =>
      by_cases hae : a = e
      · subst a
        simp
      · have hea : e ≠ a := Ne.symm hae
        by_cases hew : e ∈ w <;> simp [hae, hea, hew, ih]

theorem sum_eraseMarker (p : C → ℝ≥0∞) (e : C) :
    (∑ c, if c = e then 0 else p c) = nonMarkerMass p e := by
  rfl

theorem markerMass_add_nonMarkerMass (p : C → ℝ≥0∞) (e : C) :
    p e + nonMarkerMass p e = ∑ c, p c := by
  classical
  calc
    p e + nonMarkerMass p e =
        (∑ c, if c = e then p c else 0) +
          ∑ c, if c = e then 0 else p c := by simp [nonMarkerMass]
    _ = ∑ c, ((if c = e then p c else 0) +
          if c = e then 0 else p c) := by rw [Finset.sum_add_distrib]
    _ = ∑ c, p c := by
      apply Finset.sum_congr rfl
      intro c hc
      by_cases hce : c = e <;> simp [hce]

theorem nonMarkerMass_eq_one_sub (p : C → ℝ≥0∞) (e : C)
    (hprob : (∑ c, p c) = 1) :
    nonMarkerMass p e = 1 - p e := by
  have hle : p e ≤ 1 := by
    rw [← hprob, ← markerMass_add_nonMarkerMass p e]
    exact le_add_right le_rfl
  apply ENNReal.eq_sub_of_add_eq
    (ne_top_of_le_ne_top ENNReal.one_ne_top hle)
  rw [add_comm, markerMass_add_nonMarkerMass, hprob]

/-- The total tilted mass of all marker-free gaps is the geometric resolvent
of the nonmarker one-letter mass. -/
theorem tsum_gapWeight (p : C → ℝ≥0∞) (e : C) (s : ℝ≥0∞) :
    (∑' g : GapWords e, tiltedWordWeight s p g.1) =
      (1 - s * nonMarkerMass p e)⁻¹ := by
  change (∑' g : {w : List C // e ∉ w}, tiltedWordWeight s p g.1) = _
  rw [show (∑' g : {w : List C // e ∉ w}, tiltedWordWeight s p g.1) =
      ∑' w : List C, Set.indicator {w : List C | e ∉ w}
        (tiltedWordWeight s p) w from
    tsum_subtype {w : List C | e ∉ w} (tiltedWordWeight s p)]
  have hindicator :
      Set.indicator {w : List C | e ∉ w} (tiltedWordWeight s p) =
        wordWeight (fun c ↦ if c = e then 0 else s * p c) := by
    funext w
    rw [Set.indicator_apply]
    simp only [Set.mem_setOf_eq]
    by_cases hw : e ∉ w
    · rw [if_pos hw]
      induction w with
      | nil => simp
      | cons a w ih =>
          have hae : a ≠ e := by
            intro h
            exact hw (by simp [h])
          have hwe : e ∉ w := by
            intro h
            exact hw (by simp [h])
          have hi := ih hwe
          simp only [tiltedWordWeight, wordWeight] at hi ⊢
          simp only [List.length_cons, pow_succ, List.map_cons, List.prod_cons,
            if_neg hae]
          rw [← hi]
          ac_rfl
    · rw [if_neg hw]
      push_neg at hw
      rw [wordWeight_eraseMarker (fun c ↦ s * p c) e w, if_pos hw]
  rw [hindicator, tsum_wordWeight]
  congr 2
  calc
    (∑ c, if c = e then 0 else s * p c) =
        s * ∑ c, if c = e then 0 else p c := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro c hc
          by_cases hce : c = e <;> simp [hce]
    _ = s * nonMarkerMass p e := by rw [sum_eraseMarker]

/-- Multiplying the tilted gap mass by its geometric normalizer produces a
probability law whenever the tilted nonmarker mass is strictly below one. -/
theorem tsum_normalizedGapWeight (p : C → ℝ≥0∞) (e : C) (s : ℝ≥0∞)
    (hlt : s * nonMarkerMass p e < 1) :
    (∑' g : GapWords e,
        (1 - s * nonMarkerMass p e) * tiltedWordWeight s p g.1) = 1 := by
  rw [ENNReal.tsum_mul_left, tsum_gapWeight]
  apply ENNReal.mul_inv_cancel
  · exact ne_of_gt (tsub_pos_iff_lt.mpr hlt)
  · exact ENNReal.sub_ne_top ENNReal.one_ne_top

end GapMass

section Regrouping

variable {C G : Type*} [DecidableEq C] [Monoid G]

/-- An arbitrary nonnegative sum over finite words may be regrouped exactly by
its unique nonempty list of marker-free gaps. -/
theorem tsum_words_eq_markerGapLists (e : C) (F : List C → ℝ≥0∞) :
    ∑' w : List C, F w =
      ∑' gs : MarkerGapLists e, F ([e].intercalate gs.1) := by
  rw [← (markerGapEquiv e).symm.tsum_eq F]
  rfl

/-- The renewal-coordinate summand: one factor for each gap and one marker
factor between successive gaps.  There is no spurious identity increment:
a word with no marker has exactly one gap. -/
def markerGapListTerm (e : C) (gapWeight : List C → ℝ≥0∞)
    (markerWeight : ℝ≥0∞) (κ : List C → G) (f : G → ℝ≥0∞)
    (gs : MarkerGapLists e) : ℝ≥0∞ :=
  markerWeight ^ gs.1.tail.length *
    (gs.1.map gapWeight).prod * f ((gs.1.map κ).prod)

/-- The unnormalized `(k+1)`-fold return moment.  The fiber condition uses
the tail length, so `k=0` is exactly one gap and introduces no identity step. -/
def gapConvolutionMoment (e : C) (gapWeight : List C → ℝ≥0∞)
    (κ : List C → G) (f : G → ℝ≥0∞) (k : ℕ) : ℝ≥0∞ :=
  ∑' gs : {gs : MarkerGapLists e // gs.1.tail.length = k},
    (gs.1.1.map gapWeight).prod * f ((gs.1.1.map κ).prod)

/-- Group the renewal sum by the exact number of intervening markers. -/
theorem tsum_markerGapListTerms_eq_geometricMoments
    (e : C) (gapWeight : List C → ℝ≥0∞) (markerWeight : ℝ≥0∞)
    (κ : List C → G) (f : G → ℝ≥0∞) :
    (∑' gs : MarkerGapLists e,
        markerGapListTerm e gapWeight markerWeight κ f gs) =
      ∑' k : ℕ, markerWeight ^ k *
        gapConvolutionMoment e gapWeight κ f k := by
  rw [← ENNReal.tsum_fiberwise
    (fun gs : MarkerGapLists e ↦
      markerGapListTerm e gapWeight markerWeight κ f gs)
    (fun gs ↦ gs.1.tail.length)]
  apply tsum_congr
  intro k
  unfold gapConvolutionMoment
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro gs
  simp only [markerGapListTerm]
  have hk : gs.1.1.tail.length = k := by simpa using gs.2
  rw [hk]
  simp [mul_assoc]

/-- Exact noncommutative renewal regrouping.  The code need only factor over
canonical gaps in their original order; it is not assumed to be a monoid
homomorphism and its empty-word value is not assumed to be the identity. -/
theorem tsum_tiltedWords_eq_markerGapListTerms
    (e : C) (s : ℝ≥0∞) (p : C → ℝ≥0∞)
    (κ : List C → G) (code : List C → G) (f : G → ℝ≥0∞)
    (hcode : ∀ w, code w = ((markerGaps e w).map κ).prod) :
    (∑' w : List C, tiltedWordWeight s p w * f (code w)) =
      ∑' gs : MarkerGapLists e,
        markerGapListTerm e (tiltedWordWeight s p)
          (tiltedWordWeight s p [e]) κ f gs := by
  rw [tsum_words_eq_markerGapLists e]
  apply tsum_congr
  intro gs
  rcases hgs : gs.1 with _ | ⟨g, tail⟩
  · exact (gs.2.1 hgs).elim
  · have hinter :
        tiltedWordWeight s p ([e].intercalate (g :: tail)) =
          tiltedWordWeight s p [e] ^ tail.length *
            ((g :: tail).map (tiltedWordWeight s p)).prod :=
        tiltedWordWeight_intercalate_marker s p e g tail
    have hsplit : markerGaps e ([e].intercalate (g :: tail)) = g :: tail :=
      markerGaps_unique e ([e].intercalate (g :: tail)) (g :: tail)
        (by simpa [hgs] using gs.2.2) (by simp) rfl
    simp only [markerGapListTerm, hgs, List.tail_cons, hinter, hcode, hsplit]

/-- Exact Abel-series form before normalization: physical word length is in
`tiltedWordWeight`, while the right side is grouped by the number of return
increments. -/
theorem tsum_tiltedWords_eq_geometricReturnMoments
    (e : C) (s : ℝ≥0∞) (p : C → ℝ≥0∞)
    (κ : List C → G) (code : List C → G) (f : G → ℝ≥0∞)
    (hcode : ∀ w, code w = ((markerGaps e w).map κ).prod) :
    (∑' w : List C, tiltedWordWeight s p w * f (code w)) =
      ∑' k : ℕ, tiltedWordWeight s p [e] ^ k *
        gapConvolutionMoment e (tiltedWordWeight s p) κ f k := by
  rw [tsum_tiltedWords_eq_markerGapListTerms e s p κ code f hcode]
  exact tsum_markerGapListTerms_eq_geometricMoments e
    (tiltedWordWeight s p) (tiltedWordWeight s p [e]) κ f

/-- Specialization to the minimum-rank return code constructed in
`MinimalRankCompression`. -/
theorem tsum_tiltedWords_returnMatrix
    {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    {r : ℕ} (M : C → Matrix ι ι F) (e : C)
    (U : Matrix ι (Fin r) F) (V : Matrix (Fin r) ι F)
    (hfac : matrixWord M [e] = U * V)
    (s : ℝ≥0∞) (p : C → ℝ≥0∞)
    (f : Matrix (Fin r) (Fin r) F → ℝ≥0∞) :
    (∑' w : List C,
        tiltedWordWeight s p w * f (returnMatrix M U V w)) =
      ∑' gs : MarkerGapLists e,
        markerGapListTerm e (tiltedWordWeight s p)
          (tiltedWordWeight s p [e]) (returnMatrix M U V) f gs := by
  apply tsum_tiltedWords_eq_markerGapListTerms e s p
    (returnMatrix M U V) (returnMatrix M U V) f
  exact fun w ↦ (returnMatrix_prod_markerGaps M e U V hfac w).symm

end Regrouping

section DiscreteL1

variable {J : Type*}

/-- Total variation in the convention `sum |mu-nu|`; the probability-theory
normalization is half this value. -/
def discreteL1Distance (mu nu : J → ℝ) : ℝ :=
  ∑' j, |mu j - nu j|

/-- A reusable discrete dominated-convergence lemma: pointwise convergence of
countable laws, with one summable uniform envelope, implies total-variation
convergence. -/
theorem tendsto_discreteL1Distance_zero_of_dominated
    {I : Type*} {l : Filter I} (mu : I → J → ℝ) (nu : J → ℝ)
    (bound : J → ℝ) (hbound : Summable bound)
    (hpoint : ∀ j, Tendsto (fun i ↦ mu i j) l (𝓝 (nu j)))
    (hdom : ∀ᶠ i in l, ∀ j, |mu i j - nu j| ≤ bound j) :
    Tendsto (fun i ↦ discreteL1Distance (mu i) nu) l (𝓝 0) := by
  have hterm (j : J) :
      Tendsto (fun i ↦ |mu i j - nu j|) l (𝓝 0) := by
    have hsub : Tendsto (fun i ↦ mu i j - nu j) l (𝓝 (nu j - nu j)) :=
      (hpoint j).sub tendsto_const_nhds
    simpa [Function.comp_def] using (continuous_abs.tendsto (nu j - nu j)).comp hsub
  simpa [discreteL1Distance] using
    tendsto_tsum_of_dominated_convergence hbound hterm
      (hdom.mono fun i hi j ↦ by simpa [Real.norm_eq_abs] using hi j)

/-- Normalization is preserved by a scalar factor once the unnormalized total
mass and the reciprocal relation are known. -/
theorem tsum_normalized_countableLaw
    (mass : J → ℝ) (a : ℝ) (hmass : Summable mass)
    (hnorm : a * ∑' j, mass j = 1) :
    ∑' j, a * mass j = 1 := by
  rw [tsum_mul_left]
  exact hnorm

end DiscreteL1

section TiltedGapLaw

variable {C : Type*} [Fintype C] [DecidableEq C]

def realNonMarkerMass (p : C → ℝ) (e : C) : ℝ :=
  ∑ c, if c = e then 0 else p c

/-- The normalized return-gap formula, with `r` standing for the total
nonmarker letter mass. -/
def tiltedGapLaw (r s : ℝ) (p : C → ℝ) (e : C) (g : GapWords e) : ℝ :=
  (1 - s * r) * s ^ g.1.length * wordWeight p g.1

/-- Discount per internal marker after the physical word-length tilt has
been absorbed into the normalized gap law. -/
def renewalMarkerDiscount (r s : ℝ) : ℝ :=
  s * (1 - r) / (1 - s * r)

theorem one_sub_renewalMarkerDiscount
    (r s : ℝ) (hne : 1 - s * r ≠ 0) :
    1 - renewalMarkerDiscount r s = (1 - s) / (1 - s * r) := by
  unfold renewalMarkerDiscount
  field_simp
  ring

theorem renewalMarkerDiscount_nonneg
    (r s : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ renewalMarkerDiscount r s := by
  unfold renewalMarkerDiscount
  exact div_nonneg (mul_nonneg hs0 (sub_nonneg.mpr hr1))
    (sub_nonneg.mpr <| by
      calc
        s * r ≤ 1 * 1 := mul_le_mul hs1 hr1 hr0 zero_le_one
        _ = 1 := one_mul 1)

theorem renewalMarkerDiscount_lt_one
    (r s : ℝ) (hr0 : 0 ≤ r) (hrlt : r < 1)
    (hs0 : 0 ≤ s) (hslt : s < 1) :
    renewalMarkerDiscount r s < 1 := by
  have hden : 0 < 1 - s * r := sub_pos.mpr <| by
    exact mul_lt_one_of_nonneg_of_lt_one_right hslt.le hr0 hrlt
  apply sub_pos.mp
  rw [one_sub_renewalMarkerDiscount r s hden.ne']
  exact div_pos (sub_pos.mpr hslt) hden

theorem tendsto_renewalMarkerDiscount_one
    {I : Type*} {l : Filter I} (r : ℝ) (s : I → ℝ)
    (hrlt : r < 1) (hs : Tendsto s l (nhds 1)) :
    Tendsto (fun i ↦ renewalMarkerDiscount r (s i)) l (nhds 1) := by
  have hne : 1 - r ≠ 0 := (sub_pos.mpr hrlt).ne'
  have hc : ContinuousAt (fun t : ℝ ↦ renewalMarkerDiscount r t) 1 := by
    unfold renewalMarkerDiscount
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · simpa using hne
  have hval : renewalMarkerDiscount r 1 = 1 := by
    simp [renewalMarkerDiscount, hne]
  simpa only [Function.comp_def, hval] using hc.tendsto.comp hs

theorem realNonMarkerMass_eq_one_sub (p : C → ℝ) (e : C)
    (hprob : ∑ c, p c = 1) :
    realNonMarkerMass p e = 1 - p e := by
  unfold realNonMarkerMass
  have hsplit : p e + (∑ c, if c = e then 0 else p c) = ∑ c, p c := by
    calc
      p e + (∑ c, if c = e then 0 else p c) =
          (∑ c, if c = e then p c else 0) +
            (∑ c, if c = e then 0 else p c) := by simp
      _ = ∑ c, ((if c = e then p c else 0) +
          (if c = e then 0 else p c)) := by rw [Finset.sum_add_distrib]
      _ = ∑ c, p c := by
        apply Finset.sum_congr rfl
        intro c hc
        by_cases hce : c = e <;> simp [hce]
  rw [hprob] at hsplit
  linarith

theorem wordWeight_nonneg (p : C → ℝ) (hp : ∀ c, 0 ≤ p c) (w : List C) :
    0 ≤ wordWeight p w := by
  induction w with
  | nil => simp
  | cons a w ih => simpa using mul_nonneg (hp a) ih

theorem wordWeight_pos (p : C → ℝ) (hp : ∀ c, 0 < p c) (w : List C) :
    0 < wordWeight p w := by
  induction w with
  | nil => simp
  | cons a w ih => simpa using mul_pos (hp a) ih

theorem ofReal_wordWeight (p : C → ℝ) (hp : ∀ c, 0 ≤ p c)
    (w : List C) :
    ENNReal.ofReal (wordWeight p w) =
      wordWeight (fun c ↦ ENNReal.ofReal (p c)) w := by
  induction w with
  | nil => simp
  | cons a w ih =>
      rw [wordWeight_cons, wordWeight_cons,
        ENNReal.ofReal_mul (hp a), ih]

theorem ofReal_realNonMarkerMass (p : C → ℝ) (hp : ∀ c, 0 ≤ p c)
    (e : C) :
    ENNReal.ofReal (realNonMarkerMass p e) =
      nonMarkerMass (fun c ↦ ENNReal.ofReal (p c)) e := by
  rw [realNonMarkerMass, nonMarkerMass,
    ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro c hc
    by_cases hce : c = e <;> simp [hce, hp c]
  · intro c hc
    by_cases hce : c = e <;> simp [hce, hp c]

/-- Marker-free real word weights have the expected geometric total.  This is
the real-valued counterpart of `tsum_gapWeight`, including the summability
needed by countable Markov operators. -/
theorem hasSum_gapWordWeight_geometric
    (p : C → ℝ) (e : C) (hp : ∀ c, 0 ≤ p c)
    (hlt : realNonMarkerMass p e < 1) :
    HasSum (fun g : GapWords e ↦ wordWeight p g.1)
      (1 - realNonMarkerMass p e)⁻¹ := by
  let q : C → ℝ≥0∞ := fun c ↦ ENNReal.ofReal (p c)
  let u : GapWords e → ℝ≥0∞ := fun g ↦
    ENNReal.ofReal (wordWeight p g.1)
  have hr0 : 0 ≤ realNonMarkerMass p e := by
    unfold realNonMarkerMass
    exact Finset.sum_nonneg fun c hc ↦ by
      by_cases hce : c = e <;> simp [hce, hp c]
  have hbase : 0 < 1 - realNonMarkerMass p e := sub_pos.mpr hlt
  have hqmass : nonMarkerMass q e =
      ENNReal.ofReal (realNonMarkerMass p e) := by
    exact (ofReal_realNonMarkerMass p hp e).symm
  have hsub : 1 - ENNReal.ofReal (realNonMarkerMass p e) =
      ENNReal.ofReal (1 - realNonMarkerMass p e) := by
    rw [ENNReal.ofReal_sub 1 hr0, ENNReal.ofReal_one]
  have hE := tsum_gapWeight q e (1 : ℝ≥0∞)
  simp only [one_mul] at hE
  rw [hqmass] at hE
  have hpoint (g : GapWords e) :
      u g = tiltedWordWeight (1 : ℝ≥0∞) q g.1 := by
    change ENNReal.ofReal (wordWeight p g.1) = _
    rw [ofReal_wordWeight p hp g.1]
    simp [q, tiltedWordWeight]
  have htu : (∑' g : GapWords e, u g) =
      ∑' g : GapWords e, tiltedWordWeight (1 : ℝ≥0∞) q g.1 :=
    tsum_congr hpoint
  have hfinite : (∑' g : GapWords e, u g) ≠ ⊤ := by
    rw [htu]
    rw [hE]
    exact ENNReal.inv_ne_top.2 <| by
      rw [hsub]
      exact (ENNReal.ofReal_pos.2 hbase).ne'
  have htoReal := ENNReal.hasSum_toReal hfinite
  have htarget :
      ((∑' g : GapWords e, u g)).toReal =
        (1 - realNonMarkerMass p e)⁻¹ := by
    rw [htu]
    rw [hE, hsub,
      ENNReal.toReal_inv, ENNReal.toReal_ofReal hbase.le]
  have hsumreal : (∑' g : GapWords e, (u g).toReal) =
      (1 - realNonMarkerMass p e)⁻¹ := by
    rw [← ENNReal.tsum_toReal_eq (fun g ↦ ENNReal.ofReal_ne_top)]
    exact htarget
  rw [hsumreal] at htoReal
  simpa [u, ENNReal.toReal_ofReal, wordWeight_nonneg p hp] using htoReal

theorem summable_gapWordWeight
    (p : C → ℝ) (e : C) (hp : ∀ c, 0 ≤ p c)
    (hlt : realNonMarkerMass p e < 1) :
    Summable (fun g : GapWords e ↦ wordWeight p g.1) :=
  (hasSum_gapWordWeight_geometric p e hp hlt).summable

theorem realNonMarkerMass_mul_left (s : ℝ) (p : C → ℝ) (e : C) :
    realNonMarkerMass (fun c ↦ s * p c) e =
      s * realNonMarkerMass p e := by
  unfold realNonMarkerMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  by_cases hce : c = e <;> simp [hce]

theorem wordWeight_mul_left (s : ℝ) (p : C → ℝ) (w : List C) :
    wordWeight (fun c ↦ s * p c) w =
      s ^ w.length * wordWeight p w := by
  induction w with
  | nil => simp
  | cons a w ih =>
      simp only [wordWeight_cons, List.length_cons, pow_succ, ih]
      ring

/-- The explicit tilted gap formula is a probability law for every
`s ∈ [0,1]` when the untilted nonmarker mass is strictly below one. -/
theorem hasSum_tiltedGapLaw_one
    (r s : ℝ) (p : C → ℝ) (e : C)
    (hp : ∀ c, 0 ≤ p c) (hr : r = realNonMarkerMass p e)
    (hrlt : r < 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    HasSum (tiltedGapLaw r s p e) 1 := by
  have hsrlt : s * r < 1 := by
    rw [hr]
    have hr0 : 0 ≤ realNonMarkerMass p e := by
      unfold realNonMarkerMass
      exact Finset.sum_nonneg fun c hc ↦ by
        by_cases hce : c = e <;> simp [hce, hp c]
    exact mul_lt_one_of_nonneg_of_lt_one_right hs1 hr0 (hr ▸ hrlt)
  have hraw := hasSum_gapWordWeight_geometric
    (fun c ↦ s * p c) e (fun c ↦ mul_nonneg hs0 (hp c)) (by
      rw [realNonMarkerMass_mul_left, ← hr]
      exact hsrlt)
  have hscaled := hraw.mul_left (1 - s * r)
  have hne : 1 - s * r ≠ 0 := (sub_pos.mpr hsrlt).ne'
  convert! hscaled using 1
  · funext g
    simp only [tiltedGapLaw, wordWeight_mul_left]
    ring
  · rw [realNonMarkerMass_mul_left, ← hr]
    field_simp

theorem summable_tiltedGapLaw
    (r s : ℝ) (p : C → ℝ) (e : C)
    (hp : ∀ c, 0 ≤ p c) (hr : r = realNonMarkerMass p e)
    (hrlt : r < 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Summable (tiltedGapLaw r s p e) :=
  (hasSum_tiltedGapLaw_one r s p e hp hr hrlt hs0 hs1).summable

theorem tiltedGapLaw_nonneg
    (r s : ℝ) (p : C → ℝ) (e : C)
    (hp : ∀ c, 0 ≤ p c) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (g : GapWords e) :
    0 ≤ tiltedGapLaw r s p e g := by
  unfold tiltedGapLaw
  have hsr : s * r ≤ 1 := by
    calc
      s * r ≤ 1 * 1 := mul_le_mul hs1 hr1 hr0 zero_le_one
      _ = 1 := one_mul 1
  exact mul_nonneg
    (mul_nonneg (sub_nonneg.mpr hsr) (pow_nonneg hs0 _))
    (wordWeight_nonneg p hp g.1)

theorem tiltedGapLaw_pos_at_one
    (r : ℝ) (p : C → ℝ) (e : C)
    (hp : ∀ c, 0 < p c) (hrlt : r < 1) (g : GapWords e) :
    0 < tiltedGapLaw r 1 p e g := by
  simpa [tiltedGapLaw] using
    mul_pos (sub_pos.mpr hrlt) (wordWeight_pos p hp g.1)

theorem continuous_tiltedGapLaw (r : ℝ) (p : C → ℝ) (e : C)
    (g : GapWords e) :
    Continuous (fun s ↦ tiltedGapLaw r s p e g) := by
  unfold tiltedGapLaw
  fun_prop

/-- The length-tilted return law converges in total variation to its untilted
law.  The summable base-gap hypothesis is the exact analytic input; for a
positive IID law it follows from `tsum_gapWeight` and positive marker mass. -/
theorem tendsto_tiltedGapLaw_discreteL1
    (r : ℝ) (p : C → ℝ) (e : C)
    (hp : ∀ c, 0 ≤ p c) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hsum : Summable (fun g : GapWords e ↦ wordWeight p g.1)) :
    Tendsto (fun s ↦ discreteL1Distance
      (tiltedGapLaw r s p e) (tiltedGapLaw r 1 p e))
      (𝓝[Set.Icc 0 1] (1 : ℝ)) (𝓝 0) := by
  apply tendsto_discreteL1Distance_zero_of_dominated
    (fun s g ↦ tiltedGapLaw r s p e g) (tiltedGapLaw r 1 p e)
    (fun g ↦ 2 * wordWeight p g.1) (hsum.mul_left 2)
  · intro g
    exact (continuous_tiltedGapLaw r p e g).continuousAt.mono_left inf_le_left
  · filter_upwards [self_mem_nhdsWithin] with s hs
    intro g
    have hs0 : 0 ≤ s := hs.1
    have hs1 : s ≤ 1 := hs.2
    have hsr0 : 0 ≤ s * r := mul_nonneg hs0 hr0
    have hsr1 : s * r ≤ 1 := by
      calc
        s * r ≤ 1 * 1 := mul_le_mul hs1 hr1 hr0 zero_le_one
        _ = 1 := one_mul 1
    have ha0 : 0 ≤ 1 - s * r := sub_nonneg.mpr hsr1
    have ha1 : 1 - s * r ≤ 1 := sub_le_self 1 hsr0
    have hpow0 : 0 ≤ s ^ g.1.length := pow_nonneg hs0 _
    have hpow1 : s ^ g.1.length ≤ 1 := pow_le_one₀ hs0 hs1
    have hw0 : 0 ≤ wordWeight p g.1 := wordWeight_nonneg p hp g.1
    have hmu0 : 0 ≤ tiltedGapLaw r s p e g :=
      mul_nonneg (mul_nonneg ha0 hpow0) hw0
    have hmu1 : tiltedGapLaw r s p e g ≤ wordWeight p g.1 := by
      rw [tiltedGapLaw]
      calc
        (1 - s * r) * s ^ g.1.length * wordWeight p g.1 ≤
            1 * 1 * wordWeight p g.1 := by gcongr
        _ = wordWeight p g.1 := by simp
    have hb0 : 0 ≤ tiltedGapLaw r 1 p e g := by
      simpa [tiltedGapLaw] using mul_nonneg (sub_nonneg.mpr hr1) hw0
    have hb1 : tiltedGapLaw r 1 p e g ≤ wordWeight p g.1 := by
      simpa [tiltedGapLaw] using
        mul_le_of_le_one_left hw0 (sub_le_self 1 hr0)
    calc
      |tiltedGapLaw r s p e g - tiltedGapLaw r 1 p e g| ≤
          |tiltedGapLaw r s p e g| + |tiltedGapLaw r 1 p e g| := abs_sub _ _
      _ = tiltedGapLaw r s p e g + tiltedGapLaw r 1 p e g := by
          rw [abs_of_nonneg hmu0, abs_of_nonneg hb0]
      _ ≤ wordWeight p g.1 + wordWeight p g.1 := add_le_add hmu1 hb1
      _ = 2 * wordWeight p g.1 := by ring

/-- Concrete positive-IID specialization: the geometric gap summability
hypothesis is discharged from the strict nonmarker-mass inequality. -/
theorem tendsto_tiltedGapLaw_discreteL1_of_nonMarkerMass_lt_one
    (p : C → ℝ) (e : C) (hp : ∀ c, 0 ≤ p c)
    (hlt : realNonMarkerMass p e < 1) :
    Tendsto (fun s ↦ discreteL1Distance
      (tiltedGapLaw (realNonMarkerMass p e) s p e)
      (tiltedGapLaw (realNonMarkerMass p e) 1 p e))
      (nhdsWithin (1 : ℝ) (Set.Icc 0 1)) (nhds 0) := by
  have hr0 : 0 ≤ realNonMarkerMass p e := by
    unfold realNonMarkerMass
    exact Finset.sum_nonneg fun c hc ↦ by
      by_cases hce : c = e <;> simp [hce, hp c]
  exact tendsto_tiltedGapLaw_discreteL1
    (realNonMarkerMass p e) p e hp hr0 hlt.le
    (summable_gapWordWeight p e hp hlt)

end TiltedGapLaw

end IndependentZeroBlocks
