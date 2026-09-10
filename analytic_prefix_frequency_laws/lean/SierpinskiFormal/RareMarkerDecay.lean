import SierpinskiFormal.MatrixBoundaryExpansion
import SierpinskiFormal.RenewalWordGenerating
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-! # Negligibility of words with fewer than two reset markers -/

noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace IndependentZeroBlocks

variable {A : Type*} [DecidableEq A]

theorem exists_last_marker (e : A) (w : List A) (he : e ∈ w) :
    ∃ y z : List A, e ∉ z ∧ w = y ++ e :: z := by
  induction w with
  | nil => simp at he
  | cons a w ih =>
      by_cases htail : e ∈ w
      · obtain ⟨y, z, hz, rfl⟩ := ih htail
        exact ⟨a :: y, z, hz, rfl⟩
      · have ha : e = a := (List.mem_cons.mp he).resolve_right htail
        subst a
        exact ⟨[], w, htail, rfl⟩

theorem mem_range_markerBoundary_iff (e : A) (w : List A) :
    w ∈ Set.range (MarkerBoundary.word e) ↔ 2 ≤ w.count e := by
  constructor
  · rintro ⟨t, rfl⟩
    simp only [MarkerBoundary.word, List.count_append, List.count_singleton_self]
    omega
  · intro hw
    induction w with
    | nil => simp at hw
    | cons a w ih =>
        by_cases ha : a = e
        · subst a
          have hm : e ∈ w := by
            have hc : 0 < w.count e := by simpa using hw
            exact List.count_pos_iff.mp hc
          obtain ⟨y, z, hz, rfl⟩ := exists_last_marker e w hm
          exact ⟨⟨[], y, z, by simp, hz⟩, by simp [MarkerBoundary.word]⟩
        · have hw' : 2 ≤ w.count e := by simpa [ha] using hw
          obtain ⟨t, ht⟩ := ih hw'
          exact ⟨⟨a :: t.left, t.middle, t.right,
            by simp [ha, Ne.symm ha, t.left_free], t.right_free⟩,
            by simp only [MarkerBoundary.word, List.cons_append] at ht ⊢; rw [ht]⟩

section Weighted
variable [Fintype A]

theorem exactLengthWordSum_cons (p : A → ℝ) (f : List A → ℝ) (N : ℕ) :
    exactLengthWordSum p f (N + 1) =
      ∑ a, p a * exactLengthWordSum p (fun w ↦ f (a :: w)) N := by
  simp_rw [exactLengthWordSum_eq_tuple_sum]
  rw [Fintype.sum_equiv (finSuccTupleEquiv N)
    (fun x : Fin (N + 1) → A ↦ wordWeight p (List.ofFn x) * f (List.ofFn x))
    (fun ax : A × (Fin N → A) ↦
      p ax.1 * (wordWeight p (List.ofFn ax.2) * f (ax.1 :: List.ofFn ax.2)))]
  · rw [Fintype.sum_prod_type]
    simp_rw [Finset.mul_sum]
  · intro x
    simp [List.ofFn_succ, finSuccTupleEquiv, wordWeight, mul_assoc]

theorem exactLengthWordSum_zero (p : A → ℝ) (f : List A → ℝ) :
    exactLengthWordSum p f 0 = f [] := by
  simp [exactLengthWordSum_eq_tuple_sum, wordWeight]

def zeroMarkerMass (p : A → ℝ) (e : A) (N : ℕ) : ℝ :=
  exactLengthWordSum p (fun w ↦ if w.count e = 0 then 1 else 0) N

def oneMarkerMass (p : A → ℝ) (e : A) (N : ℕ) : ℝ :=
  exactLengthWordSum p (fun w ↦ if w.count e = 1 then 1 else 0) N

theorem zeroMarkerMass_succ (p : A → ℝ) (e : A) (N : ℕ) :
    zeroMarkerMass p e (N + 1) =
      (∑ a ∈ Finset.univ.erase e, p a) * zeroMarkerMass p e N := by
  rw [zeroMarkerMass, exactLengthWordSum_cons]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ e)]
  have he : exactLengthWordSum p (fun w ↦ if (e :: w).count e = 0 then 1 else 0) N = 0 := by
    simp [exactLengthWordSum_eq_tuple_sum]
  rw [he, mul_zero, add_zero, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  have hae := (Finset.mem_erase.mp ha).1
  simp [zeroMarkerMass, hae, Ne.symm hae]

theorem oneMarkerMass_succ (p : A → ℝ) (e : A) (N : ℕ) :
    oneMarkerMass p e (N + 1) =
      (∑ a ∈ Finset.univ.erase e, p a) * oneMarkerMass p e N +
        p e * zeroMarkerMass p e N := by
  rw [oneMarkerMass, exactLengthWordSum_cons]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ e)]
  have he : exactLengthWordSum p (fun w ↦ if (e :: w).count e = 1 then 1 else 0) N =
      zeroMarkerMass p e N := by
    simp [zeroMarkerMass]
  rw [he, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  have hae := (Finset.mem_erase.mp ha).1
  simp [oneMarkerMass, hae, Ne.symm hae]

theorem zeroMarkerMass_eq_pow (p : A → ℝ) (e : A) (N : ℕ) :
    zeroMarkerMass p e N = (∑ a ∈ Finset.univ.erase e, p a) ^ N := by
  induction N with
  | zero => simp [zeroMarkerMass, exactLengthWordSum_zero]
  | succ N ih => rw [zeroMarkerMass_succ, ih, pow_succ']

theorem oneMarkerMass_succ_eq (p : A → ℝ) (e : A) (N : ℕ) :
    oneMarkerMass p e (N + 1) =
      (N + 1 : ℝ) * p e * (∑ a ∈ Finset.univ.erase e, p a) ^ N := by
  induction N with
  | zero =>
      rw [oneMarkerMass_succ]
      simp [oneMarkerMass, zeroMarkerMass, exactLengthWordSum_zero]
  | succ N ih =>
      rw [oneMarkerMass_succ, ih, zeroMarkerMass_eq_pow]
      simp only [Nat.cast_add, Nat.cast_one, pow_succ]
      ring

theorem rareBoundaryWordSum_eq_count_sum
    (p : A → ℝ) (f : List A → ℝ) (e : A) (N : ℕ) :
    rareBoundaryWordSum p f e N =
      exactLengthWordSum p (fun w ↦ if w.count e < 2 then f w else 0) N := by
  unfold rareBoundaryWordSum exactLengthWordSum
  apply tsum_congr
  intro w
  by_cases hlen : w.length = N
  · by_cases hc : w.count e < 2
    · have hm : w ∉ Set.range (MarkerBoundary.word e) := by
        rw [mem_range_markerBoundary_iff]; omega
      simp [hlen, hc, hm] <;> omega
    · have hm : w ∈ Set.range (MarkerBoundary.word e) := by
        rw [mem_range_markerBoundary_iff]; omega
      simp [hlen, hc, hm] <;> omega
  · simp [hlen]

theorem norm_rareBoundaryWordSum_le
    (p : A → ℝ) (hp : ∀ a, 0 ≤ p a)
    (f : List A → ℝ) (hf : ∀ w, ‖f w‖ ≤ 1) (e : A) (N : ℕ) :
    ‖rareBoundaryWordSum p f e N‖ ≤ zeroMarkerMass p e N + oneMarkerMass p e N := by
  rw [rareBoundaryWordSum_eq_count_sum, exactLengthWordSum_eq_tuple_sum]
  rw [zeroMarkerMass, oneMarkerMass]
  simp only [exactLengthWordSum_eq_tuple_sum, ← Finset.sum_add_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro x _
  let w := List.ofFn x
  have hw : 0 ≤ wordWeight p w := wordWeight_nonneg p hp w
  change ‖wordWeight p w * (if w.count e < 2 then f w else 0)‖ ≤
    wordWeight p w * (if w.count e = 0 then 1 else 0) +
      wordWeight p w * (if w.count e = 1 then 1 else 0)
  by_cases hc0 : w.count e = 0
  · simpa [hc0, norm_mul, Real.norm_eq_abs, abs_of_nonneg hw] using
      (mul_le_mul_of_nonneg_left (hf w) hw)
  · by_cases hc1 : w.count e = 1
    · simpa [hc1, norm_mul, Real.norm_eq_abs, abs_of_nonneg hw] using
        (mul_le_mul_of_nonneg_left (hf w) hw)
    · have hc : ¬ w.count e < 2 := by omega
      simp [hc, hc0, hc1]

theorem tendsto_rareBoundaryWordSum_zero
    (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1)
    (f : List A → ℝ) (hf : ∀ w, ‖f w‖ ≤ 1) (e : A) (he : 0 < p e) :
    Tendsto (rareBoundaryWordSum p f e) atTop (𝓝 0) := by
  let rho : ℝ := ∑ a ∈ Finset.univ.erase e, p a
  have hr0 : 0 ≤ rho := Finset.sum_nonneg (fun a _ ↦ hp a)
  have hr1 : rho < 1 := by
    have hs : rho + p e = 1 := by
      rw [← hp1]
      exact Finset.sum_erase_add _ _ (Finset.mem_univ e)
    linarith
  have hpow : Tendsto (fun N : ℕ ↦ rho ^ N) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  have hnpow : Tendsto (fun N : ℕ ↦ (N : ℝ) * rho ^ N) atTop (𝓝 0) :=
    tendsto_self_mul_const_pow_of_lt_one hr0 hr1
  have hz : Tendsto (zeroMarkerMass p e) atTop (𝓝 0) := by
    change Tendsto (fun N ↦ zeroMarkerMass p e N) atTop (𝓝 0)
    simpa only [zeroMarkerMass_eq_pow] using hpow
  have ho : Tendsto (oneMarkerMass p e) atTop (𝓝 0) := by
    apply (tendsto_add_atTop_iff_nat 1).mp
    have hh := (hnpow.add hpow).mul_const (p e)
    convert hh using 1
    · funext N
      rw [oneMarkerMass_succ_eq]
      ring
    · simp
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun N ↦ norm_nonneg _) (norm_rareBoundaryWordSum_le p hp f hf e)
    (by simpa using hz.add ho)

theorem tendsto_realCesaroMean_rareBoundaryWordSum_zero
    (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1)
    (f : List A → ℝ) (hf : ∀ w, ‖f w‖ ≤ 1) (e : A) (he : 0 < p e) :
    Tendsto (realCesaroMean (rareBoundaryWordSum p f e)) atTop (𝓝 0) := by
  have h := (tendsto_rareBoundaryWordSum_zero p hp hp1 f hf e he).cesaro
  unfold realCesaroMean
  simpa only [div_eq_mul_inv, mul_comm] using h

end Weighted
end IndependentZeroBlocks
