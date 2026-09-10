import SierpinskiFormal.GroupFlowStationaryState

/-!
# Abel states for varying Markov operators

This file constructs the geometrically discounted orbit of a positive
normalized state in the norm dual.  It also isolates the compactness argument
which says that approximate stationary states for norm-convergent Markov
operators have stationary weak-star cluster points.
-/

noncomputable section

open Filter Set Topology
open scoped BigOperators Topology

namespace IndependentZeroBlocks

variable (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- The norm-dual terms in the discounted orbit of a state. -/
def discountedStateTerm (P : C(X, ℝ) →L[ℝ] C(X, ℝ))
    (hP : IsMarkovOperator X P) (L0 : PositiveNormalizedState X)
    (c : ℝ) (k : ℕ) : StrongDual ℝ C(X, ℝ) :=
  c ^ k • WeakDual.toStrongDual (((pullbackState X P hP)^[k] L0).1)

/-- The discounted orbit is absolutely summable in the norm dual. -/
theorem summable_discountedStateTerm [Nonempty X]
    (P : C(X, ℝ) →L[ℝ] C(X, ℝ)) (hP : IsMarkovOperator X P)
    (L0 : PositiveNormalizedState X) (c : ℝ) (hc : 0 ≤ c) (hclt : c < 1) :
    Summable (discountedStateTerm X P hP L0 c) := by
  apply Summable.of_norm_bounded
    (f := discountedStateTerm X P hP L0 c)
    (summable_geometric_of_lt_one hc hclt)
  intro k
  rw [show discountedStateTerm X P hP L0 c k =
    c ^ k • WeakDual.toStrongDual (((pullbackState X P hP)^[k] L0).1) from rfl]
  have hnorm := norm_smul_of_nonneg (pow_nonneg hc k)
    (WeakDual.toStrongDual (((pullbackState X P hP)^[k] L0).1))
  rw [hnorm]
  calc
    c ^ k * ‖WeakDual.toStrongDual (((pullbackState X P hP)^[k] L0).1)‖ ≤
        c ^ k * 1 := mul_le_mul_of_nonneg_left
          (positiveNormalizedStates_norm_le_one X
            (((pullbackState X P hP)^[k] L0).2)) (pow_nonneg hc k)
    _ = c ^ k := mul_one _

/-- The geometrically discounted orbit, first formed in the Banach dual. -/
def discountedStateDual (P : C(X, ℝ) →L[ℝ] C(X, ℝ))
    (hP : IsMarkovOperator X P) (L0 : PositiveNormalizedState X)
    (c : ℝ) : StrongDual ℝ C(X, ℝ) :=
  (1 - c) • ∑' k : ℕ, discountedStateTerm X P hP L0 c k

theorem tsum_discountedStateTerm_apply [Nonempty X]
    (P : C(X, ℝ) →L[ℝ] C(X, ℝ)) (hP : IsMarkovOperator X P)
    (L0 : PositiveNormalizedState X) (c : ℝ) (hc : 0 ≤ c) (hclt : c < 1)
    (f : C(X, ℝ)) :
    (∑' k : ℕ, discountedStateTerm X P hP L0 c k) f =
      ∑' k : ℕ, c ^ k * (((pullbackState X P hP)^[k] L0).1 f) := by
  let ev : (StrongDual ℝ C(X, ℝ)) →L[ℝ] ℝ :=
    ContinuousLinearMap.apply ℝ ℝ f
  change ev (∑' k : ℕ, discountedStateTerm X P hP L0 c k) = _
  rw [ev.map_tsum (summable_discountedStateTerm X P hP L0 c hc hclt)]
  rfl

/-- The Abel state `(1-c) ∑ k, c^k (P*)^k L0`. -/
def discountedState [Nonempty X]
    (P : C(X, ℝ) →L[ℝ] C(X, ℝ)) (hP : IsMarkovOperator X P)
    (L0 : PositiveNormalizedState X) (c : ℝ) (hc : 0 ≤ c) (hclt : c < 1) :
    PositiveNormalizedState X :=
  ⟨StrongDual.toWeakDual (discountedStateDual X P hP L0 c), by
    constructor
    · intro f hf
      change 0 ≤ (1 - c) *
        (∑' k : ℕ, discountedStateTerm X P hP L0 c k) f
      rw [tsum_discountedStateTerm_apply X P hP L0 c hc hclt f]
      apply mul_nonneg (sub_nonneg.mpr hclt.le)
      apply tsum_nonneg
      intro k
      change 0 ≤ c ^ k * (((pullbackState X P hP)^[k] L0).1 f)
      exact mul_nonneg (pow_nonneg hc k)
        (((pullbackState X P hP)^[k] L0).2.1 f hf)
    · change (1 - c) *
        (∑' k : ℕ, discountedStateTerm X P hP L0 c k) 1 = 1
      rw [tsum_discountedStateTerm_apply X P hP L0 c hc hclt 1]
      have hone : ∀ k : ℕ, (((pullbackState X P hP)^[k] L0).1 1) = 1 :=
        fun k ↦ positiveNormalizedStates_one X
          (((pullbackState X P hP)^[k] L0).2)
      simp_rw [hone, mul_one]
      rw [tsum_geometric_of_lt_one hc hclt]
      exact (mul_inv_cancel₀ (ne_of_gt (sub_pos.mpr hclt)))⟩

@[simp] theorem discountedState_apply [Nonempty X]
    (P : C(X, ℝ) →L[ℝ] C(X, ℝ)) (hP : IsMarkovOperator X P)
    (L0 : PositiveNormalizedState X) (c : ℝ) (hc : 0 ≤ c) (hclt : c < 1)
    (f : C(X, ℝ)) :
    (discountedState X P hP L0 c hc hclt).1 f =
      (1 - c) * ∑' k : ℕ,
        c ^ k * (((pullbackState X P hP)^[k] L0).1 f) := by
  change (1 - c) *
    (∑' k : ℕ, discountedStateTerm X P hP L0 c k) f = _
  rw [tsum_discountedStateTerm_apply X P hP L0 c hc hclt f]

/-- Scalar summability of every coordinate of the discounted orbit. -/
theorem summable_discountedState_apply [Nonempty X]
    (P : C(X, ℝ) →L[ℝ] C(X, ℝ)) (hP : IsMarkovOperator X P)
    (L0 : PositiveNormalizedState X) (c : ℝ) (hc : 0 ≤ c) (hclt : c < 1)
    (f : C(X, ℝ)) :
    Summable (fun k : ℕ ↦ c ^ k * (((pullbackState X P hP)^[k] L0).1 f)) := by
  have hs := summable_discountedStateTerm X P hP L0 c hc hclt
  exact (hs.hasSum.map (ContinuousLinearMap.apply ℝ ℝ f)
    (ContinuousLinearMap.apply ℝ ℝ f).continuous).summable

/-- The defining resolvent identity, evaluated at a continuous function. -/
theorem discountedState_resolvent_apply [Nonempty X]
    (P : C(X, ℝ) →L[ℝ] C(X, ℝ)) (hP : IsMarkovOperator X P)
    (L0 : PositiveNormalizedState X) (c : ℝ) (hc : 0 ≤ c) (hclt : c < 1)
    (f : C(X, ℝ)) :
    (discountedState X P hP L0 c hc hclt).1 f =
      (1 - c) * L0.1 f + c *
        (pullbackState X P hP
          (discountedState X P hP L0 c hc hclt)).1 f := by
  rw [discountedState_apply, pullbackState_apply, discountedState_apply]
  have hshift : ∀ k : ℕ,
      (((pullbackState X P hP)^[k] L0).1 (P f)) =
        (((pullbackState X P hP)^[k + 1] L0).1 f) := by
    intro k
    calc
      (((pullbackState X P hP)^[k] L0).1 (P f)) =
          (pullbackState X P hP ((pullbackState X P hP)^[k] L0)).1 f := rfl
      _ = (((pullbackState X P hP)^[k + 1] L0).1 f) := by
        rw [Function.iterate_succ_apply']
  simp_rw [hshift]
  have hs := summable_discountedState_apply X P hP L0 c hc hclt f
  have htail :
      (∑' k : ℕ, c ^ (k + 1) * (((pullbackState X P hP)^[k + 1] L0).1 f)) =
        c * ∑' k : ℕ, c ^ k * (((pullbackState X P hP)^[k + 1] L0).1 f) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    rw [pow_succ]
    ring
  calc
    (1 - c) * ∑' k : ℕ,
        c ^ k * (((pullbackState X P hP)^[k] L0).1 f) =
      (1 - c) * (L0.1 f + ∑' k : ℕ,
        c ^ (k + 1) * (((pullbackState X P hP)^[k + 1] L0).1 f)) := by
          rw [hs.tsum_eq_zero_add]
          simp only [pow_zero, one_mul, Function.iterate_zero_apply]
    _ = (1 - c) * L0.1 f + c * ((1 - c) * ∑' k : ℕ,
        c ^ k * (((pullbackState X P hP)^[k + 1] L0).1 f)) := by
          rw [htail]
          ring

/-- The defining resolvent identity for the Abel state. -/
theorem discountedState_resolvent [Nonempty X]
    (P : C(X, ℝ) →L[ℝ] C(X, ℝ)) (hP : IsMarkovOperator X P)
    (L0 : PositiveNormalizedState X) (c : ℝ) (hc : 0 ≤ c) (hclt : c < 1) :
    discountedState X P hP L0 c hc hclt =
      ⟨(1 - c) • L0.1 + c •
          (pullbackState X P hP (discountedState X P hP L0 c hc hclt)).1,
        by
          constructor
          · intro f hf
            exact add_nonneg (mul_nonneg (sub_nonneg.mpr hclt.le) (L0.2.1 f hf))
              (mul_nonneg hc
                ((pullbackState X P hP
                  (discountedState X P hP L0 c hc hclt)).2.1 f hf))
          · change (1 - c) * L0.1 1 + c *
                (pullbackState X P hP
                  (discountedState X P hP L0 c hc hclt)).1 1 = 1
            rw [L0.2.2, (pullbackState X P hP
              (discountedState X P hP L0 c hc hclt)).2.2]
            ring⟩ := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro f
  exact discountedState_resolvent_apply X P hP L0 c hc hclt f

/-- A normalized positive state is bounded by the uniform norm on every
coordinate. -/
theorem norm_state_apply_le [Nonempty X] (L : PositiveNormalizedState X)
    (f : C(X, ℝ)) : ‖L.1 f‖ ≤ ‖f‖ := by
  calc
    ‖L.1 f‖ ≤ ‖WeakDual.toStrongDual L.1‖ * ‖f‖ :=
      ContinuousLinearMap.le_opNorm _ f
    _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right
      (positiveNormalizedStates_norm_le_one X L.2) (norm_nonneg f)
    _ = ‖f‖ := one_mul _

/-- A weak-star cluster point of states whose fixed-operator defect tends to
zero is stationary. -/
theorem stationary_of_mapClusterPt_of_defect [Nonempty X]
    (P : C(X, ℝ) →L[ℝ] C(X, ℝ)) (hP : IsMarkovOperator X P)
    (Lseq : ℕ → PositiveNormalizedState X)
    (hdefect : ∀ f : C(X, ℝ), Tendsto (fun n ↦
      (pullbackState X P hP (Lseq n)).1 f - (Lseq n).1 f) atTop (𝓝 0))
    (L : PositiveNormalizedState X) (hcluster : MapClusterPt L atTop Lseq) :
    pullbackState X P hP L = L := by
  let F : Filter ℕ := comap Lseq (𝓝 L) ⊓ atTop
  haveI : NeBot F := neBot_inf_comap_iff_map'.mpr hcluster
  have hLF : Tendsto Lseq F (𝓝 L) :=
    tendsto_iff_comap.mpr (show F ≤ comap Lseq (𝓝 L) from inf_le_left)
  have hFtop : F ≤ atTop := inf_le_right
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro f
  have hbase : Tendsto (fun n ↦ (Lseq n).1 f) F (𝓝 (L.1 f)) :=
    (((WeakDual.eval_continuous f).comp continuous_subtype_val).tendsto L).comp hLF
  have hpull : Tendsto (fun n ↦ (pullbackState X P hP (Lseq n)).1 f) F
      (𝓝 ((pullbackState X P hP L).1 f)) :=
    (((WeakDual.eval_continuous f).comp continuous_subtype_val).tendsto _).comp
      ((continuous_pullbackState X P hP).continuousAt.tendsto.comp hLF)
  have hdiff := hpull.sub hbase
  have hzero := (hdefect f).mono_left hFtop
  exact sub_eq_zero.mp (tendsto_nhds_unique hdiff hzero)

/-- Norm convergence of the operators transfers an approximate-stationarity
defect from `Pₙ` to the limiting operator `P`. -/
theorem tendsto_fixed_operator_defect [Nonempty X]
    (P : C(X, ℝ) →L[ℝ] C(X, ℝ))
    (Pseq : ℕ → C(X, ℝ) →L[ℝ] C(X, ℝ))
    (hPseq : ∀ n, IsMarkovOperator X (Pseq n))
    (Lseq : ℕ → PositiveNormalizedState X)
    (hop : Tendsto (fun n ↦ ‖Pseq n - P‖) atTop (𝓝 0))
    (hdefect : ∀ f : C(X, ℝ), Tendsto (fun n ↦
      (pullbackState X (Pseq n) (hPseq n) (Lseq n)).1 f - (Lseq n).1 f)
        atTop (𝓝 0)) :
    ∀ f : C(X, ℝ), Tendsto (fun n ↦ (Lseq n).1 (P f) - (Lseq n).1 f)
      atTop (𝓝 0) := by
  intro f
  have herr : Tendsto (fun n ↦ (Lseq n).1 ((P - Pseq n) f)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg _)
      (Eventually.of_forall fun n ↦ by
        calc
          ‖(Lseq n).1 ((P - Pseq n) f)‖ ≤ ‖(P - Pseq n) f‖ :=
            norm_state_apply_le X (Lseq n) ((P - Pseq n) f)
          _ ≤ ‖P - Pseq n‖ * ‖f‖ := ContinuousLinearMap.le_opNorm _ f
          _ = ‖Pseq n - P‖ * ‖f‖ := by
            rw [norm_sub_rev P (Pseq n)])
    have hupper : Tendsto (fun n ↦ ‖Pseq n - P‖ * ‖f‖) atTop (𝓝 0) := by
      simpa using hop.mul_const ‖f‖
    exact hupper
  have hvary := hdefect f
  have hadd := herr.add hvary
  convert hadd using 1 <;> simp [pullbackState_apply, map_sub]

/-- Approximate stationary states for norm-convergent Markov operators have
stationary cluster points for the limiting operator. -/
theorem stationary_of_mapClusterPt_of_tendsto_operator [Nonempty X]
    (P : C(X, ℝ) →L[ℝ] C(X, ℝ)) (hP : IsMarkovOperator X P)
    (Pseq : ℕ → C(X, ℝ) →L[ℝ] C(X, ℝ))
    (hPseq : ∀ n, IsMarkovOperator X (Pseq n))
    (Lseq : ℕ → PositiveNormalizedState X)
    (hop : Tendsto (fun n ↦ ‖Pseq n - P‖) atTop (𝓝 0))
    (hdefect : ∀ f : C(X, ℝ), Tendsto (fun n ↦
      (pullbackState X (Pseq n) (hPseq n) (Lseq n)).1 f - (Lseq n).1 f)
        atTop (𝓝 0))
    (L : PositiveNormalizedState X) (hcluster : MapClusterPt L atTop Lseq) :
    pullbackState X P hP L = L := by
  apply stationary_of_mapClusterPt_of_defect X P hP Lseq _ L hcluster
  simpa [pullbackState_apply] using
    tendsto_fixed_operator_defect X P Pseq hPseq Lseq hop hdefect

/-- The Abel resolvent defect tends to zero when the discount tends to one,
even when the Markov operator varies with the index. -/
theorem tendsto_discountedState_defect [Nonempty X]
    (Pseq : ℕ → C(X, ℝ) →L[ℝ] C(X, ℝ))
    (hPseq : ∀ n, IsMarkovOperator X (Pseq n))
    (L0 : PositiveNormalizedState X)
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hclt : ∀ n, c n < 1)
    (hc_one : Tendsto c atTop (𝓝 1)) :
    ∀ f : C(X, ℝ), Tendsto (fun n ↦
      (pullbackState X (Pseq n) (hPseq n)
        (discountedState X (Pseq n) (hPseq n) L0 (c n) (hc n) (hclt n))).1 f -
      (discountedState X (Pseq n) (hPseq n) L0 (c n) (hc n) (hclt n)).1 f)
      atTop (𝓝 0) := by
  intro f
  let A : ℕ → PositiveNormalizedState X := fun n ↦
    discountedState X (Pseq n) (hPseq n) L0 (c n) (hc n) (hclt n)
  have hid : ∀ n,
      (pullbackState X (Pseq n) (hPseq n) (A n)).1 f - (A n).1 f =
        (1 - c n) *
          ((pullbackState X (Pseq n) (hPseq n) (A n)).1 f - L0.1 f) := by
    intro n
    have hr := discountedState_resolvent_apply X (Pseq n) (hPseq n) L0
      (c n) (hc n) (hclt n) f
    change (A n).1 f = (1 - c n) * L0.1 f + c n *
      (pullbackState X (Pseq n) (hPseq n) (A n)).1 f at hr
    rw [hr]
    ring
  rw [show (fun n ↦
      (pullbackState X (Pseq n) (hPseq n) (A n)).1 f - (A n).1 f) =
    (fun n ↦ (1 - c n) *
      ((pullbackState X (Pseq n) (hPseq n) (A n)).1 f - L0.1 f)) from
      funext hid]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hbound : ∀ n,
      ‖(1 - c n) *
        ((pullbackState X (Pseq n) (hPseq n) (A n)).1 f - L0.1 f)‖ ≤
          (1 - c n) * (2 * ‖f‖) := by
    intro n
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (show 0 ≤ 1 - c n from sub_nonneg.mpr (hclt n).le)]
    apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr (hclt n).le)
    rw [← Real.norm_eq_abs]
    exact (norm_sub_le _ _).trans (by
      simpa [two_mul] using add_le_add
        (norm_state_apply_le X
          (pullbackState X (Pseq n) (hPseq n) (A n)) f)
        (norm_state_apply_le X L0 f))
  apply squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg _)
    (Eventually.of_forall hbound)
  have hone_sub : Tendsto (fun n ↦ 1 - c n) atTop (𝓝 0) := by
    have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    simpa using hone.sub hc_one
  simpa using hone_sub.mul_const (2 * ‖f‖)

/-- Every weak-star cluster point of variable-operator Abel states is
stationary for the norm limit of the operators. -/
theorem discountedState_cluster_stationary [Nonempty X]
    (P : C(X, ℝ) →L[ℝ] C(X, ℝ)) (hP : IsMarkovOperator X P)
    (Pseq : ℕ → C(X, ℝ) →L[ℝ] C(X, ℝ))
    (hPseq : ∀ n, IsMarkovOperator X (Pseq n))
    (hop : Tendsto (fun n ↦ ‖Pseq n - P‖) atTop (𝓝 0))
    (L0 : PositiveNormalizedState X)
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hclt : ∀ n, c n < 1)
    (hc_one : Tendsto c atTop (𝓝 1))
    (L : PositiveNormalizedState X)
    (hcluster : MapClusterPt L atTop (fun n ↦
      discountedState X (Pseq n) (hPseq n) L0 (c n) (hc n) (hclt n))) :
    pullbackState X P hP L = L := by
  exact stationary_of_mapClusterPt_of_tendsto_operator X P hP Pseq hPseq _ hop
    (tendsto_discountedState_defect X Pseq hPseq L0 c hc hclt hc_one)
    L hcluster

/-- On the compact state space, a scalar coordinate converges if all
weak-star cluster states have the same value in that coordinate. -/
theorem tendsto_state_eval_of_forall_mapClusterPt [Nonempty X]
    (Lseq : ℕ → PositiveNormalizedState X) (f : C(X, ℝ)) (r : ℝ)
    (hcluster : ∀ L : PositiveNormalizedState X,
      MapClusterPt L atTop Lseq → L.1 f = r) :
    Tendsto (fun n ↦ (Lseq n).1 f) atTop (𝓝 r) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  by_contra hnot
  push_neg at hnot
  have hfreq : ∃ᶠ n : ℕ in atTop, ε ≤ dist ((Lseq n).1 f) r :=
    frequently_atTop.mpr fun N ↦ by
      obtain ⟨n, hn, hdist⟩ := hnot N
      exact ⟨n, hn, hdist⟩
  let S : Set ℕ := {n | ε ≤ dist ((Lseq n).1 f) r}
  let F : Filter ℕ := atTop ⊓ 𝓟 S
  haveI : NeBot F := frequently_iff_neBot.mp hfreq
  letI : CompactSpace (PositiveNormalizedState X) :=
    isCompact_iff_compactSpace.mp (isCompact_positiveNormalizedStates X)
  obtain ⟨L, _, hLF⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (PositiveNormalizedState X))).exists_mapClusterPt
      (by simp : Tendsto Lseq F (𝓟 Set.univ))
  have hLtop : MapClusterPt L atTop Lseq := hLF.mono inf_le_left
  let G : Filter ℕ := comap Lseq (𝓝 L) ⊓ F
  haveI : NeBot G := neBot_inf_comap_iff_map'.mpr hLF
  have hLG : Tendsto Lseq G (𝓝 L) :=
    tendsto_iff_comap.mpr (show G ≤ comap Lseq (𝓝 L) from inf_le_left)
  have heval : Tendsto (fun n ↦ (Lseq n).1 f) G (𝓝 (L.1 f)) :=
    (((WeakDual.eval_continuous f).comp continuous_subtype_val).tendsto L).comp hLG
  have hGS : G ≤ 𝓟 S := le_trans inf_le_right inf_le_right
  have hevent : ∀ᶠ n in G, ε ≤ dist ((Lseq n).1 f) r :=
    hGS (by simp [S])
  have hclosed : IsClosed {y : ℝ | ε ≤ dist y r} :=
    isClosed_Ici.preimage (continuous_id.dist continuous_const)
  have hlim : ε ≤ dist (L.1 f) r :=
    hclosed.mem_of_tendsto heval hevent
  rw [hcluster L hLtop, dist_self] at hlim
  exact (not_le_of_gt hε) hlim

/-- If all stationary states for the limit operator agree on `f`, then the
corresponding variable-operator Abel values converge to that common value. -/
theorem tendsto_discountedState_apply_of_stationary_value [Nonempty X]
    (P : C(X, ℝ) →L[ℝ] C(X, ℝ)) (hP : IsMarkovOperator X P)
    (Pseq : ℕ → C(X, ℝ) →L[ℝ] C(X, ℝ))
    (hPseq : ∀ n, IsMarkovOperator X (Pseq n))
    (hop : Tendsto (fun n ↦ ‖Pseq n - P‖) atTop (𝓝 0))
    (L0 : PositiveNormalizedState X)
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hclt : ∀ n, c n < 1)
    (hc_one : Tendsto c atTop (𝓝 1))
    (f : C(X, ℝ)) (r : ℝ)
    (hvalue : ∀ L : PositiveNormalizedState X,
      pullbackState X P hP L = L → L.1 f = r) :
    Tendsto (fun n ↦
      (discountedState X (Pseq n) (hPseq n) L0 (c n) (hc n) (hclt n)).1 f)
      atTop (𝓝 r) := by
  apply tendsto_state_eval_of_forall_mapClusterPt X _ f r
  intro L hcluster
  exact hvalue L (discountedState_cluster_stationary X P hP Pseq hPseq hop L0
    c hc hclt hc_one L hcluster)

end IndependentZeroBlocks
