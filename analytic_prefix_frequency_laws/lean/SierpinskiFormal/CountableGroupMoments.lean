import SierpinskiFormal.CountableAbelGroupMean
import SierpinskiFormal.RenewalWordGenerating
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Countable group-law moments

This file expands iterates of a countably supported group-action operator as
explicit sums over finite tuples.  The tuple product is written in
chronological (left-to-right) order.  It also identifies a discounted state,
and its one-step pullback, with the corresponding Abel moment series.  The
one-step version has exactly `k + 1` increments and is the form used by the
renewal gap decomposition.
-/

noncomputable section

open Filter Set Topology
open scoped BigOperators Topology ENNReal

namespace IndependentZeroBlocks

variable {G D : Type*} [Group G]

/-- Product-law weight of a finite tuple. -/
def countableTupleWeight (weight : D → ℝ) {n : ℕ} (a : Fin n → D) : ℝ :=
  ((List.ofFn a).map weight).prod

/-- Group product of a tuple, in increasing index order. -/
def countableTupleProduct (step : D → G) {n : ℕ} (a : Fin n → D) : G :=
  ((List.ofFn a).map step).prod

@[simp] theorem countableTupleWeight_zero (weight : D → ℝ)
    (a : Fin 0 → D) : countableTupleWeight weight a = 1 := by
  simp [countableTupleWeight]

@[simp] theorem countableTupleProduct_zero (step : D → G)
    (a : Fin 0 → D) : countableTupleProduct step a = 1 := by
  simp [countableTupleProduct]

@[simp] theorem countableTupleWeight_cons (weight : D → ℝ)
    {n : ℕ} (d : D) (a : Fin n → D) :
    countableTupleWeight weight (Fin.cons d a) =
      weight d * countableTupleWeight weight a := by
  simp [countableTupleWeight]

@[simp] theorem countableTupleProduct_cons (step : D → G)
    {n : ℕ} (d : D) (a : Fin n → D) :
    countableTupleProduct step (Fin.cons d a) =
      step d * countableTupleProduct step a := by
  simp [countableTupleProduct]

theorem countableTupleWeight_nonneg
    (weight : D → ℝ) (hweight : ∀ d, 0 ≤ weight d)
    {n : ℕ} (a : Fin n → D) :
    0 ≤ countableTupleWeight weight a := by
  have hlist : ∀ l : List D, 0 ≤ (l.map weight).prod := by
    intro l
    induction l with
    | nil => simp
    | cons d l ih => simpa using mul_nonneg (hweight d) ih
  exact hlist (List.ofFn a)

/-- A probability law induces a probability law on every finite tuple
space. -/
theorem hasSum_countableTupleWeight_one
    (weight : D → ℝ) (hweight : ∀ d, 0 ≤ weight d)
    (hweight_sum : HasSum weight 1) (n : ℕ) :
    HasSum (countableTupleWeight weight : (Fin n → D) → ℝ) 1 := by
  induction n with
  | zero =>
      convert (hasSum_unique
        (fun a : Fin 0 → D ↦ countableTupleWeight weight a)) using 1
      exact countableTupleWeight_zero weight default
  | succ n ih =>
      have hprod : Summable (fun p : D × (Fin n → D) ↦
          weight p.1 * countableTupleWeight weight p.2) :=
        hweight_sum.summable.mul_of_nonneg ih.summable hweight
          (fun a ↦ countableTupleWeight_nonneg weight hweight a)
      have htsum : (∑' p : D × (Fin n → D),
          weight p.1 * countableTupleWeight weight p.2) = 1 := by
        rw [hprod.tsum_prod]
        simp_rw [tsum_mul_left]
        simp only [ih.tsum_eq, mul_one]
        exact hweight_sum.tsum_eq
      have hsprod : HasSum (fun p : D × (Fin n → D) ↦
          weight p.1 * countableTupleWeight weight p.2) 1 := by
        rw [← htsum]
        exact hprod.hasSum
      apply ((Fin.consEquiv (fun _ : Fin (n + 1) ↦ D)).hasSum_iff).mp
      convert hsprod using 1
      funext p
      change countableTupleWeight weight (Fin.cons p.1 p.2) = _
      exact countableTupleWeight_cons weight p.1 p.2

theorem summable_countableTupleWeight
    (weight : D → ℝ) (hweight : ∀ d, 0 ≤ weight d)
    (hweight_sum : HasSum weight 1) (n : ℕ) :
    Summable (countableTupleWeight weight : (Fin n → D) → ℝ) :=
  (hasSum_countableTupleWeight_one weight hweight hweight_sum n).summable

section BooleanFlow

variable [TopologicalSpace G] [DiscreteTopology G]

/-- The explicit `n`-fold convolution moment, with group increments
multiplied from left to right in tuple order. -/
def countableGroupTupleMoment
    (q : G → Bool) (step : D → G) (weight : D → ℝ)
    (u v : G) (n : ℕ) : ℝ :=
  ∑' a : Fin n → D, countableTupleWeight weight a *
    boolIndicator (q (u * countableTupleProduct step a * v))

theorem summable_countableGroupTupleMoment_term
    (q : G → Bool) (step : D → G) (weight : D → ℝ)
    (hweight : ∀ d, 0 ≤ weight d) (hweight_sum : HasSum weight 1)
    (u v : G) (n : ℕ) :
    Summable (fun a : Fin n → D ↦ countableTupleWeight weight a *
      boolIndicator (q (u * countableTupleProduct step a * v))) := by
  apply Summable.of_nonneg_of_le
    (f := countableTupleWeight weight)
    (g := fun a : Fin n → D ↦ countableTupleWeight weight a *
      boolIndicator (q (u * countableTupleProduct step a * v)))
  · intro a
    exact mul_nonneg (countableTupleWeight_nonneg weight hweight a) (by
      cases q (u * countableTupleProduct step a * v) <;> simp [boolIndicator])
  · intro a
    have hb : boolIndicator (q (u * countableTupleProduct step a * v)) ≤ 1 := by
      cases q (u * countableTupleProduct step a * v) <;> simp [boolIndicator]
    simpa using mul_le_of_le_one_right
      (countableTupleWeight_nonneg weight hweight a) hb
  · exact summable_countableTupleWeight weight hweight hweight_sum n

@[simp] theorem countableGroupTupleMoment_zero
    (q : G → Bool) (step : D → G) (weight : D → ℝ) (u v : G) :
    countableGroupTupleMoment q step weight u v 0 =
      boolIndicator (q (u * v)) := by
  unfold countableGroupTupleMoment
  rw [(hasSum_unique (fun a : Fin 0 → D ↦
    countableTupleWeight weight a *
      boolIndicator (q (u * countableTupleProduct step a * v)))).tsum_eq]
  simp

/-- Exposing the last increment gives the recursion matching iteration of
the left-action averaging operator. -/
theorem countableGroupTupleMoment_succ_eq_tsum_last
    (q : G → Bool) (step : D → G) (weight : D → ℝ)
    (hweight : ∀ d, 0 ≤ weight d) (hweight_sum : HasSum weight 1)
    (u v : G) (n : ℕ) :
    countableGroupTupleMoment q step weight u v (n + 1) =
      ∑' d, weight d *
        countableGroupTupleMoment q step weight u (step d * v) n := by
  unfold countableGroupTupleMoment
  rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) ↦ D)).tsum_eq]
  have hpair : Summable (fun p : D × (Fin n → D) ↦
      countableTupleWeight weight ((Fin.snocEquiv
        (fun _ : Fin (n + 1) ↦ D)) p) *
      boolIndicator (q (u * countableTupleProduct step ((Fin.snocEquiv
        (fun _ : Fin (n + 1) ↦ D)) p) * v))) := by
    exact (((Fin.snocEquiv (fun _ : Fin (n + 1) ↦ D)).hasSum_iff).mpr
      (summable_countableGroupTupleMoment_term q step weight hweight
        hweight_sum u v (n + 1)).hasSum).summable
  rw [hpair.tsum_prod]
  apply tsum_congr
  intro d
  calc
    (∑' a : Fin n → D,
        countableTupleWeight weight ((Fin.snocEquiv
          (fun _ : Fin (n + 1) ↦ D)) (d, a)) *
        boolIndicator (q (u * countableTupleProduct step ((Fin.snocEquiv
          (fun _ : Fin (n + 1) ↦ D)) (d, a)) * v))) =
      ∑' a : Fin n → D, weight d *
        (countableTupleWeight weight a *
          boolIndicator (q (u * countableTupleProduct step a * (step d * v)))) := by
        apply tsum_congr
        intro a
        change countableTupleWeight weight (Fin.snoc a d) *
            boolIndicator (q (u * countableTupleProduct step (Fin.snoc a d) * v)) = _
        unfold countableTupleWeight countableTupleProduct
        rw [show List.ofFn (Fin.snoc a d) = List.ofFn a ++ [d] by
          simpa [List.concat_eq_append] using (List.ofFn_succ' (Fin.snoc a d))]
        simp only [countableTupleWeight, countableTupleProduct, List.map_append,
          List.map_singleton, List.prod_append, List.prod_singleton]
        rw [show u * (((List.ofFn a).map step).prod * step d) * v =
            u * ((List.ofFn a).map step).prod * (step d * v) by
          simp only [mul_assoc]]
        ring
    _ = weight d *
        (∑' a : Fin n → D, countableTupleWeight weight a *
          boolIndicator (q (u * countableTupleProduct step a * (step d * v)))) :=
      tsum_mul_left

/-- Operator iterates at a Boolean-flow coordinate are the explicit tuple
moments above. -/
theorem iterate_countableGroupActionAverage_coordinate_eq_tupleMoment
    (q : G → Bool) (step : D → G) (weight : D → ℝ)
    (hweight : ∀ d, 0 ≤ weight d) (hweight_sum : HasSum weight 1)
    (u v : G) (n : ℕ) :
    (((countableGroupActionAverage (X := BooleanGroupRightFlow q) step weight)^[n])
      (booleanGroupFlowCoordinate q u)) (booleanGroupFlowPoint q v) =
      countableGroupTupleMoment q step weight u v n := by
  have habs : Summable fun d ↦ |weight d| := by
    simpa only [abs_of_nonneg (hweight _)] using hweight_sum.summable
  induction n generalizing v with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      rw [countableGroupActionAverage_apply
        (X := BooleanGroupRightFlow q) step weight habs]
      simp only [smul_booleanGroupFlowPoint]
      simp_rw [ih]
      exact (countableGroupTupleMoment_succ_eq_tsum_last q step weight
        hweight hweight_sum u v n).symm

/-- The countable-law discounted state is the Abel sum of its explicit
finite-tuple moments. -/
theorem discountedState_coordinate_eq_tupleMoment
    (q : G → Bool) (step : D → G) (weight : D → ℝ)
    (hweight : ∀ d, 0 ≤ weight d) (hweight_sum : HasSum weight 1)
    (u v : G) (c : ℝ) (hc : 0 ≤ c) (hclt : c < 1) :
    (discountedState (BooleanGroupRightFlow q)
      (countableGroupActionAverage (X := BooleanGroupRightFlow q) step weight)
      (countableGroupActionAverage_isMarkov (X := BooleanGroupRightFlow q)
        step weight hweight hweight_sum)
      (evaluationState (BooleanGroupRightFlow q) (booleanGroupFlowPoint q v))
      c hc hclt).1 (booleanGroupFlowCoordinate q u) =
      (1 - c) * ∑' k : ℕ, c ^ k *
        countableGroupTupleMoment q step weight u v k := by
  rw [discountedState_apply]
  congr 1
  apply tsum_congr
  intro k
  congr 1
  rw [iterate_pullbackState_apply]
  change (((countableGroupActionAverage
      (X := BooleanGroupRightFlow q) step weight)^[k])
    (booleanGroupFlowCoordinate q u)) (booleanGroupFlowPoint q v) = _
  exact iterate_countableGroupActionAverage_coordinate_eq_tupleMoment
    q step weight hweight hweight_sum u v k

/-- Pulling the discounted state back once produces the Abel series with
`k + 1` increments.  This is the indexing convention of renewal gap lists:
`k` intervening markers delimit exactly `k + 1` gaps. -/
theorem pullback_discountedState_coordinate_eq_tupleMoment_succ
    (q : G → Bool) (step : D → G) (weight : D → ℝ)
    (hweight : ∀ d, 0 ≤ weight d) (hweight_sum : HasSum weight 1)
    (u v : G) (c : ℝ) (hc : 0 ≤ c) (hclt : c < 1) :
    (pullbackState (BooleanGroupRightFlow q)
      (countableGroupActionAverage (X := BooleanGroupRightFlow q) step weight)
      (countableGroupActionAverage_isMarkov (X := BooleanGroupRightFlow q)
        step weight hweight hweight_sum)
      (discountedState (BooleanGroupRightFlow q)
        (countableGroupActionAverage (X := BooleanGroupRightFlow q) step weight)
        (countableGroupActionAverage_isMarkov (X := BooleanGroupRightFlow q)
          step weight hweight hweight_sum)
        (evaluationState (BooleanGroupRightFlow q) (booleanGroupFlowPoint q v))
        c hc hclt)).1 (booleanGroupFlowCoordinate q u) =
      (1 - c) * ∑' k : ℕ, c ^ k *
        countableGroupTupleMoment q step weight u v (k + 1) := by
  let P := countableGroupActionAverage
    (X := BooleanGroupRightFlow q) step weight
  let hP : IsMarkovOperator (BooleanGroupRightFlow q) P :=
    countableGroupActionAverage_isMarkov
      (X := BooleanGroupRightFlow q) step weight hweight hweight_sum
  let L0 : PositiveNormalizedState (BooleanGroupRightFlow q) :=
    evaluationState (BooleanGroupRightFlow q) (booleanGroupFlowPoint q v)
  change (pullbackState (BooleanGroupRightFlow q) P hP
      (discountedState (BooleanGroupRightFlow q) P hP L0 c hc hclt)).1
      (booleanGroupFlowCoordinate q u) = _
  rw [pullbackState_apply, discountedState_apply]
  congr 1
  apply tsum_congr
  intro k
  congr 1
  have hshift :
      (((pullbackState (BooleanGroupRightFlow q) P hP)^[k] L0).1
          (P (booleanGroupFlowCoordinate q u))) =
        (((pullbackState (BooleanGroupRightFlow q) P hP)^[k + 1] L0).1
          (booleanGroupFlowCoordinate q u)) := by
    change (pullbackState (BooleanGroupRightFlow q) P hP
      ((pullbackState (BooleanGroupRightFlow q) P hP)^[k] L0)).1
        (booleanGroupFlowCoordinate q u) = _
    rw [Function.iterate_succ_apply']
  rw [hshift, iterate_pullbackState_apply]
  change (((countableGroupActionAverage
      (X := BooleanGroupRightFlow q) step weight)^[k + 1])
    (booleanGroupFlowCoordinate q u)) (booleanGroupFlowPoint q v) = _
  exact iterate_countableGroupActionAverage_coordinate_eq_tupleMoment
    q step weight hweight hweight_sum u v (k + 1)

/-- Passing from the ordinary Abel series to its one-step-shifted
`(k+1)`-increment series does not change a limit as `c → 1`. -/
theorem tendsto_shifted_tupleMoment_of_tendsto_discountedState
    (q : G → Bool) (step : D → G) (weight : ℕ → D → ℝ)
    (hweight : ∀ n d, 0 ≤ weight n d)
    (hweight_sum : ∀ n, HasSum (weight n) 1)
    (u v : G) (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (hclt : ∀ n, c n < 1) (hc_one : Tendsto c atTop (𝓝 1))
    (r : ℝ)
    (hlim : Tendsto (fun n ↦
      (discountedState (BooleanGroupRightFlow q)
        (countableGroupActionAverage (X := BooleanGroupRightFlow q) step (weight n))
        (countableGroupActionAverage_isMarkov (X := BooleanGroupRightFlow q)
          step (weight n) (hweight n) (hweight_sum n))
        (evaluationState (BooleanGroupRightFlow q) (booleanGroupFlowPoint q v))
        (c n) (hc n) (hclt n)).1 (booleanGroupFlowCoordinate q u))
      atTop (𝓝 r)) :
    Tendsto (fun n ↦ (1 - c n) * ∑' k : ℕ, c n ^ k *
      countableGroupTupleMoment q step (weight n) u v (k + 1))
      atTop (𝓝 r) := by
  let Pseq : ℕ → C(BooleanGroupRightFlow q, ℝ) →L[ℝ]
      C(BooleanGroupRightFlow q, ℝ) := fun n ↦
    countableGroupActionAverage (X := BooleanGroupRightFlow q) step (weight n)
  let hPseq : ∀ n, IsMarkovOperator (BooleanGroupRightFlow q) (Pseq n) :=
    fun n ↦ countableGroupActionAverage_isMarkov
      (X := BooleanGroupRightFlow q) step (weight n) (hweight n) (hweight_sum n)
  let L0 : PositiveNormalizedState (BooleanGroupRightFlow q) :=
    evaluationState (BooleanGroupRightFlow q) (booleanGroupFlowPoint q v)
  let A : ℕ → PositiveNormalizedState (BooleanGroupRightFlow q) := fun n ↦
    discountedState (BooleanGroupRightFlow q) (Pseq n) (hPseq n) L0
      (c n) (hc n) (hclt n)
  have hdefect := tendsto_discountedState_defect
    (BooleanGroupRightFlow q) Pseq hPseq L0 c hc hclt hc_one
      (booleanGroupFlowCoordinate q u)
  have hpull : Tendsto (fun n ↦
      (pullbackState (BooleanGroupRightFlow q) (Pseq n) (hPseq n) (A n)).1
        (booleanGroupFlowCoordinate q u)) atTop (𝓝 r) := by
    have hadd := hdefect.add hlim
    convert hadd using 1
    · funext n
      dsimp [A, Pseq, hPseq, L0]
      ring
    · ring
  convert hpull using 1
  funext n
  dsimp [A, Pseq, hPseq, L0]
  exact (pullback_discountedState_coordinate_eq_tupleMoment_succ
    q step (weight n) (hweight n) (hweight_sum n) u v
      (c n) (hc n) (hclt n)).symm

/-- Rational Abel convergence in the exact `(k+1)`-increment form required
by a renewal decomposition. -/
theorem exists_rational_tendsto_countableGroupTupleAbel_succ
    [Countable G]
    (q : G → Bool)
    (hDLP : HasBooleanDoubleLimitProperty (booleanGroupRightRow q))
    (step : D → G)
    (weight : ℕ → D → ℝ) (weightLim : D → ℝ)
    (hweight : ∀ n d, 0 ≤ weight n d)
    (hweight_sum : ∀ n, HasSum (weight n) 1)
    (hweightLim : ∀ d, 0 < weightLim d)
    (hweightLim_sum : HasSum weightLim 1)
    (hgenerate : Subgroup.closure (Set.range step) = ⊤)
    (hdiff : ∀ n, Summable fun d ↦ |weight n d - weightLim d|)
    (hl1 : Tendsto (fun n ↦ ∑' d, |weight n d - weightLim d|)
      atTop (𝓝 0))
    (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (hclt : ∀ n, c n < 1)
    (hc_one : Tendsto c atTop (𝓝 1)) (z : G) :
    ∃ r : ℚ, Tendsto (fun n ↦ (1 - c n) * ∑' k : ℕ, c n ^ k *
      countableGroupTupleMoment q step (weight n) z 1 (k + 1))
      atTop (𝓝 (r : ℝ)) := by
  obtain ⟨r, hr⟩ := exists_rational_tendsto_countableGroupAbel
    q hDLP step weight weightLim hweight hweight_sum hweightLim
      hweightLim_sum hgenerate hdiff hl1 c hc hclt hc_one z
  refine ⟨r, ?_⟩
  exact tendsto_shifted_tupleMoment_of_tendsto_discountedState
    q step weight hweight hweight_sum z 1 c hc hclt hc_one (r : ℝ) hr

end BooleanFlow

section RenewalFiber

variable {C : Type*} [DecidableEq C]

/-- A marker-gap list is equivalently a nonempty list of marker-free gap
words.  This small equivalence keeps the proof carried by `GapWords` while
preserving the original list order definitionally. -/
def markerGapListsEquivNonemptyGapWords (e : C) :
    MarkerGapLists e ≃ {gs : List (GapWords e) // gs ≠ []} where
  toFun gs := ⟨gs.1.attach.map (fun g ↦
      ⟨g.1, gs.2.2 g.1 g.2⟩), by
    intro h
    have hatt : gs.1.attach = [] := List.map_eq_nil_iff.mp h
    have : gs.1 = [] := List.attach_eq_nil_iff.mp hatt
    exact gs.2.1 this⟩
  invFun gs := ⟨gs.1.map Subtype.val, by
      constructor
      · intro h
        have : gs.1 = [] := List.map_eq_nil_iff.mp h
        exact gs.2 this
      · intro g hg
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
        exact a.2⟩
  left_inv gs := by
    unfold GapWords
    apply Subtype.ext
    dsimp only
    rw [List.map_map]
    change List.map (fun g : {x // x ∈ gs.1} ↦ (g : List C)) gs.1.attach = gs.1
    exact (@List.attach_map_val (List C) (List C) gs.1 (fun x ↦ x)).trans
      (List.map_id gs.1)
  right_inv gs := by
    unfold GapWords
    apply Subtype.ext
    apply (List.map_injective_iff.mpr (fun a b h ↦ Subtype.ext h))
    dsimp
    rw [List.map_map]
    trans List.map
      (fun g : {x // x ∈ List.map Subtype.val gs.1} ↦ (g : List C))
      (List.map Subtype.val gs.1).attach
    · apply List.map_congr_left
      intro g hg
      rfl
    · calc
        List.map (fun g : {x // x ∈ List.map Subtype.val gs.1} ↦ (g : List C))
            (List.map Subtype.val gs.1).attach =
            List.map (fun x : List C ↦ x) (List.map Subtype.val gs.1) :=
          @List.attach_map_val (List C) (List C)
            (List.map Subtype.val gs.1) (fun x : List C ↦ x)
        _ = List.map Subtype.val gs.1 := by simp

/-- Canonical reindexing of a renewal fiber with `k` markers by its ordered
tuple of exactly `k + 1` gaps. -/
def markerGapFiberEquivTuple (e : C) (k : ℕ) :
    {gs : MarkerGapLists e // gs.1.tail.length = k} ≃
      (Fin (k + 1) → GapWords e) := by
  unfold MarkerGapLists GapWords
  let E := markerGapListsEquivNonemptyGapWords e
  let F : {gs : MarkerGapLists e // gs.1.tail.length = k} →
      List.Vector (GapWords e) (k + 1) := fun gs ↦
    ⟨(E gs.1).1, by
      unfold MarkerGapLists at gs
      unfold GapWords
      have hne : gs.1.1 ≠ [] := gs.1.2.1
      have hEval : (E gs.1).1 = gs.1.1.attach.map (fun g ↦
          (⟨g.1, gs.1.2.2 g.1 g.2⟩ : GapWords e)) := by
        dsimp only [E]
        rfl
      calc
        (E gs.1).1.length = gs.1.1.length := by
          rw [hEval]
          convert! (List.length_map (fun g : {x // x ∈ gs.1.1} ↦
            (⟨g.1, gs.1.2.2 g.1 g.2⟩ : GapWords e))).trans
              (List.length_attach (l := gs.1.1))
        _ = k + 1 := by
          cases h : gs.1.1 with
          | nil => exact (hne h).elim
          | cons g tail =>
              have hk := gs.2
              simp only [h, List.tail_cons] at hk
              simp [h, hk]⟩
  let Finv : List.Vector (GapWords e) (k + 1) →
      {gs : MarkerGapLists e // gs.1.tail.length = k} := fun xs ↦
    ⟨E.symm ⟨xs.1, by
        intro hnil
        have hbad : 0 = k + 1 := by simpa [hnil] using xs.2
        omega⟩, by
      unfold GapWords at xs
      have hlen : xs.1.length = k + 1 := xs.2
      have hEval : (E.symm ⟨xs.1, by
          intro hnil
          have hbad : 0 = k + 1 := by simpa [hnil] using xs.2
          omega⟩).1 = xs.1.map Subtype.val := by
        dsimp only [E]
        rfl
      rw [hEval, List.length_tail, List.length_map, hlen]
      omega⟩
  exact (Equiv.mk F Finv (by
    intro xs
    apply Subtype.ext
    change E.symm ⟨(E xs.1).1, _⟩ = xs.1
    simpa using E.symm_apply_apply xs.1) (by
    intro xs
    apply Subtype.ext
    change (E (E.symm ⟨xs.1, _⟩)).1 = xs.1
    simpa using congrArg Subtype.val (E.apply_symm_apply ⟨xs.1, _⟩))).trans
      (Equiv.vectorEquivFin (GapWords e) (k + 1))

theorem markerGapFiberEquivTuple_symm_list (e : C) (k : ℕ)
    (a : Fin (k + 1) → GapWords e) :
    ((markerGapFiberEquivTuple e k).symm a).1.1 =
      (List.ofFn a).map Subtype.val := by
  change (List.Vector.ofFn a).toList.map Subtype.val = _
  rw [List.Vector.toList_ofFn]

/-- The renewal `(k+1)`-gap fiber is exactly the usual product-law tuple
sum.  This records both the off-by-one and the noncommutative product order
used by `gapConvolutionMoment`. -/
theorem gapConvolutionMoment_eq_tupleTsum
    (e : C) (gapWeight : List C → ℝ≥0∞)
    (κ : List C → G) (f : G → ℝ≥0∞) (k : ℕ) :
    gapConvolutionMoment e gapWeight κ f k =
      ∑' a : Fin (k + 1) → GapWords e,
        ((List.ofFn a).map (fun g ↦ gapWeight g.1)).prod *
          f (((List.ofFn a).map (fun g ↦ κ g.1)).prod) := by
  unfold gapConvolutionMoment
  rw [← (markerGapFiberEquivTuple e k).symm.tsum_eq]
  apply tsum_congr
  intro a
  rw [markerGapFiberEquivTuple_symm_list]
  dsimp only [GapWords] at a ⊢
  simp only [List.map_map, Function.comp_apply]
  rfl

end RenewalFiber

end IndependentZeroBlocks
