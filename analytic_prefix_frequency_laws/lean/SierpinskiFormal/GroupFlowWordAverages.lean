import SierpinskiFormal.GroupBooleanFlow
import SierpinskiFormal.GroupFlowStationaryMeasure
import SierpinskiFormal.MatrixWordLogDensityBridge

/-!
# Word averages as Cesaro state values on Boolean group flows

The finite-law Markov operator on the right-row flow reproduces uniform IID
word averages when tested at a coordinate.  The tuple reindexing in the
proof accounts for the order in which a left group action builds a product.
-/

noncomputable section

open Filter Set Topology
open scoped BigOperators BoundedContinuousFunction

namespace IndependentZeroBlocks

variable {G A : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable [TopologicalSpace A] [DiscreteTopology A] [Fintype A] [Nonempty A]

/-- The right row indexed by `v`, as a point of the compact Boolean flow. -/
def booleanGroupFlowPoint (q : G → Bool) (v : G) : BooleanGroupRightFlow q :=
  ⟨booleanGroupRightRow q v, subset_closure ⟨v, rfl⟩⟩

@[simp] theorem booleanGroupFlowPoint_apply (q : G → Bool) (v z : G) :
    (booleanGroupFlowPoint q v).val z = q (z * v) := rfl

/-- The real indicator of the `u` coordinate on the Boolean flow. -/
def booleanGroupFlowCoordinate (q : G → Bool) (u : G) :
    C(BooleanGroupRightFlow q, ℝ) :=
  ⟨fun x ↦ boolIndicator (x.val u),
    (continuous_of_discreteTopology : Continuous (boolIndicator : Bool → ℝ)).comp
      ((continuous_apply u).comp continuous_subtype_val)⟩

@[simp] theorem booleanGroupFlowCoordinate_apply
    (q : G → Bool) (u : G) (x : BooleanGroupRightFlow q) :
    booleanGroupFlowCoordinate q u x = boolIndicator (x.val u) := rfl

/-- Acting on a row point multiplies its row index on the left. -/
@[simp] theorem smul_booleanGroupFlowPoint (q : G → Bool) (g v : G) :
    g • booleanGroupFlowPoint q v = booleanGroupFlowPoint q (g * v) := by
  apply Subtype.ext
  funext z
  simp only [booleanGroupRightFlow_smul_apply, booleanGroupFlowPoint_apply]
  rw [mul_assoc]

/-- Uniform weights on the finite alphabet. -/
def uniformAlphabetWeight (a : A) : ℝ := (Fintype.card A : ℝ)⁻¹

theorem uniformAlphabetWeight_nonneg (a : A) :
    0 ≤ uniformAlphabetWeight a := by
  simp [uniformAlphabetWeight]

theorem uniformAlphabetWeight_pos (a : A) :
    0 < uniformAlphabetWeight a := by
  simp [uniformAlphabetWeight, Fintype.card_pos]

theorem sum_uniformAlphabetWeight :
    ∑ a : A, uniformAlphabetWeight a = 1 := by
  simp [uniformAlphabetWeight]

/-- Uniform exact-word averages can be exposed by their last letter as well
as by their first letter. -/
theorem uniformIidWordAverage_succ_eq_sum_last
    (f : BoundedWordFunction A) (n : ℕ) :
    uniformIidWordAverage f (n + 1) =
      (Fintype.card A : ℝ)⁻¹ *
        ∑ a : A, uniformIidWordAverage (wordRightTranslate [a] f) n := by
  rw [uniformIidWordAverage_eq_tuple_sum]
  simp_rw [uniformIidWordAverage_eq_tuple_sum]
  rw [Fintype.sum_equiv
    (Fin.snocEquiv (fun _ : Fin (n + 1) ↦ A)).symm
    (fun x : Fin (n + 1) → A ↦ f (List.ofFn x))
    (fun ax : A × (Fin n → A) ↦
      f (List.ofFn ax.2 ++ [ax.1]))]
  · rw [Fintype.sum_prod_type]
    simp only [wordRightTranslate_apply]
    rw [pow_succ, mul_inv]
    simp_rw [Finset.mul_sum]
    ring
  · intro x
    change f (List.ofFn x) =
      f (List.ofFn (Fin.init x) ++ [x (Fin.last n)])
    rw [List.ofFn_succ']
    simp only [List.concat_eq_append]
    congr 2

/-- The bounded word observable obtained from a group predicate and two
fixed contexts. -/
def booleanGroupContextWordIndicator (q : G → Bool) (step : A → G)
    (u v : G) : BoundedWordFunction A :=
  booleanWordIndicator (fun w ↦ q (u * (w.map step).prod * v))

@[simp] theorem booleanGroupContextWordIndicator_apply
    (q : G → Bool) (step : A → G) (u v : G) (w : List A) :
    booleanGroupContextWordIndicator q step u v w =
      boolIndicator (q (u * (w.map step).prod * v)) := rfl

/-- Exact iterates of the group-action Markov operator are exact-length IID
word averages. -/
theorem iterate_groupActionAverage_coordinate_eq_uniformIidWordAverage
    (q : G → Bool) (step : A → G) (u v : G) (n : ℕ) :
    (((groupActionAverage (X := BooleanGroupRightFlow q) step
        (uniformAlphabetWeight (A := A)))^[n])
      (booleanGroupFlowCoordinate q u)) (booleanGroupFlowPoint q v) =
      uniformIidWordAverage (booleanGroupContextWordIndicator q step u v) n := by
  induction n generalizing v with
  | zero =>
      simp [uniformIidWordAverage, uniformWordExtensionAverage,
        booleanGroupContextWordIndicator_apply]
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      rw [finiteMapAverage_apply]
      simp only [uniformAlphabetWeight, groupActionContinuousMap_apply]
      rw [← Finset.mul_sum]
      rw [uniformIidWordAverage_succ_eq_sum_last]
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      change (((groupActionAverage (X := BooleanGroupRightFlow q) step
        (uniformAlphabetWeight (A := A)))^[n])
        (booleanGroupFlowCoordinate q u))
          (step a • booleanGroupFlowPoint q v) = _
      rw [smul_booleanGroupFlowPoint, ih]
      congr 1
      ext w
      simp only [wordRightTranslate_apply,
        booleanGroupContextWordIndicator_apply, List.map_append,
        List.map_singleton, List.prod_append, List.prod_singleton]
      simp [mul_assoc]

/-- Iterating pullback of a state is dual to iterating the operator on the
tested function. -/
theorem iterate_pullbackState_apply
    {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    (P : C(Y, ℝ) →L[ℝ] C(Y, ℝ)) (hP : IsMarkovOperator Y P)
    (L : PositiveNormalizedState Y) (f : C(Y, ℝ)) (n : ℕ) :
    (((pullbackState Y P hP)^[n]) L).1 f = L.1 (((P : C(Y, ℝ) → C(Y, ℝ))^[n]) f) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', pullbackState_apply, ih]
      rw [Function.iterate_succ_apply]

/-- The requested bridge: the Cesaro state started at the row `v`, tested
at coordinate `u`, is the uniform IID word Cesaro mean at horizon `n+1`. -/
theorem stateCesaro_groupActionAverage_coordinate_eq_uniformIidWordCesaro
    (q : G → Bool) (step : A → G) (u v : G) (n : ℕ) :
    (stateCesaro (BooleanGroupRightFlow q)
      (groupActionAverage (X := BooleanGroupRightFlow q) step
        (uniformAlphabetWeight (A := A)))
      (finiteMapAverage_isMarkov (BooleanGroupRightFlow q) _ _
        uniformAlphabetWeight_nonneg sum_uniformAlphabetWeight)
      (evaluationState (BooleanGroupRightFlow q) (booleanGroupFlowPoint q v)) n).1
      (booleanGroupFlowCoordinate q u) =
    uniformIidWordCesaro (booleanGroupContextWordIndicator q step u v) (n + 1) := by
  rw [stateCesaro_apply]
  unfold uniformIidWordCesaro
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [iterate_pullbackState_apply]
  change (((groupActionAverage (X := BooleanGroupRightFlow q) step
      (uniformAlphabetWeight (A := A)))^[k])
      (booleanGroupFlowCoordinate q u)) (booleanGroupFlowPoint q v) = _
  exact iterate_groupActionAverage_coordinate_eq_uniformIidWordAverage q step u v k

/-- Specialization of the compact-countable mechanism to the Boolean right
row flow.  The double-limit property supplies countability of the flow. -/
theorem exists_invariant_measure_and_finite_orbit_booleanGroupRightFlow
    [Countable G] (q : G → Bool)
    (hDLP : HasBooleanDoubleLimitProperty (booleanGroupRightRow q))
    (step : A → G) (hgenerate : Subgroup.closure (Set.range step) = ⊤)
    (v : G) :
    ∃ (L : PositiveNormalizedState (BooleanGroupRightFlow q))
      (F : Finset (BooleanGroupRightFlow q)),
      MapClusterPt L atTop
        (stateCesaro (BooleanGroupRightFlow q)
          (groupActionAverage (X := BooleanGroupRightFlow q) step
            (uniformAlphabetWeight (A := A)))
          (finiteMapAverage_isMarkov (BooleanGroupRightFlow q) _ _
            uniformAlphabetWeight_nonneg sum_uniformAlphabetWeight)
          (evaluationState (BooleanGroupRightFlow q)
            (booleanGroupFlowPoint q v))) ∧
      (∀ g : G, MeasureTheory.Measure.map
          (fun x : BooleanGroupRightFlow q ↦ g • x)
          (stateRieszMeasure (BooleanGroupRightFlow q) L) =
        stateRieszMeasure (BooleanGroupRightFlow q) L) ∧
      F.Nonempty ∧
      ∀ g : G, Set.MapsTo (fun x : BooleanGroupRightFlow q ↦ g • x)
        (F : Set (BooleanGroupRightFlow q)) F := by
  letI : Countable (BooleanGroupRightFlow q) :=
    booleanGroupRightFlow_countable q hDLP
  exact exists_invariant_finite_orbit_finset_of_compact_group_flow
    (X := BooleanGroupRightFlow q) step (uniformAlphabetWeight (A := A))
    uniformAlphabetWeight_pos sum_uniformAlphabetWeight hgenerate
    (booleanGroupFlowPoint q v)

end IndependentZeroBlocks
