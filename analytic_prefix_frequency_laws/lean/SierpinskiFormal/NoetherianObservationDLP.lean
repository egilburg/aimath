import SierpinskiFormal.BooleanDoubleLimitClosure
import SierpinskiFormal.GroupBooleanTranslations
import SierpinskiFormal.MinimalRankCompression
import SierpinskiFormal.WeightedWordCesaro

/-! # Stable observations without a finite generating alphabet

Over a Noetherian module with Noetherian dual, the evaluation relation is
stable for arbitrary parameter sets. In particular, a finite-dimensional
field representation of the countable return group needs no finite
generation assumption.
-/

noncomputable section
open Filter Topology
namespace IndependentZeroBlocks

theorem noetherianEvaluation_hasBooleanDoubleLimitProperty
    {R V X Y : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [IsNoetherian R V] [IsNoetherian R (Module.Dual R V)]
    (row : X → V) (col : Y → Module.Dual R V) :
    HasBooleanDoubleLimitProperty (fun x y ↦ nonzeroBool (col y (row x))) := by
  intro x y rowLimit columnLimit rowOuter columnOuter hrow hcol hro hco
  apply zero_one_double_limit_of_no_staircases
    (fun i j ↦ nonzeroIndicator (col (y j) (row (x i))))
    (fun i j ↦ nonzeroIndicator_zero_one _) ?_ ?_
    rowLimit columnLimit rowOuter columnOuter
    (by simpa only [boolIndicator_nonzeroBool] using hrow)
    (by simpa only [boolIndicator_nonzeroBool] using hcol) hro hco
  · intro ix iy hz hd
    exact noetherian_no_upper_evaluation_staircase
      (fun i ↦ row (x (ix i))) (fun j ↦ col (y (iy j)))
      (fun i j hij ↦ (nonzeroIndicator_eq_zero_iff _).mp (hz i j hij))
      (fun i hi ↦ hd i ((nonzeroIndicator_eq_zero_iff _).mpr hi))
  · intro ix iy hz hd
    exact noetherianDual_no_lower_evaluation_staircase
      (fun i ↦ row (x (ix i))) (fun j ↦ col (y (iy j)))
      (fun i j hij ↦ (nonzeroIndicator_eq_zero_iff _).mp (hz i j hij))
      (fun i hi ↦ hd i ((nonzeroIndicator_eq_zero_iff _).mpr hi))

/-- Arbitrary group representations on a Noetherian module and its dual
have stable Boolean coefficient kernels. No generator family is chosen. -/
theorem noetherian_groupObservation_rightRow_hasBooleanDoubleLimitProperty
    {R V G : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [IsNoetherian R V] [IsNoetherian R (Module.Dual R V)] [Group G]
    (ρ : G →* Module.End R V) (l : Module.Dual R V) (v : V) :
    HasBooleanDoubleLimitProperty (fun g h ↦ nonzeroBool (l (ρ (h * g) v))) := by
  have h := noetherianEvaluation_hasBooleanDoubleLimitProperty
    (fun g ↦ ρ g v) (fun h ↦ l.comp (ρ h))
  simpa only [LinearMap.comp_apply, map_mul, Module.End.mul_apply] using h

theorem field_matrixWord_rightKernel_hasBooleanDoubleLimitProperty
    {F A ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    (M : A → Matrix ι ι F) (l : Module.Dual F (ι → F)) (v : ι → F) :
    HasBooleanDoubleLimitProperty (fun w z : List A ↦ nonzeroBool
      (l ((matrixWord M (z ++ w)).mulVec v))) := by
  have h := noetherianEvaluation_hasBooleanDoubleLimitProperty
    (fun w ↦ (matrixWord M w).mulVec v)
    (fun z ↦ l.comp (matrixWord M z).mulVecLin)
  simpa only [matrixWord_append, Matrix.mulVec_mulVec, LinearMap.comp_apply,
    Matrix.mulVecLin_apply] using h

theorem exists_tendsto_field_matrixWord_weighted_cesaro
    {F A ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    [TopologicalSpace A] [DiscreteTopology A] [Fintype A] [Nonempty A]
    (M : A → Matrix ι ι F) (l : Module.Dual F (ι → F)) (v : ι → F)
    (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) :
    ∃ L : ℝ, Tendsto (weightedIidWordCesaro p (booleanWordIndicator
      (fun w ↦ nonzeroBool (l ((matrixWord M w).mulVec v))))) atTop (𝓝 L) := by
  exact exists_tendsto_boolean_weighted_iid_word_cesaro p hp hp1 _
    (field_matrixWord_rightKernel_hasBooleanDoubleLimitProperty M l v)

end IndependentZeroBlocks
