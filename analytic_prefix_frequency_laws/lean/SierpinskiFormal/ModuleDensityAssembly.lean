import SierpinskiFormal.ModuleBoundaryExpansion
import SierpinskiFormal.ModuleCentralReturnMean
import SierpinskiFormal.RareMarkerDecay

set_option autoImplicit false

/-!
# Boundary-density assembly for module endomorphism words

The generic layer combines the exact first/last marker expansion with rare
boundary decay and the summable boundary mixture.  Module return-group means
are inserted in the final specialization.
-/

noncomputable section

open Filter Set
open scoped Topology BigOperators

namespace IndependentZeroBlocks

section BooleanBounds

variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
  [Fintype A] [Nonempty A]

theorem norm_moduleWeightedWordExtensionAverage_boolean_le_one
    (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1)
    (q : List A → Bool) (n : ℕ) (z : List A) :
    ‖weightedWordExtensionAverage p (booleanWordIndicator q) n z‖ ≤ 1 := by
  induction n generalizing z with
  | zero =>
      cases hq : q z <;> norm_num [weightedWordExtensionAverage,
        booleanWordIndicator_apply, boolIndicator, hq]
  | succ n ih =>
      rw [weightedWordExtensionAverage]
      calc
        ‖∑ a, p a * weightedWordExtensionAverage p
            (booleanWordIndicator q) n (z ++ [a])‖ ≤
            ∑ a, ‖p a * weightedWordExtensionAverage p
              (booleanWordIndicator q) n (z ++ [a])‖ := norm_sum_le _ _
        _ ≤ ∑ a, p a := by
          apply Finset.sum_le_sum
          intro a _
          rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hp a)]
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left (ih (z ++ [a])) (hp a)
        _ = 1 := hp1

end BooleanBounds

section BoundaryWeights

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem moduleBoundaryWeight_nonneg
    (p : A → ℝ) (e : A) (hp : ∀ a, 0 ≤ p a)
    (i : GapWords e × GapWords e) :
    0 ≤ moduleBoundaryWeight p e i := by
  unfold moduleBoundaryWeight
  exact mul_nonneg
    (mul_nonneg (sq_nonneg (p e)) (wordWeight_nonneg p hp i.1.1))
    (wordWeight_nonneg p hp i.2.1)

set_option maxHeartbeats 800000 in
theorem summable_moduleBoundaryWeight
    (p : A → ℝ) (e : A) (hp : ∀ a, 0 ≤ p a)
    (hp1 : ∑ a, p a = 1) (he : 0 < p e) :
    Summable (moduleBoundaryWeight p e) := by
  have hlt : realNonMarkerMass p e < 1 := by
    rw [realNonMarkerMass_eq_one_sub p e hp1]
    linarith
  let f : GapWords e → ℝ := fun g ↦ wordWeight p g.1
  have hg : Summable f := summable_gapWordWeight p e hp hlt
  have hg0 : 0 ≤ f := fun g ↦ wordWeight_nonneg p hp g.1
  have hgg : Summable (fun i : GapWords e × GapWords e ↦ f i.1 * f i.2) :=
    hg.mul_of_nonneg hg hg0 hg0
  change Summable (fun i : GapWords e × GapWords e ↦
    p e ^ 2 * wordWeight p i.1.1 * wordWeight p i.2.1)
  simpa only [f, mul_assoc] using hgg.mul_left (p e ^ 2)

set_option maxHeartbeats 800000 in
theorem hasSum_moduleBoundaryWeight_one
    (p : A → ℝ) (e : A) (hp : ∀ a, 0 ≤ p a)
    (hp1 : ∑ a, p a = 1) (he : 0 < p e) :
    HasSum (moduleBoundaryWeight p e) 1 := by
  have hlt : realNonMarkerMass p e < 1 := by
    rw [realNonMarkerMass_eq_one_sub p e hp1]
    linarith
  let f : GapWords e → ℝ := fun g ↦ wordWeight p g.1
  have hg : Summable f := summable_gapWordWeight p e hp hlt
  have hg0 : 0 ≤ f := fun g ↦ wordWeight_nonneg p hp g.1
  have hgg : Summable (fun i : GapWords e × GapWords e ↦ f i.1 * f i.2) :=
    hg.mul_of_nonneg hg hg0 hg0
  have hgap : (∑' g : GapWords e, wordWeight p g.1) = (p e)⁻¹ := by
    rw [(hasSum_gapWordWeight_geometric p e hp hlt).tsum_eq,
      realNonMarkerMass_eq_one_sub p e hp1]
    congr 1
    ring
  have hsum : (∑' i : GapWords e × GapWords e,
      moduleBoundaryWeight p e i) = 1 := by
    rw [show moduleBoundaryWeight p e = fun i : GapWords e × GapWords e ↦
        (p e) ^ 2 * (f i.1 * f i.2) by
      funext i
      simp only [moduleBoundaryWeight, f]
      exact mul_assoc _ _ _]
    rw [tsum_mul_left]
    rw [← hg.tsum_mul_tsum hg hgg, hgap]
    field_simp
  rw [← hsum]
  exact (summable_moduleBoundaryWeight p e hp hp1 he).hasSum

end BoundaryWeights

section GenericAssembly

variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
  [Fintype A] [Nonempty A] [DecidableEq A]

theorem tendsto_weightedPredicate_of_boundary_cesaro
    (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1)
    (e : A) (he : 0 < p e)
    (original : List A → Bool)
    (central : List A → List A → List A → Bool)
    (hboundary : ∀ x y z,
      original (x ++ [e] ++ y ++ [e] ++ z) = central x z y)
    (L : GapWords e × GapWords e → ℝ)
    (hL : ∀ i, Tendsto
      (realCesaroMean (abstractBoundaryCentralSequence p central i))
      atTop (𝓝 (L i))) :
    Tendsto
      (realCesaroMean (fun n ↦ weightedWordExtensionAverage p
        (booleanWordIndicator original) n []))
      atTop (𝓝 (∑' i, moduleBoundaryWeight p e i * L i)) := by
  have hw := summable_moduleBoundaryWeight p e hp hp1 he
  have hw0 : ∀ i : GapWords e × GapWords e,
      0 ≤ moduleBoundaryWeight p e i :=
    moduleBoundaryWeight_nonneg p e hp
  have hc : ∀ (i : GapWords e × GapWords e) n,
      ‖abstractBoundaryCentralSequence p central i n‖ ≤ 1 := by
    intro i n
    exact norm_moduleWeightedWordExtensionAverage_boolean_le_one p hp hp1
      (central i.1.1 i.2.1) n []
  have hmix : Tendsto
      (realCesaroMean (abstractBoundaryMixture p e central)) atTop
      (𝓝 (∑' i, moduleBoundaryWeight p e i * L i)) := by
    simpa only [abstractBoundaryMixture] using
      tendsto_realCesaroMean_renewalBoundaryMixture
        (moduleBoundaryWeight p e) hw hw0 (moduleBoundaryDelay e)
        (abstractBoundaryCentralSequence p central) L hc hL
  have hf : ∀ w : List A, ‖boolIndicator (original w)‖ ≤ 1 := by
    intro w
    cases hq : original w <;> norm_num [boolIndicator, hq]
  have hrare := tendsto_realCesaroMean_rareBoundaryWordSum_zero
    p hp hp1 (fun w ↦ boolIndicator (original w)) hf e he
  have hcesaro (N : ℕ) :
      realCesaroMean (fun n ↦ weightedWordExtensionAverage p
        (booleanWordIndicator original) n []) N =
      realCesaroMean (rareBoundaryWordSum p
        (fun w ↦ boolIndicator (original w)) e) N +
      realCesaroMean (abstractBoundaryMixture p e central) N := by
    unfold realCesaroMean
    simp_rw [weightedPredicate_eq_rare_add_mixture
      p e original central hboundary]
    rw [Finset.sum_add_distrib]
    ring
  rw [show realCesaroMean (fun n ↦ weightedWordExtensionAverage p
      (booleanWordIndicator original) n []) =
      fun N ↦ realCesaroMean (rareBoundaryWordSum p
        (fun w ↦ boolIndicator (original w)) e) N +
        realCesaroMean (abstractBoundaryMixture p e central) N by
    funext N
    exact hcesaro N]
  simpa only [zero_add] using hrare.add hmix

end GenericAssembly

section ModuleAssembly

variable {R A V B : Type*} [CommRing R]
variable [AddCommGroup V] [Module R V]
variable [AddCommGroup B] [Module R B]
variable [IsNoetherian R V] [IsNoetherian R (Module.Dual R V)]
variable [IsNoetherian R B] [IsNoetherian R (Module.Dual R B)]
variable [TopologicalSpace A] [DiscreteTopology A]
variable [Fintype A] [Nonempty A] [DecidableEq A]

/-- A boundary central sequence is exactly the physical-length central return
average with the boundary functional and seed induced by the two exterior
marker-free gaps. -/
theorem moduleBoundaryCentralSequence_eq_moduleCentralReturnExactAverage
    (p : A → ℝ) (M : A → Module.End R V)
    (U : B →ₗ[R] V) (V0 : V →ₗ[R] B)
    (left : Module.Dual R V) (seed : V)
    {e : A} (i : GapWords e × GapWords e) :
    moduleBoundaryCentralSequence p M U V0 left seed i =
      moduleCentralReturnExactAverage M U V0
        (compressedBoundaryLeft M U left i.1.1)
        (compressedBoundarySeed M V0 seed i.2.1) p := by
  rfl

/-- Boundary Cesaro limits assemble to the explicit boundary-weighted limit
of the original module coefficient predicate. -/
theorem tendsto_weightedModuleCoefficient_of_boundary_cesaro
    (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1)
    (M : A → Module.End R V) (e : A) (he : 0 < p e)
    (U : B →ₗ[R] V) (V0 : V →ₗ[R] B)
    (hfac : endoWord M [e] = U.comp V0)
    (left : Module.Dual R V) (seed : V)
    (L : GapWords e × GapWords e → ℝ)
    (hL : ∀ i, Tendsto
      (realCesaroMean
        (moduleBoundaryCentralSequence p M U V0 left seed i))
      atTop (nhds (L i))) :
    Tendsto
      (realCesaroMean (fun n ↦ weightedWordExtensionAverage p
        (booleanWordIndicator (moduleCoefficientNonzero M left seed)) n []))
      atTop (nhds (∑' i, moduleBoundaryWeight p e i * L i)) := by
  exact tendsto_weightedPredicate_of_boundary_cesaro
    p hp hp1 e he
    (moduleCoefficientNonzero M left seed)
    (moduleBoundaryCentralPredicate M U V0 left seed)
    (moduleCoefficientNonzero_boundary M e U V0 hfac left seed)
    L hL

/-- A reset factorization with bijective compressed returns gives one family
of rational central boundary means, independent of the strictly positive
normalized finite letter law.  For each law, the Cesaro density of the
original module coefficient predicate is their explicit boundary mixture. -/
theorem exists_rational_moduleBoundaryMeans_forall_positive_laws
    (M : A → Module.End R V) (e : A)
    (U : B →ₗ[R] V) (V0 : V →ₗ[R] B)
    (hfac : endoWord M [e] = U.comp V0)
    (hbij : ∀ y : List A, Function.Bijective (compressedReturn M U V0 y))
    (left : Module.Dual R V) (seed : V) :
    ∃ m : GapWords e × GapWords e → ℚ,
      ∀ (p : A → ℝ), (∀ a, 0 < p a) → (∑ a, p a = 1) →
        ((∀ i, Tendsto
          (realCesaroMean
            (moduleBoundaryCentralSequence p M U V0 left seed i))
          atTop (nhds (m i : ℝ))) ∧
        Tendsto
          (realCesaroMean (fun n ↦ weightedWordExtensionAverage p
            (booleanWordIndicator
              (moduleCoefficientNonzero M left seed)) n []))
          atTop (nhds (∑' i,
            moduleBoundaryWeight p e i * (m i : ℝ)))) := by
  let K : List A → (B ≃ₗ[R] B) := fun y ↦
    LinearEquiv.ofBijective (compressedReturn M U V0 y) (hbij y)
  have hK : ∀ y, (K y).toLinearMap = compressedReturn M U V0 y := by
    intro y
    rfl
  have hcentral : ∀ i : GapWords e × GapWords e,
      ∃ q : ℚ, ∀ (p : A → ℝ), (∀ a, 0 < p a) → (∑ a, p a = 1) →
        Tendsto
          (realCesaroMean
            (moduleBoundaryCentralSequence p M U V0 left seed i))
          atTop (nhds (q : ℝ)) := by
    intro i
    simpa only [moduleBoundaryCentralSequence_eq_moduleCentralReturnExactAverage]
      using exists_rational_forall_tendsto_moduleCentralReturnCesaro
        M e U V0 hfac K hK
        (compressedBoundaryLeft M U left i.1.1)
        (compressedBoundarySeed M V0 seed i.2.1)
  choose m hm using hcentral
  refine ⟨m, ?_⟩
  intro p hp hp1
  have hm' : ∀ i, Tendsto
      (realCesaroMean
        (moduleBoundaryCentralSequence p M U V0 left seed i))
      atTop (nhds (m i : ℝ)) := fun i ↦ hm i p hp hp1
  refine ⟨hm', ?_⟩
  exact tendsto_weightedModuleCoefficient_of_boundary_cesaro
    p (fun a ↦ (hp a).le) hp1 M e (hp e) U V0 hfac left seed
      (fun i ↦ (m i : ℝ)) hm'

end ModuleAssembly

end IndependentZeroBlocks
