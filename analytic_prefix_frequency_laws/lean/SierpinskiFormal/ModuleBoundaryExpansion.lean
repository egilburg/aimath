import SierpinskiFormal.MatrixBoundaryExpansion
import SierpinskiFormal.FiniteLengthCompression

set_option autoImplicit false

/-!
# First/last marker expansion for module endomorphism words

The first section isolates the boundary-mixture argument for an arbitrary
Boolean word predicate and an arbitrary central boundary predicate.  The
module reset identity is supplied in the specialization below.
-/

noncomputable section

open Filter Set
open scoped Topology BigOperators

namespace IndependentZeroBlocks

section AbstractBoundary

variable {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
  [Fintype A] [Nonempty A] [DecidableEq A]

def moduleBoundaryWeight (p : A → ℝ) (e : A)
    (i : GapWords e × GapWords e) : ℝ :=
  p e ^ 2 * wordWeight p i.1.1 * wordWeight p i.2.1

def moduleBoundaryDelay (e : A) (i : GapWords e × GapWords e) : ℕ :=
  i.1.1.length + i.2.1.length + 2

def abstractBoundaryCentralSequence
    (p : A → ℝ) (central : List A → List A → List A → Bool)
    {e : A} (i : GapWords e × GapWords e) (n : ℕ) : ℝ :=
  weightedWordExtensionAverage p
    (booleanWordIndicator (central i.1.1 i.2.1)) n []

def abstractBoundaryMixture
    (p : A → ℝ) (e : A)
    (central : List A → List A → List A → Bool) : ℕ → ℝ :=
  renewalBoundaryMixture (moduleBoundaryWeight p e) (moduleBoundaryDelay e)
    (abstractBoundaryCentralSequence p central)

theorem markerBoundaryAbstractSum_eq_mixture
    (p : A → ℝ) (e : A)
    (central : List A → List A → List A → Bool) (N : ℕ) :
    (∑' t : MarkerBoundary e,
      if (t.word e).length = N then
        p e ^ 2 * wordWeight p t.left * wordWeight p t.middle *
          wordWeight p t.right *
          boolIndicator (central t.left t.right t.middle)
      else 0) = abstractBoundaryMixture p e central N := by
  let E := markerBoundaryEquiv e
  let original : MarkerBoundary e → ℝ := fun t ↦
    if (t.word e).length = N then
      p e ^ 2 * wordWeight p t.left * wordWeight p t.middle *
        wordWeight p t.right * boolIndicator (central t.left t.right t.middle)
    else 0
  let separated : (GapWords e × GapWords e) × List A → ℝ := fun iy ↦
    if moduleBoundaryDelay e iy.1 + iy.2.length = N then
      moduleBoundaryWeight p e iy.1 * wordWeight p iy.2 *
        boolIndicator (central iy.1.1.1 iy.1.2.1 iy.2)
    else 0
  have horiginal : Summable original := by
    apply summable_of_finite_support
    have hfin := (List.finite_length_eq A N).preimage
      (MarkerBoundary.word_injective e).injOn
    exact hfin.subset (by
      intro t ht
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      by_contra hlen
      apply ht
      dsimp only [original]
      rw [if_neg hlen])
  have hcompose : separated ∘ E = original := by
    funext t
    change separated (markerBoundaryEquiv e t) = original t
    change (if t.left.length + t.right.length + 2 + t.middle.length = N then
        p e ^ 2 * wordWeight p t.left * wordWeight p t.right *
          wordWeight p t.middle * boolIndicator (central t.left t.right t.middle) else 0) =
      if (t.word e).length = N then
        p e ^ 2 * wordWeight p t.left * wordWeight p t.middle *
          wordWeight p t.right * boolIndicator (central t.left t.right t.middle) else 0
    by_cases hsep : t.left.length + t.right.length + 2 + t.middle.length = N
    · have hword : (t.word e).length = N := by
        rw [MarkerBoundary.length_word]
        omega
      rw [if_pos hsep, if_pos hword]
      ring
    · have hword : ¬(t.word e).length = N := by
        intro h
        apply hsep
        rw [MarkerBoundary.length_word] at h
        omega
      rw [if_neg hsep, if_neg hword]
  have hseparated : Summable separated := by
    apply (E.summable_iff).mp
    rw [hcompose]
    exact horiginal
  change (∑' t : MarkerBoundary e, original t) = _
  calc
    (∑' t : MarkerBoundary e, original t) =
        ∑' iy : (GapWords e × GapWords e) × List A, separated iy := by
      rw [← E.tsum_eq separated]
      exact tsum_congr (fun t ↦ (congrFun hcompose t).symm)
    _ = ∑' i : GapWords e × GapWords e, ∑' y : List A, separated (i, y) :=
      hseparated.tsum_prod
    _ = abstractBoundaryMixture p e central N := by
      rw [abstractBoundaryMixture, renewalBoundaryMixture]
      apply tsum_congr
      intro i
      by_cases hd : moduleBoundaryDelay e i ≤ N
      · let m := N - moduleBoundaryDelay e i
        have hlen (y : List A) :
            moduleBoundaryDelay e i + y.length = N ↔ y.length = m := by
          dsimp [m]
          omega
        calc
          (∑' y : List A, separated (i, y)) =
              moduleBoundaryWeight p e i *
                exactLengthWordSum p
                  (fun y ↦ boolIndicator (central i.1.1 i.2.1 y)) m := by
            rw [exactLengthWordSum, ← tsum_mul_left]
            apply tsum_congr
            intro y
            by_cases hy : y.length = m
            · have hc : moduleBoundaryDelay e i + y.length = N := (hlen y).mpr hy
              rw [show separated (i, y) = moduleBoundaryWeight p e i *
                    wordWeight p y * boolIndicator (central i.1.1 i.2.1 y) by
                dsimp only [separated]
                rw [if_pos hc]]
              rw [Set.indicator_of_mem (by simpa using hy)]
              ring
            · have hc : ¬moduleBoundaryDelay e i + y.length = N :=
                fun h ↦ hy ((hlen y).mp h)
              rw [show separated (i, y) = 0 by
                dsimp only [separated]
                rw [if_neg hc]]
              rw [Set.indicator_of_notMem (by simpa using hy)]
              simp
          _ = moduleBoundaryWeight p e i *
              abstractBoundaryCentralSequence p central i m := by
            rw [exactLengthWordSum_eq_tuple_sum]
            rw [abstractBoundaryCentralSequence,
              weightedWordExtensionAverage_eq_tuple_sum]
            simp only [List.nil_append, booleanWordIndicator_apply]
          _ = moduleBoundaryWeight p e i *
              delayedSequence (moduleBoundaryDelay e i)
                (abstractBoundaryCentralSequence p central i) N := by
            simp [delayedSequence, hd, m]
      · have hnone : ∀ y : List A,
            ¬moduleBoundaryDelay e i + y.length = N := by
          intro y h
          omega
        simp [separated, hnone, delayedSequence, hd]

theorem weightedPredicate_eq_rare_add_mixture
    (p : A → ℝ) (e : A) (original : List A → Bool)
    (central : List A → List A → List A → Bool)
    (hboundary : ∀ x y z,
      original (x ++ [e] ++ y ++ [e] ++ z) = central x z y)
    (N : ℕ) :
    weightedWordExtensionAverage p (booleanWordIndicator original) N [] =
      rareBoundaryWordSum p (fun w ↦ boolIndicator (original w)) e N +
        abstractBoundaryMixture p e central N := by
  rw [weightedWordExtensionAverage_eq_tuple_sum]
  simp only [List.nil_append, booleanWordIndicator_apply]
  rw [← exactLengthWordSum_eq_tuple_sum p
    (fun w ↦ boolIndicator (original w)) N]
  rw [exactLengthWordSum_eq_rare_add_markerBoundary]
  congr 1
  rw [markerBoundaryWordSum]
  rw [← markerBoundaryAbstractSum_eq_mixture p e central N]
  apply tsum_congr
  intro t
  by_cases hlen : (t.word e).length = N
  · simp only [hlen, if_true]
    rw [MarkerBoundary.wordWeight_word]
    rw [show t.word e = t.left ++ [e] ++ t.middle ++ [e] ++ t.right by rfl]
    rw [hboundary]
  · have hlen' : ¬t.left.length + t.middle.length + t.right.length + 2 = N := by
      simpa using hlen
    simp [hlen, hlen']

end AbstractBoundary

section ModuleReset

variable {R V B A : Type*} [CommRing R]
  [AddCommGroup V] [Module R V] [AddCommGroup B] [Module R B]

/-- The original scalar nonvanishing predicate on endomorphism words. -/
def moduleCoefficientNonzero (M : A → Module.End R V)
    (left : Module.Dual R V) (seed : V) (w : List A) : Bool :=
  nonzeroBool (left (endoWord M w seed))

/-- With fixed boundary gaps, the middle word is observed through its
compressed return endomorphism. -/
def moduleBoundaryCentralPredicate
    (M : A → Module.End R V) (U : B →ₗ[R] V) (V0 : V →ₗ[R] B)
    (left : Module.Dual R V) (seed : V)
    (x z y : List A) : Bool :=
  nonzeroBool (compressedBoundaryLeft M U left x
    (compressedReturn M U V0 y (compressedBoundarySeed M V0 seed z)))

theorem moduleCoefficientNonzero_boundary
    (M : A → Module.End R V) (e : A)
    (U : B →ₗ[R] V) (V0 : V →ₗ[R] B)
    (hfac : endoWord M [e] = U.comp V0)
    (left : Module.Dual R V) (seed : V) (x y z : List A) :
    moduleCoefficientNonzero M left seed (x ++ [e] ++ y ++ [e] ++ z) =
      moduleBoundaryCentralPredicate M U V0 left seed x z y := by
  apply congrArg nonzeroBool
  have h := coefficient_boundary_endoResetSandwichWord
    M [e] x z U V0 hfac [y] left seed
  simpa [moduleCoefficientNonzero, moduleBoundaryCentralPredicate,
    endoResetSandwichWord, List.append_assoc] using h

variable [TopologicalSpace A] [DiscreteTopology A]
  [Fintype A] [Nonempty A] [DecidableEq A]

def moduleBoundaryCentralSequence
    {e : A} (p : A → ℝ) (M : A → Module.End R V)
    (U : B →ₗ[R] V) (V0 : V →ₗ[R] B)
    (left : Module.Dual R V) (seed : V)
    (i : GapWords e × GapWords e) (n : ℕ) : ℝ :=
  abstractBoundaryCentralSequence p
    (moduleBoundaryCentralPredicate M U V0 left seed) i n

def moduleBoundaryMixture
    (p : A → ℝ) (M : A → Module.End R V) (e : A)
    (U : B →ₗ[R] V) (V0 : V →ₗ[R] B)
    (left : Module.Dual R V) (seed : V) : ℕ → ℝ :=
  abstractBoundaryMixture p e
    (moduleBoundaryCentralPredicate M U V0 left seed)

theorem weightedModuleCoefficient_eq_rare_add_mixture
    (p : A → ℝ) (M : A → Module.End R V) (e : A)
    (U : B →ₗ[R] V) (V0 : V →ₗ[R] B)
    (hfac : endoWord M [e] = U.comp V0)
    (left : Module.Dual R V) (seed : V) (N : ℕ) :
    weightedWordExtensionAverage p
        (booleanWordIndicator (moduleCoefficientNonzero M left seed)) N [] =
      rareBoundaryWordSum p
          (fun w ↦ boolIndicator (moduleCoefficientNonzero M left seed w)) e N +
        moduleBoundaryMixture p M e U V0 left seed N := by
  exact weightedPredicate_eq_rare_add_mixture p e
    (moduleCoefficientNonzero M left seed)
    (moduleBoundaryCentralPredicate M U V0 left seed)
    (moduleCoefficientNonzero_boundary M e U V0 hfac left seed) N

end ModuleReset

end IndependentZeroBlocks
