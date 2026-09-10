import SierpinskiFormal.SourceAtomicTransform

/-! # Full analytic atomic law for recognizable source observations

The common marker and rational coefficients are fixed before positive source
parameters. The exact actual law, analytic branch values, all analytic mixed
moments, and jointly holomorphic exponential transforms are linked below.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter MeasureTheory Set Topology
open scoped BigOperators
namespace IndependentZeroBlocks
namespace FiniteStateSource

attribute [local instance] selectorMeasurableSpace selectorTopologicalSpace
variable {R A Q J : Type*} [CommRing R] [Fintype Q] [DecidableEq Q] [Fintype J]

/-- The complete scalar-word source endpoint. Its explicit branches are
analytic functions of raw positive edge parameters and determine the actual
pathwise limit. `sourceBlockMixedMoment_eq_integral` and
`sourceComplexExpTransform_eq_integral` identify all mixed moments and joint
exponential transforms of any finite collection of these common-boundary
limits; their analytic and entire properties are separately proved. -/
theorem exists_commonReset_source_scalarWord_analytic_atomic_law
    (S : FiniteStateSource Q A) {f : J → List A → R}
    (D : ∀ j, ScalarWordRepresentation R A (f j)) :
    ∃ h : List S.Selector, h ≠ [] ∧
      ∀ op : (J → Bool) → Bool,
      ∃ (m : Q → BlockBranchCoefficients h)
        (hm : ∀ q s ξ u v, (m q s ξ u v : ℝ) ∈ Icc (0 : ℝ) 1),
        ∀ q (p : (r : Q) → S.Edge r → ℝ) (hp : ∀ r e, 0 < p r e),
        (∀ u : GapWords (endoMarkerBlock h),
          AnalyticAt ℝ (fun z ↦ S.sourceBlockBranch h (m q) (hm q) z u) p) ∧
        IIDBlockAtomicLaw (S.normalizedSelectorLaw p hp) h.length (endoMarkerBlock h)
          (fun w ↦ scalarWordBooleanPredicate op f (S.transducer.outputWord q w))
          (S.sourceBlockBranch h (m q) (hm q) p) := by
  obtain ⟨h, hh, hall⟩ := S.exists_commonReset_source_scalarWord_atomic_law D
  refine ⟨h, hh, ?_⟩
  intro op
  obtain ⟨m, hm, hLaw⟩ := hall op
  refine ⟨m, hm, ?_⟩
  intro q p hp
  refine ⟨S.analyticAt_sourceBlockBranch h (m q) (hm q) p hp, ?_⟩
  have heq : S.sourceBlockBranch h (m q) (hm q) p =
      blockMarkerBranch h.length (endoMarkerBlock h) (m q) (S.normalizedSelectorLaw p hp).weight :=
    funext (S.sourceBlockBranch_eq h (m q) (hm q) p hp)
  rw [heq]
  exact hLaw q p hp

/-- Recognizable polynomial Boolean observations over arbitrary commutative
rings, with arbitrary initial source state, have the full analytic atomic law
on every fixed positive edge support. -/
theorem exists_commonReset_source_polynomialWord_analytic_atomic_law
    (S : FiniteStateSource Q A) {I : Type*} {f : I → List A → R}
    (D : ∀ i, ScalarWordRepresentation R A (f i)) (P : J → MvPolynomial I R) :
    ∃ h : List S.Selector, h ≠ [] ∧
      ∀ op : (J → Bool) → Bool,
      ∃ (m : Q → BlockBranchCoefficients h)
        (hm : ∀ q s ξ u v, (m q s ξ u v : ℝ) ∈ Icc (0 : ℝ) 1),
        ∀ q (p : (r : Q) → S.Edge r → ℝ) (hp : ∀ r e, 0 < p r e),
        (∀ u : GapWords (endoMarkerBlock h),
          AnalyticAt ℝ (fun z ↦ S.sourceBlockBranch h (m q) (hm q) z u) p) ∧
        IIDBlockAtomicLaw (S.normalizedSelectorLaw p hp) h.length (endoMarkerBlock h)
          (fun w ↦ scalarWordBooleanPredicate op
            (fun j w ↦ MvPolynomial.eval (fun i ↦ f i w) (P j)) (S.transducer.outputWord q w))
          (S.sourceBlockBranch h (m q) (hm q) p) := by
  let DP := fun j ↦ (ScalarWordRepresentation.mvPolynomial_family D (P j)).some
  exact S.exists_commonReset_source_scalarWord_analytic_atomic_law DP

/-- A finite family of operations and starting states uses one simultaneous
full-measure event for each fixed source law. No common event over an
uncountable parameter set is asserted. -/
theorem source_atomic_family_simultaneous {K : Type*} [Fintype K]
    (S : FiniteStateSource Q A) (p : (r : Q) → S.Edge r → ℝ)
    (hp : ∀ r e, 0 < p r e) (ell : ℕ) (e : Fin ell → S.Selector)
    (q : K → Q) (event : K → List A → Bool) (B : K → GapWords e → ℝ)
    (h : ∀ k, IIDBlockAtomicLaw (S.normalizedSelectorLaw p hp) ell e
      (fun w ↦ event k (S.transducer.outputWord (q k) w)) (B k)) :
    ∀ᵐ ω ∂(S.normalizedSelectorLaw p hp).iidMeasure, ∀ k,
      Tendsto (fun N ↦ S.pathFrequency (q k) (event k) N ω)
        atTop (𝓝 (B k (initialMarkerGap e (iidBlockPath ell ω)))) :=
  ae_all_iff.mpr fun k ↦ (S.source_atomicLaw_pathwise p hp ell e (q k) (event k) (B k) (h k)).1

end FiniteStateSource
end IndependentZeroBlocks
