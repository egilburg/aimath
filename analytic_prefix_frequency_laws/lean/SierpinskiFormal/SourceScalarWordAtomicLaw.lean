import SierpinskiFormal.ScalarWordAtomicLaw
import SierpinskiFormal.FiniteStateSourceProbability
import SierpinskiFormal.FiniteStateReindex

/-! # Atomic pathwise laws for arbitrary-start finite-state sources -/

noncomputable section
open Filter MeasureTheory Set Topology
open scoped BigOperators
namespace IndependentZeroBlocks
namespace FiniteStateSource

attribute [local instance] selectorMeasurableSpace selectorTopologicalSpace

variable {R A Q J : Type*} [CommRing R] [Fintype Q] [DecidableEq Q] [Fintype J]

/-- One selector marker is chosen before the starting state, Boolean operation
and positive edge weights. The initial gap is allowed to retain latent selector
choices. The record's pathwise and L1 conclusions refer to the exact accepted
source path via `pathFrequency_eq_stationary`. -/
theorem exists_commonReset_source_scalarWord_atomic_law
    (S : FiniteStateSource Q A) {f : J → List A → R}
    (D : ∀ j, ScalarWordRepresentation R A (f j)) :
    ∃ h : List S.Selector, h ≠ [] ∧
      ∀ op : (J → Bool) → Bool,
      ∃ m : Q → (s : Fin h.length) → (Fin (s : ℕ) → S.Selector) →
          List (Fin h.length → S.Selector) → List (Fin h.length → S.Selector) → ℚ,
        (∀ q s ξ u v, (m q s ξ u v : ℝ) ∈ Icc (0 : ℝ) 1) ∧
        ∀ q (p : (r : Q) → S.Edge r → ℝ) (hp : ∀ r e, 0 < p r e),
        IIDBlockAtomicLaw (S.normalizedSelectorLaw p hp) h.length (endoMarkerBlock h)
          (fun w ↦ scalarWordBooleanPredicate op f (S.transducer.outputWord q w))
          (blockMarkerBranch h.length (endoMarkerBlock h) (m q)
            (S.normalizedSelectorLaw p hp).weight) := by
  classical
  let E := fun qj : Q × J ↦ (D qj.2).pullbackFinite S.transducer qj.1
  obtain ⟨h, hh, hall⟩ := exists_commonReset_scalarWord_atomic_law E
  refine ⟨h, hh, ?_⟩
  intro op
  choose m hm hLaw using (fun q : Q ↦ hall (fun b ↦ op (fun j ↦ b (q, j))))
  refine ⟨m, hm, ?_⟩
  intro q p hp
  have hpos : ∀ a, 0 < (S.normalizedSelectorLaw p hp).weight a := by
    intro a
    exact S.selectorWeight_pos (normalizedSourceWeights p)
      (fun r e ↦ normalizedSourceWeights_pos p hp r e) a
  have hevent : scalarWordBooleanPredicate (fun b : Q × J → Bool ↦ op (fun j ↦ b (q, j)))
      (fun qj w ↦ f qj.2 (S.transducer.outputWord qj.1 w)) =
      (fun w ↦ scalarWordBooleanPredicate op f (S.transducer.outputWord q w)) := by
    rfl
  simpa only [hevent] using hLaw q (S.normalizedSelectorLaw p hp) hpos

theorem source_atomicLaw_pathwise
    (S : FiniteStateSource Q A) (p : (r : Q) → S.Edge r → ℝ)
    (hp : ∀ r e, 0 < p r e) (ell : ℕ) (e : Fin ell → S.Selector)
    (q : Q) (event : List A → Bool) (D : GapWords e → ℝ)
    (h : IIDBlockAtomicLaw (S.normalizedSelectorLaw p hp) ell e
      (fun w ↦ event (S.transducer.outputWord q w)) D) :
    (∀ᵐ ω ∂(S.normalizedSelectorLaw p hp).iidMeasure,
      Tendsto (fun N ↦ S.pathFrequency q event N ω)
        atTop (𝓝 (D (initialMarkerGap e (iidBlockPath ell ω))))) ∧
    Tendsto (fun N ↦ ∫ ω, ‖S.pathFrequency q event N ω -
      D (initialMarkerGap e (iidBlockPath ell ω))‖
        ∂(S.normalizedSelectorLaw p hp).iidMeasure) atTop (𝓝 0) := by
  simpa only [S.pathFrequency_eq_stationary] using And.intro h.pathwise h.in_L1

theorem exists_commonReset_source_polynomialWord_atomic_law
    (S : FiniteStateSource Q A) {I : Type*} {f : I → List A → R}
    (D : ∀ i, ScalarWordRepresentation R A (f i))
    (P : J → MvPolynomial I R) :
    ∃ h : List S.Selector, h ≠ [] ∧
      ∀ op : (J → Bool) → Bool,
      ∃ m : Q → (s : Fin h.length) → (Fin (s : ℕ) → S.Selector) →
          List (Fin h.length → S.Selector) → List (Fin h.length → S.Selector) → ℚ,
        (∀ q s ξ u v, (m q s ξ u v : ℝ) ∈ Icc (0 : ℝ) 1) ∧
        ∀ q (p : (r : Q) → S.Edge r → ℝ) (hp : ∀ r e, 0 < p r e),
        IIDBlockAtomicLaw (S.normalizedSelectorLaw p hp) h.length (endoMarkerBlock h)
          (fun w ↦ scalarWordBooleanPredicate op
            (fun j w ↦ MvPolynomial.eval (fun i ↦ f i w) (P j)) (S.transducer.outputWord q w))
          (blockMarkerBranch h.length (endoMarkerBlock h) (m q)
            (S.normalizedSelectorLaw p hp).weight) := by
  let DP := fun j ↦ (ScalarWordRepresentation.mvPolynomial_family D (P j)).some
  exact S.exists_commonReset_source_scalarWord_atomic_law DP

end FiniteStateSource
end IndependentZeroBlocks
