import SierpinskiFormal.ModuleBlockAtomicLaw
import SierpinskiFormal.MatrixBooleanBoundaryDensity
import SierpinskiFormal.StationaryScalarWordObservation

/-! # Arbitrary-ring scalar representations preserve the complete atomic law -/

noncomputable section
open Filter MeasureTheory Set Topology
open scoped BigOperators
namespace IndependentZeroBlocks

variable {R A J ι : Type*} [CommRing R]
  [Fintype A] [Nonempty A] [DecidableEq A]
  [TopologicalSpace A] [DiscreteTopology A]
  [MeasurableSpace A] [MeasurableSingletonClass A] [BorelSpace A]
  [Fintype J] [Fintype ι] [DecidableEq ι]

theorem exists_commonReset_matrixBoolean_atomic_law
    (M : J → A → Matrix ι ι R) (left seed : J → ι → R) :
    ∃ h : List A, h ≠ [] ∧
      ∀ op : (J → Bool) → Bool,
      ∃ m : (s : Fin h.length) → (Fin (s : ℕ) → A) →
          List (Fin h.length → A) → List (Fin h.length → A) → ℚ,
        (∀ s ξ u v, (m s ξ u v : ℝ) ∈ Icc (0 : ℝ) 1) ∧
        ∀ P : FiniteProbabilityWeights A, (∀ a, 0 < P.weight a) →
        IIDBlockAtomicLaw P h.length (endoMarkerBlock h)
          (matrixBooleanPredicate op M left seed)
          (blockMarkerBranch h.length (endoMarkerBlock h) m P.weight) := by
  classical
  obtain ⟨S, Q, T, v, rows, _, _, hFin, _, hword⟩ :=
    exists_matrixFamily_faithfulArtinian_realization M left seed
  letI := hFin
  obtain ⟨h, hh, hall⟩ := exists_commonReset_moduleBoolean_atomic_law T
  refine ⟨h, hh, ?_⟩
  intro op
  let E : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let op' : (Fin (Fintype.card J) → Bool) → Bool := fun b ↦ op (fun j ↦ b (E j))
  let rows' : Fin (Fintype.card J) → Module.Dual Q.Carrier (J → ι → Q.Carrier) :=
    fun j ↦ rows (E.symm j)
  obtain ⟨m, hm, hLaw⟩ := hall (Fintype.card J) op' rows' v
  have hpred : moduleBooleanCoefficientNonzero op' T rows' v =
      matrixBooleanPredicate op M left seed := by
    funext w
    change op (fun j ↦ moduleCoefficientNonzero T (rows (E.symm (E j))) v w) = _
    simp only [Equiv.symm_apply_apply, hword]
    rfl
  exact ⟨m, hm, fun P hp ↦ by simpa only [hpred] using hLaw P hp⟩

theorem exists_commonReset_scalarWord_atomic_law
    {f : J → List A → R} (D : ∀ j, ScalarWordRepresentation R A (f j)) :
    ∃ h : List A, h ≠ [] ∧
      ∀ op : (J → Bool) → Bool,
      ∃ m : (s : Fin h.length) → (Fin (s : ℕ) → A) →
          List (Fin h.length → A) → List (Fin h.length → A) → ℚ,
        (∀ s ξ u v, (m s ξ u v : ℝ) ∈ Icc (0 : ℝ) 1) ∧
        ∀ P : FiniteProbabilityWeights A, (∀ a, 0 < P.weight a) →
        IIDBlockAtomicLaw P h.length (endoMarkerBlock h) (scalarWordBooleanPredicate op f)
          (blockMarkerBranch h.length (endoMarkerBlock h) m P.weight) := by
  classical
  let E : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let F := ScalarWordRepresentation.packFamily (fun j : Fin (Fintype.card J) ↦ D (E.symm j))
  letI := F.fintype
  letI := F.decidableEq
  obtain ⟨h, hh, hall⟩ :=
    exists_commonReset_matrixBoolean_atomic_law F.transition F.left F.seed
  refine ⟨h, hh, ?_⟩
  intro op
  let op' : (Fin (Fintype.card J) → Bool) → Bool := fun b ↦ op (fun j ↦ b (E j))
  have hpred : matrixBooleanPredicate op' F.transition F.left F.seed =
      scalarWordBooleanPredicate op f := by
    funext w
    simp only [matrixBooleanPredicate, scalarWordBooleanPredicate, F.coefficient, op',
      Equiv.symm_apply_apply]
  simpa only [hpred] using hall op'

end IndependentZeroBlocks
