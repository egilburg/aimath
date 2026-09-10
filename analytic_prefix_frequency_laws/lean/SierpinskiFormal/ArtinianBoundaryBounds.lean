import SierpinskiFormal.ArtinianBlockDensity
import SierpinskiFormal.HigherRankMeanBounds

/-!
# Probability bounds for Artinian module boundary means

The law-independent rational boundary means from `ArtinianBlockDensity` are
limits of Boolean averages.  Evaluating their common convergence theorem at
one uniform law therefore places every mean in `[0,1]`.
-/

set_option autoImplicit false
noncomputable section

open Filter Set
open scoped BigOperators Topology

namespace IndependentZeroBlocks

variable {R V A : Type*} [CommRing R] [IsArtinianRing R]
  [AddCommGroup V] [Module R V] [Module.Finite R V]
variable [TopologicalSpace A] [DiscreteTopology A] [Fintype A] [Nonempty A]
  [DecidableEq A]

/-- Simplified bounded-coefficient form of the Artinian block-density
theorem.  The reset word and rational boundary coefficients are independent
of the strictly positive normalized Bernoulli law; every coefficient is a
probability value, and the original scalar density is their displayed
suffix/boundary mixture. -/
theorem exists_minLengthWord_bounded_moduleBoundaryMeans_forall_positive_laws
    (T : A → Module.End R V) (left : Module.Dual R V) (seed : V) :
    ∃ h : List A, h ≠ [] ∧
      ∃ m : (s : Fin h.length) → (Fin (s : ℕ) → A) →
          GapWords (endoMarkerBlock h) × GapWords (endoMarkerBlock h) → ℚ,
        (∀ (s : Fin h.length) (xi : Fin (s : ℕ) → A)
          (i : GapWords (endoMarkerBlock h) × GapWords (endoMarkerBlock h)),
          (m s xi i : ℝ) ∈ Set.Icc (0 : ℝ) 1) ∧
        ∀ (p : A → ℝ), (∀ a, 0 < p a) → (∑ a, p a = 1) →
          Tendsto
            (realCesaroMean (fun n ↦ weightedWordExtensionAverage p
              (booleanWordIndicator (moduleCoefficientNonzero T left seed))
              n []))
            atTop (nhds ((∑ s : Fin h.length,
              ∑ xi : Fin (s : ℕ) → A,
                wordWeight p (List.ofFn xi) *
                  (∑' i : GapWords (endoMarkerBlock h) ×
                      GapWords (endoMarkerBlock h),
                    moduleBoundaryWeight (blockWeight p h.length)
                      (endoMarkerBlock h) i * (m s xi i : ℝ))) /
              (h.length : ℝ))) := by
  classical
  obtain ⟨h, hh, hmin, U, V0, hfac, hbij, m, hm⟩ :=
    exists_minLengthWord_moduleBoundaryMeans_forall_positive_laws T left seed
  let pRef : A → ℝ := uniformAlphabetWeight
  have hpRefPos : ∀ a, 0 < pRef a := fun a ↦ uniformAlphabetWeight_pos a
  have hpRef1 : ∑ a, pRef a = 1 := sum_uniformAlphabetWeight
  have hRef := hm pRef hpRefPos hpRef1
  have hpBlock0 : ∀ c : Fin h.length → A,
      0 ≤ blockWeight pRef h.length c :=
    blockWeight_nonneg pRef (fun a ↦ (hpRefPos a).le) h.length
  have hpBlock1 :
      ∑ c : Fin h.length → A, blockWeight pRef h.length c = 1 :=
    sum_blockWeight_eq_one pRef hpRef1 h.length
  have hmBound : ∀ (s : Fin h.length) (xi : Fin (s : ℕ) → A)
      (i : GapWords (endoMarkerBlock h) × GapWords (endoMarkerBlock h)),
      (m s xi i : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    intro s xi i
    apply realCesaroLimit_mem_Icc _ (hRef.1 s xi i)
    intro n
    rw [moduleBoundaryCentralSequence_eq_moduleCentralReturnExactAverage]
    exact moduleCentralReturnExactAverage_mem_Icc
      (blockEndomorphism T h.length) U V0
      (compressedBoundaryLeft (blockEndomorphism T h.length) U left i.1.1)
      (compressedBoundarySeed (blockEndomorphism T h.length) V0
        (moduleSuffixSeed T (List.ofFn xi) seed) i.2.1)
      (blockWeight pRef h.length) hpBlock0 hpBlock1 n
  refine ⟨h, hh, m, hmBound, ?_⟩
  intro p hp hp1
  exact (hm p hp hp1).2

end IndependentZeroBlocks

