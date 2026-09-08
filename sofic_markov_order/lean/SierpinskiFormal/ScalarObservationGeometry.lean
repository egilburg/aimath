import SierpinskiFormal.ObservableSpan
import SierpinskiFormal.AffinePredicateDensity
import SierpinskiFormal.MatrixCertificateTransfer

set_option autoImplicit false
namespace IndependentZeroBlocks
open scoped BigOperators

section FiniteModel

variable {K V : Type*} [CommRing K] [IsNoetherianRing K]
  [AddCommGroup V] [Module K V]

/-- Scalar support geometry obtained from a finite closed family of actual
word observations.  This formulation isolates precisely the finite model
needed by the proof, so it applies beyond finite-dimensional vector spaces. -/
theorem scalarObservation_sparse_geometry_of_finite_word_model
    (b : ℕ) (hb : 2 ≤ b) (T : Fin b → Module.End K V) (u : ℕ → V)
    (hrec : ∀ n (r : Fin b), u (b * n + r.val) = T r (u n))
    (l : Module.Dual K V)
    (hmodel : ∃ (d : ℕ) (w : Fin d → List (Fin b)) (a : Fin d → K)
      (C : Fin b → Matrix (Fin d) (Fin d) K),
      (∀ x, l x = ∑ j, a j * l (linearWord T (w j) x)) ∧
      (∀ r i x, l (linearWord T (w i) (T r x)) =
        ∑ j, C r i j * l (linearWord T (w j) x))) :
    (HasZeroPredicateDensity (fun n ↦ l (u n) ≠ 0) ↔
      HasUniformRelativeHoles (fun n ↦ l (u n) ≠ 0)) ∧
    (HasZeroPredicateDensity (fun n ↦ l (u n) ≠ 0) ↔
      ∃ α : ℝ, α < 1 ∧
        HasUniformPowerIntervalBound α (fun n ↦ l (u n) ≠ 0)) ∧
    (HasZeroPredicateDensity (fun n ↦ l (u n) ≠ 0) ∨
      HasPositiveLowerPredicateDensity (fun n ↦ l (u n) ≠ 0)) ∧
    (HasPositiveLowerPredicateDensity (fun n ↦ l (u n) ≠ 0) ↔
      ¬HasZeroPredicateDensity (fun n ↦ l (u n) ≠ 0)) := by
  classical
  obtain ⟨d, w, a, C, hreconstruct, hclosed⟩ := hmodel
  let g : ℕ → (Fin d → K) := fun n i ↦ l (linearWord T (w i) (u n))
  let S : Fin b → Module.End K (Fin d → K) := fun r ↦ Matrix.mulVecLin (C r)
  have grec : ∀ n (r : Fin b), g (b * n + r.val) = S r (g n) := by
    intro n r
    funext i
    simp only [g, S, hrec n r]
    rw [hclosed r i (u n)]
    rfl
  let q : Fin d → ℕ := fun i ↦ b ^ (w i).length
  let s : Fin d → ℕ := fun i ↦ Nat.ofDigits b ((w i).map Fin.val)
  have hq : ∀ i, 0 < q i := by
    intro i
    exact pow_pos (by omega) _
  have hsupport (n : ℕ) :
      g n ≠ 0 ↔ ∃ i, l (u (q i * n + s i)) ≠ 0 := by
    constructor
    · intro hn
      by_contra hnone
      push_neg at hnone
      apply hn
      funext i
      dsimp only [g]
      rw [linearWord_apply_digitRecurrence b T u hrec]
      exact hnone i
    · rintro ⟨i, hi⟩ hn
      apply hi
      have hz := congrFun hn i
      dsimp only [g] at hz
      rw [linearWord_apply_digitRecurrence b T u hrec] at hz
      exact hz
  have hpred : (fun n ↦ g n ≠ 0) =
      (fun n ↦ ∃ i, l (u (q i * n + s i)) ≠ 0) := by
    funext n
    exact propext (hsupport n)
  have hsub : ∀ n, l (u n) ≠ 0 → g n ≠ 0 := by
    intro n hfn hgn
    apply hfn
    rw [hreconstruct]
    apply Finset.sum_eq_zero
    intro i hi
    have hgi : l (linearWord T (w i) (u n)) = 0 := by
      simpa only [g, Pi.zero_apply] using congrFun hgn i
    simp [hgi]
  have hg := linearDigit_sparse_geometry_equivalences b hb S g grec
  have fzero_to_gzero :
      HasZeroPredicateDensity (fun n ↦ l (u n) ≠ 0) →
        HasZeroPredicateDensity (fun n ↦ g n ≠ 0) := by
    intro hz
    rw [hpred]
    exact hz.finite_affine_preimages q s hq
  have gholes_to_fholes :
      HasUniformRelativeHoles (fun n ↦ g n ≠ 0) →
        HasUniformRelativeHoles (fun n ↦ l (u n) ≠ 0) := by
    intro hh
    exact hh.mono hsub
  have gbound_to_fbound (α : ℝ) :
      HasUniformPowerIntervalBound α (fun n ↦ g n ≠ 0) →
        HasUniformPowerIntervalBound α (fun n ↦ l (u n) ≠ 0) := by
    intro hh
    exact hh.mono hsub
  have gpositive_to_fpositive :
      HasPositiveLowerPredicateDensity (fun n ↦ g n ≠ 0) →
        HasPositiveLowerPredicateDensity (fun n ↦ l (u n) ≠ 0) := by
    intro hp
    rw [hpred] at hp
    exact positiveLowerPredicateDensity_of_finite_affine_preimages
      (fun n ↦ l (u n) ≠ 0) q s hq hp
  have hzero_holes :
      HasZeroPredicateDensity (fun n ↦ l (u n) ≠ 0) ↔
        HasUniformRelativeHoles (fun n ↦ l (u n) ≠ 0) := by
    constructor
    · intro hz
      exact gholes_to_fholes (hg.1.mp (fzero_to_gzero hz))
    · exact fun hh ↦ hh.toZeroPredicateDensity
  have hzero_bound :
      HasZeroPredicateDensity (fun n ↦ l (u n) ≠ 0) ↔
        ∃ α : ℝ, α < 1 ∧
          HasUniformPowerIntervalBound α (fun n ↦ l (u n) ≠ 0) := by
    constructor
    · intro hz
      obtain ⟨α, hα, hbound⟩ := hg.2.1.mp (fzero_to_gzero hz)
      exact ⟨α, hα, gbound_to_fbound α hbound⟩
    · rintro ⟨α, hα, hbound⟩
      exact hbound.toPowerPredicateBound.toZeroPredicateDensity hα
  have hpositive :
      HasPositiveLowerPredicateDensity (fun n ↦ l (u n) ≠ 0) ↔
        ¬HasZeroPredicateDensity (fun n ↦ l (u n) ≠ 0) := by
    constructor
    · exact fun hp hz ↦ hp.not_zeroDensity hz
    · intro hnz
      have hgnz : ¬HasZeroPredicateDensity (fun n ↦ g n ≠ 0) := by
        intro hgz
        exact hnz (hzero_holes.mpr (gholes_to_fholes (hg.1.mp hgz)))
      rcases hg.2.2 with hgz | hgp
      · exact False.elim (hgnz hgz)
      · exact gpositive_to_fpositive hgp
  refine ⟨hzero_holes, hzero_bound, ?_, hpositive⟩
  exact (Classical.em _).imp id hpositive.mpr

/-- For a finite closed family of actual observation rows, scalar density
zero is equivalent to one word killing every row on every recurrence state.
This is the finite-row interface for intrinsic observation certificates. -/
theorem scalarObservation_density_zero_iff_zero_row_fiber
    (b : ℕ) (hb : 2 ≤ b) (T : Fin b → Module.End K V) (u : ℕ → V)
    (hrec : ∀ n (r : Fin b), u (b * n + r.val) = T r (u n))
    (l : Module.Dual K V) (d : ℕ) (w : Fin d → List (Fin b))
    (a : Fin d → K) (C : Fin b → Matrix (Fin d) (Fin d) K)
    (hreconstruct : ∀ x, l x = ∑ j, a j * l (linearWord T (w j) x))
    (hclosed : ∀ r i x, l (linearWord T (w i) (T r x)) =
      ∑ j, C r i j * l (linearWord T (w j) x)) :
    HasZeroPredicateDensity (fun n ↦ l (u n) ≠ 0) ↔
      ∃ z : List (Fin b), ∀ n i,
        l (linearWord T (w i) (linearWord T z (u n))) = 0 := by
  classical
  let g : ℕ → (Fin d → K) := fun n i ↦ l (linearWord T (w i) (u n))
  let S : Fin b → Module.End K (Fin d → K) := fun r ↦ Matrix.mulVecLin (C r)
  have grec : ∀ n (r : Fin b), g (b * n + r.val) = S r (g n) := by
    intro n r
    funext i
    simp only [g, S, hrec n r]
    rw [hclosed r i (u n)]
    rfl
  have hstate (z : List (Fin b)) (x : V) :
      linearWord S z (fun i ↦ l (linearWord T (w i) x)) =
        (fun i ↦ l (linearWord T (w i) (linearWord T z x))) := by
    induction z with
    | nil => simp
    | cons r z ih =>
        funext i
        rw [linearWord_cons, Module.End.mul_apply, linearWord_cons,
          Module.End.mul_apply, ih]
        dsimp only [S, Matrix.mulVecLin_apply]
        exact (hclosed r i (linearWord T z x)).symm
  have hvalue (z : List (Fin b)) (n : ℕ) :
      linearWord S z (g n) =
        (fun i ↦ l (linearWord T (w i) (linearWord T z (u n)))) := by
    simpa only [g] using hstate z (u n)
  let q : Fin d → ℕ := fun i ↦ b ^ (w i).length
  let s : Fin d → ℕ := fun i ↦ Nat.ofDigits b ((w i).map Fin.val)
  have hq : ∀ i, 0 < q i := fun i ↦ pow_pos (by omega) _
  have hpred : (fun n ↦ g n ≠ 0) =
      (fun n ↦ ∃ i, l (u (q i * n + s i)) ≠ 0) := by
    funext n
    apply propext
    constructor
    · intro hn
      by_contra hnone
      push_neg at hnone
      apply hn
      funext i
      dsimp only [g]
      rw [linearWord_apply_digitRecurrence b T u hrec]
      exact hnone i
    · rintro ⟨i, hi⟩ hn
      apply hi
      have hz := congrFun hn i
      dsimp only [g] at hz
      rw [linearWord_apply_digitRecurrence b T u hrec] at hz
      exact hz
  have hfg : ∀ n, l (u n) ≠ 0 → g n ≠ 0 := by
    intro n hfn hgn
    apply hfn
    rw [hreconstruct]
    apply Finset.sum_eq_zero
    intro i hi
    have hgi : l (linearWord T (w i) (u n)) = 0 := by
      simpa only [g, Pi.zero_apply] using congrFun hgn i
    simp [hgi]
  have hzero_equiv :
      HasZeroPredicateDensity (fun n ↦ l (u n) ≠ 0) ↔
        HasZeroPredicateDensity (fun n ↦ g n ≠ 0) := by
    constructor
    · intro hz
      rw [hpred]
      exact hz.finite_affine_preimages q s hq
    · intro hz
      have gh := (linearDigit_sparse_geometry_equivalences b hb S g grec).1.mp hz
      exact (gh.mono hfg).toZeroPredicateDensity
  rw [hzero_equiv,
    linearDigit_density_zero_iff_reachable_annihilator b hb S g grec,
    linearDigit_annihilator_iff_zero_fiber b hb S g grec]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, fun n i ↦ ?_⟩
    have hword : linearWord S z (g n) = 0 := by
      rw [linearWord_apply_digitRecurrence b S g grec]
      exact hz n
    have hi := congrFun hword i
    rw [hvalue z n] at hi
    simpa only [Pi.zero_apply] using hi
  · rintro ⟨z, hz⟩
    refine ⟨z, fun n ↦ ?_⟩
    rw [← linearWord_apply_digitRecurrence b S g grec z n, hvalue]
    funext i
    exact hz n i

end FiniteModel

section FiniteDimensional

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- Every scalar output of a finite-dimensional linear digit recurrence has
the complete sparse/dense support dichotomy. -/
theorem scalarObservation_sparse_geometry_classification
    (b : ℕ) (hb : 2 ≤ b) (T : Fin b → Module.End K V) (u : ℕ → V)
    (hrec : ∀ n (r : Fin b), u (b * n + r.val) = T r (u n))
    (l : Module.Dual K V) :
    (HasZeroPredicateDensity (fun n ↦ l (u n) ≠ 0) ↔
      HasUniformRelativeHoles (fun n ↦ l (u n) ≠ 0)) ∧
    (HasZeroPredicateDensity (fun n ↦ l (u n) ≠ 0) ↔
      ∃ α : ℝ, α < 1 ∧
        HasUniformPowerIntervalBound α (fun n ↦ l (u n) ≠ 0)) ∧
    (HasZeroPredicateDensity (fun n ↦ l (u n) ≠ 0) ∨
      HasPositiveLowerPredicateDensity (fun n ↦ l (u n) ≠ 0)) ∧
    (HasPositiveLowerPredicateDensity (fun n ↦ l (u n) ≠ 0) ↔
      ¬HasZeroPredicateDensity (fun n ↦ l (u n) ≠ 0)) := by
  apply scalarObservation_sparse_geometry_of_finite_word_model b hb T u hrec l
  obtain ⟨d, w, a, C, _, hreconstruct, hclosed⟩ :=
    observableSpan_exists_finite_word_model T l
  exact ⟨d, w, a, C, hreconstruct, hclosed⟩

end FiniteDimensional
end IndependentZeroBlocks
