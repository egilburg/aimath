import SierpinskiFormal.MatrixSparseGeometry

set_option autoImplicit false
namespace IndependentZeroBlocks
open SierpinskiFormal
open scoped BigOperators

/-- A reachable-span certificate can be tested on all actual states. -/
theorem linearDigit_annihilator_iff_zero_fiber
    {K V : Type*} [Semiring K] [AddCommMonoid V] [Module K V]
    (b : ℕ) (hb : 2 ≤ b) (T : Fin b → Module.End K V) (u : ℕ → V)
    (hrec : ∀ n (r : Fin b), u (b * n + r.val) = T r (u n)) :
    (∃ w : List (Fin b), ∀ x ∈ linearReachableSpan T (u 0), linearWord T w x = 0) ↔
      ∃ w : List (Fin b), ∀ n,
        u (b ^ w.length * n + Nat.ofDigits b (w.map Fin.val)) = 0 := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w, fun n => ?_⟩
    rw [← linearWord_apply_digitRecurrence b T u hrec w n]
    exact hw _ (linearDigit_state_mem_reachableSpan b hb T u hrec n)
  · rintro ⟨w, hw⟩
    refine ⟨w, ?_⟩
    have hle : linearReachableSpan T (u 0) ≤ LinearMap.ker (linearWord T w) := by
      apply Submodule.span_le.mpr
      rintro x ⟨v, rfl⟩
      change linearWord T w (linearWord T v (u 0)) = 0
      rw [linearWord_apply_digitRecurrence_seed b T u hrec v,
        linearWord_apply_digitRecurrence b T u hrec w]
      exact hw _
    exact fun x hx => hle hx

/-- The certificate is intrinsically a common zero window along one padded
digit fiber, independently of the ambient coefficient ring. -/
theorem polynomialMatrix_certificate_iff_zero_window_fiber
    {K ι : Type*} [CommRing K] [Fintype ι]
    (B : ι → ι → Polynomial K) (U : ι → PowerSeries K)
    (b : ℕ) (hb : 2 ≤ b)
    (hEq : ∀ i, U i = ∑ j, (B i j : PowerSeries K) * dilate b (U j)) :
    PolynomialMatrixSparseCertificate B U b ↔
      ∃ w : List (Fin b), ∀ n,
        matrixWindowState U (polynomialDilationWindowThreshold B b)
          (b ^ w.length * n + Nat.ofDigits b (w.map Fin.val)) = 0 := by
  exact linearDigit_annihilator_iff_zero_fiber b hb _ _
    (matrixWindowEnd_recurrence B U b hb hEq)

end IndependentZeroBlocks
