import SierpinskiFormal.BooleanDoubleLimitClosure
import Mathlib.RingTheory.Finiteness.Cardinality

set_option autoImplicit false

/-!
# Matrix-word representations of finite modules

A finite module over a commutative ring is a quotient of a finite free module.
Choosing preimages of the finitely many images of its generators produces
coordinate matrices.  The choices need not define a linear section, and no
matrix is asserted to be invertible.
-/

noncomputable section

namespace IndependentZeroBlocks

open scoped BigOperators

variable {K V A : Type*} [CommRing K] [AddCommGroup V] [Module K V]

/-- A finite module has a finite free cover on which any family of
endomorphisms, seed, and scalar observation can be lifted compatibly.  The
cover is only required to be surjective; the lifted matrices need not be
invertible even when the original endomorphisms are automorphisms. -/
theorem finiteModule_exists_coordinate_lift [Module.Finite K V]
    (T : A → Module.End K V) (l : Module.Dual K V) (v : V) :
    ∃ (d : ℕ) (π : (Fin d → K) →ₗ[K] V)
      (M : A → Matrix (Fin d) (Fin d) K) (u a : Fin d → K),
      Function.Surjective π ∧
      π u = v ∧
      (∀ r x, π (Matrix.mulVecLin (M r) x) = T r (π x)) ∧
      (∀ x, coordinateRowDual a x = l (π x)) := by
  classical
  obtain ⟨d, e, he⟩ := Module.Finite.exists_fin (R := K) (M := V)
  let π : (Fin d → K) →ₗ[K] V := Fintype.linearCombination K e
  have hπ : Function.Surjective π := by
    apply LinearMap.range_eq_top.mp
    simpa [π] using he
  choose lift hlift using hπ
  let basisVector : Fin d → (Fin d → K) := fun j ↦ Pi.single j 1
  let M : A → Matrix (Fin d) (Fin d) K :=
    fun r i j ↦ lift (T r (π (basisVector j))) i
  let u : Fin d → K := lift v
  let a : Fin d → K := fun i ↦ l (π (basisVector i))
  refine ⟨d, π, M, u, a, (fun y ↦ ⟨lift y, hlift y⟩), hlift v, ?_, ?_⟩
  · intro r x
    have hx : x = ∑ j, x j • basisVector j := by
      funext i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single i]
      · simp [basisVector]
      · intro j hj hji
        simp [basisVector, Pi.single_apply, hji]
      · intro hi
        exact (hi (Finset.mem_univ i)).elim
    calc
      π (Matrix.mulVecLin (M r) x) =
          π (∑ j, x j • lift (T r (π (basisVector j)))) := by
            congr 1
            funext i
            rw [Matrix.mulVecLin_apply]
            simp only [Matrix.mulVec, dotProduct,
              Finset.sum_apply, Pi.smul_apply, smul_eq_mul, M]
            apply Finset.sum_congr rfl
            intro j hj
            exact mul_comm _ _
      _ = ∑ j, x j • π (lift (T r (π (basisVector j)))) := by
            simp
      _ = ∑ j, x j • T r (π (basisVector j)) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [hlift]
      _ = T r (π (∑ j, x j • basisVector j)) := by
            simp
      _ = T r (π x) := by rw [← hx]
  · intro x
    have hx : x = ∑ i, x i • basisVector i := by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single j]
      · simp [basisVector]
      · intro i hi hij
        simp [basisVector, Pi.single_apply, hij]
      · intro hj
        exact (hj (Finset.mem_univ j)).elim
    rw [coordinateRowDual_apply]
    calc
      ∑ i, a i * x i = ∑ i, x i • l (π (basisVector i)) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [smul_eq_mul, a]
        exact mul_comm _ _
      _ = l (π (∑ i, x i • basisVector i)) := by simp
      _ = l (π x) := by rw [← hx]

/-- Every scalar observation of every word in endomorphisms of a finite
module is exactly a coefficient of finite coordinate matrices over the same
ring. -/
theorem finiteModule_exists_matrix_word_representation [Module.Finite K V]
    (T : A → Module.End K V) (l : Module.Dual K V) (v : V) :
    ∃ (d : ℕ) (M : A → Matrix (Fin d) (Fin d) K) (u a : Fin d → K),
      ∀ w : List A,
        coordinateRowDual a
            (linearWord (fun r ↦ Matrix.mulVecLin (M r)) w u) =
          l (linearWord T w v) := by
  obtain ⟨d, π, M, u, a, hπ, hu, hM, ha⟩ :=
    finiteModule_exists_coordinate_lift T l v
  refine ⟨d, M, u, a, ?_⟩
  intro w
  rw [ha]
  congr 1
  induction w with
  | nil => simpa using hu
  | cons r w ih =>
      rw [linearWord_cons, linearWord_cons, Module.End.mul_apply,
        Module.End.mul_apply, hM, ih]

/-- The nonzero support kernel of any finite-module word observation has the
sequential Boolean double-limit property. -/
theorem finiteModule_wordNonzeroBool_hasBooleanDoubleLimitProperty
    [Module.Finite K V] [Fintype A]
    (T : A → Module.End K V) (l : Module.Dual K V) (v : V) :
    HasBooleanDoubleLimitProperty
      (fun x y : List A ↦ nonzeroBool (l (linearWord T (x ++ y) v))) := by
  obtain ⟨d, M, u, a, hrepr⟩ :=
    finiteModule_exists_matrix_word_representation T l v
  let e : A ≃ Fin (Fintype.card A) := Fintype.equivFin A
  let M' : Fin (Fintype.card A) → Matrix (Fin d) (Fin d) K :=
    fun i ↦ M (e.symm i)
  have hstate (w : List A) :
      linearWord (fun i ↦ Matrix.mulVecLin (M' i)) (w.map e) u =
        linearWord (fun r ↦ Matrix.mulVecLin (M r)) w u := by
    induction w with
    | nil => simp
    | cons r w ih =>
        simp only [List.map_cons, linearWord_cons, Module.End.mul_apply, ih]
        simp [M', e]
  have hkernel (p q : List A) :
      matrixWordsNonzeroBool M' u a (p.map e) (q.map e) =
        nonzeroBool (l (linearWord T (p ++ q) v)) := by
    rw [matrixWordsNonzeroBool, ← List.map_append, hstate, hrepr]
  have h := matrixWordsNonzeroBool_hasBooleanDoubleLimitProperty M' u a
  intro x y rowLimit columnLimit rowOuter columnOuter
    hrow hcolumn hrowOuter hcolumnOuter
  apply h (fun i ↦ (x i).map e) (fun j ↦ (y j).map e)
    rowLimit columnLimit rowOuter columnOuter
  · simpa only [hkernel] using hrow
  · simpa only [hkernel] using hcolumn
  · exact hrowOuter
  · exact hcolumnOuter

end IndependentZeroBlocks
