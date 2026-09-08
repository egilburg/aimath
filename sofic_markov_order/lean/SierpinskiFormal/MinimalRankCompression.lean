import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import SierpinskiFormal.ReachableSpanMortality
import SierpinskiFormal.CommRingObservationGeometry

set_option autoImplicit false

/-!
# Compression at a minimum-rank word

Products use the chronological list convention: the matrix of `x ++ y` is
the matrix of `x` multiplied on the right by the matrix of `y`.
-/

noncomputable section

open scoped BigOperators

namespace IndependentZeroBlocks

variable {F A ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]

/-- Chronological product of a matrix-labelled word. -/
def matrixWord (M : A → Matrix ι ι F) (w : List A) : Matrix ι ι F :=
  (w.map M).prod

@[simp] theorem matrixWord_nil (M : A → Matrix ι ι F) :
    matrixWord M [] = 1 := by
  simp [matrixWord]

@[simp] theorem matrixWord_append (M : A → Matrix ι ι F) (x y : List A) :
    matrixWord M (x ++ y) = matrixWord M x * matrixWord M y := by
  simp [matrixWord]

/-- Every square matrix over a field factors through a coordinate space whose
dimension is its matrix rank. -/
theorem exists_rankFactorization (H : Matrix ι ι F) :
    ∃ (U : Matrix ι (Fin H.rank) F)
      (V : Matrix (Fin H.rank) ι F), H = U * V := by
  let f : (ι → F) →ₗ[F] (ι → F) := H.mulVecLin
  let e : (Fin H.rank → F) ≃ₗ[F] LinearMap.range f :=
    LinearEquiv.ofFinrankEq _ _ (by
      simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
      rfl)
  let uLin : (Fin H.rank → F) →ₗ[F] (ι → F) :=
    (LinearMap.range f).subtype.comp e.toLinearMap
  let vLin : (ι → F) →ₗ[F] (Fin H.rank → F) :=
    e.symm.toLinearMap.comp f.rangeRestrict
  let U : Matrix ι (Fin H.rank) F :=
    LinearMap.toMatrix (Pi.basisFun F (Fin H.rank))
      (Pi.basisFun F ι) uLin
  let V : Matrix (Fin H.rank) ι F :=
    LinearMap.toMatrix (Pi.basisFun F ι)
      (Pi.basisFun F (Fin H.rank)) vLin
  refine ⟨U, V, ?_⟩
  apply (Matrix.toLin (Pi.basisFun F ι)
    (Pi.basisFun F ι)).injective
  rw [Matrix.toLin_mul (Pi.basisFun F ι)
    (Pi.basisFun F (Fin H.rank)) (Pi.basisFun F ι)]
  simp only [U, V, Matrix.toLin_toMatrix]
  rw [Matrix.toLin_eq_toLin', Matrix.toLin'_apply']
  change f = uLin.comp vLin
  ext x
  simp [uLin, vLin, e, f]

/-- The matrix obtained by compressing a word between a fixed factorization
of the reset matrix. -/
def returnMatrix {r : ℕ} (M : A → Matrix ι ι F)
    (U : Matrix ι (Fin r) F) (V : Matrix (Fin r) ι F)
    (y : List A) : Matrix (Fin r) (Fin r) F :=
  V * matrixWord M y * U

/-- Full rank of a square matrix over a field implies that it is a unit. -/
theorem isUnit_of_rank_eq_card {n : Type*} [Fintype n] [DecidableEq n]
    (K : Matrix n n F) (hK : K.rank = Fintype.card n) : IsUnit K := by
  rw [← Matrix.mulVec_surjective_iff_isUnit]
  change Function.Surjective K.mulVecLin
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  simpa [Matrix.rank, Module.finrank_fintype_fun_eq_card] using hK

/-- A nonzero finite square matrix over a field has positive matrix rank. -/
theorem rank_pos_of_ne_zero (H : Matrix ι ι F) (hH : H ≠ 0) : 0 < H.rank := by
  apply Nat.pos_of_ne_zero
  intro hrank
  apply hH
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_apply', Matrix.toLin'_apply']
  have hrange : LinearMap.range H.mulVecLin = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    simpa only [Matrix.rank] using hrank
  have hlin : H.mulVecLin = 0 := LinearMap.range_eq_bot.mp hrange
  simpa only [Matrix.mulVecLin_zero] using hlin

omit [DecidableEq ι] in
/-- If `H X H` cannot fall below rank `r`, then the compression of `X`
through any `r`-coordinate factorization `H = U V` is invertible.  These
hypotheses already force the relevant full-rank facts; no global semigroup
hypothesis is needed. -/
theorem sandwich_isUnit_of_rank_lower_bound {r : ℕ}
    (U : Matrix ι (Fin r) F) (V : Matrix (Fin r) ι F)
    (H X : Matrix ι ι F)
    (hfac : H = U * V) (hlower : r ≤ (H * X * H).rank) :
    IsUnit (V * X * U) := by
  let K : Matrix (Fin r) (Fin r) F := V * X * U
  have hsandwich : H * X * H = U * K * V := by
    simp only [K, hfac, Matrix.mul_assoc]
  have hle : (H * X * H).rank ≤ K.rank := by
    rw [hsandwich]
    exact (Matrix.rank_mul_le_left (U * K) V).trans
      (Matrix.rank_mul_le_right U K)
  have hfull : K.rank = r := by
    apply Nat.le_antisymm
    · exact K.rank_le_width
    · exact hlower.trans hle
  apply isUnit_of_rank_eq_card K
  simpa using hfull

/-- A positive lower rank for every nonempty product makes every return
compression at a nonempty reset word invertible. -/
theorem returnMatrix_isUnit_of_minRank {r : ℕ}
    (M : A → Matrix ι ι F) (h : List A)
    (U : Matrix ι (Fin r) F) (V : Matrix (Fin r) ι F)
    (hfac : matrixWord M h = U * V) (hh : h ≠ [])
    (hmin : ∀ w : List A, w ≠ [] → r ≤ (matrixWord M w).rank)
    (y : List A) : IsUnit (returnMatrix M U V y) := by
  apply sandwich_isUnit_of_rank_lower_bound U V (matrixWord M h)
    (matrixWord M y) hfac
  simpa only [← matrixWord_append, List.append_assoc] using
    hmin (h ++ y ++ h) (by simp [hh])

/-- A chosen minimum-rank nonempty word supplies its own rank-sized
factorization and invertible return matrices; no factorization data is an
external hypothesis in this package. -/
theorem exists_minRankCompression
    (M : A → Matrix ι ι F) (h : List A) (hh : h ≠ [])
    (hmin : ∀ w : List A, w ≠ [] →
      (matrixWord M h).rank ≤ (matrixWord M w).rank) :
    ∃ (U : Matrix ι (Fin (matrixWord M h).rank) F)
      (V : Matrix (Fin (matrixWord M h).rank) ι F),
      matrixWord M h = U * V ∧
        ∀ y : List A, IsUnit (returnMatrix M U V y) := by
  obtain ⟨U, V, hfac⟩ := exists_rankFactorization (matrixWord M h)
  refine ⟨U, V, hfac, fun y ↦ ?_⟩
  exact returnMatrix_isUnit_of_minRank M h U V hfac hh hmin y

/-- No zero nonempty word product automatically supplies a positive-rank
minimum word and its rank-sized reversible compression. -/
theorem exists_positive_minRankCompression [Nonempty A]
    (M : A → Matrix ι ι F)
    (hnonzero : ∀ w : List A, w ≠ [] → matrixWord M w ≠ 0) :
    ∃ h : List A, h ≠ [] ∧ 0 < (matrixWord M h).rank ∧
      (∀ w : List A, w ≠ [] →
        (matrixWord M h).rank ≤ (matrixWord M w).rank) ∧
      ∃ (U : Matrix ι (Fin (matrixWord M h).rank) F)
        (V : Matrix (Fin (matrixWord M h).rank) ι F),
        matrixWord M h = U * V ∧
          ∀ y : List A, IsUnit (returnMatrix M U V y) := by
  let ranks : Set ℕ := {n | ∃ w : List A, w ≠ [] ∧ (matrixWord M w).rank = n}
  have hranks : ranks.Nonempty := by
    let a : A := Classical.choice inferInstance
    exact ⟨(matrixWord M [a]).rank, [a], by simp, rfl⟩
  obtain ⟨h, hh, hhrank⟩ := Nat.sInf_mem hranks
  have hmin : ∀ w : List A, w ≠ [] →
      (matrixWord M h).rank ≤ (matrixWord M w).rank := by
    intro w hw
    rw [hhrank]
    exact Nat.sInf_le ⟨w, hw, rfl⟩
  obtain ⟨U, V, hfac, hunit⟩ := exists_minRankCompression M h hh hmin
  exact ⟨h, hh, rank_pos_of_ne_zero _ (hnonzero h hh), hmin,
    U, V, hfac, hunit⟩

/-- Return matrices multiply by inserting the reset word. -/
theorem returnMatrix_mul {r : ℕ}
    (M : A → Matrix ι ι F) (h : List A)
    (U : Matrix ι (Fin r) F) (V : Matrix (Fin r) ι F)
    (hfac : matrixWord M h = U * V) (y z : List A) :
    returnMatrix M U V y * returnMatrix M U V z =
      returnMatrix M U V (y ++ h ++ z) := by
  simp only [returnMatrix, matrixWord_append, hfac]
  simp only [Matrix.mul_assoc]

/-- The word consisting of an initial reset, then each supplied gap followed
by another reset. -/
def resetSandwichWord (h : List A) : List (List A) → List A
  | [] => h
  | y :: ys => h ++ y ++ resetSandwichWord h ys

@[simp] theorem matrixWord_resetSandwichWord {r : ℕ}
    (M : A → Matrix ι ι F) (h : List A)
    (U : Matrix ι (Fin r) F) (V : Matrix (Fin r) ι F)
    (hfac : matrixWord M h = U * V) (ys : List (List A)) :
    matrixWord M (resetSandwichWord h ys) =
      U * (ys.map (returnMatrix M U V)).prod * V := by
  induction ys with
  | nil => simp [resetSandwichWord, hfac]
  | cons y ys ih =>
      simp only [resetSandwichWord, matrixWord_append, hfac, ih,
        List.map_cons, List.prod_cons, returnMatrix]
      simp only [Matrix.mul_assoc]

/-- Whole-matrix compression between arbitrary boundary words. -/
theorem matrixWord_boundary_resetSandwichWord {r : ℕ}
    (M : A → Matrix ι ι F) (h x z : List A)
    (U : Matrix ι (Fin r) F) (V : Matrix (Fin r) ι F)
    (hfac : matrixWord M h = U * V) (ys : List (List A)) :
    matrixWord M (x ++ resetSandwichWord h ys ++ z) =
      matrixWord M x * U * (ys.map (returnMatrix M U V)).prod *
        V * matrixWord M z := by
  rw [matrixWord_append, matrixWord_append,
    matrixWord_resetSandwichWord M h U V hfac]
  simp only [Matrix.mul_assoc]

/-- Scalar form of the multiple-return compression. -/
theorem coefficient_boundary_resetSandwichWord {r : ℕ}
    (M : A → Matrix ι ι F) (h x z : List A)
    (U : Matrix ι (Fin r) F) (V : Matrix (Fin r) ι F)
    (hfac : matrixWord M h = U * V) (ys : List (List A))
    (lambda gamma : ι → F) :
    coordinateRowDual lambda
        ((matrixWord M (x ++ resetSandwichWord h ys ++ z)).mulVec gamma) =
      coordinateRowDual lambda
        ((matrixWord M x * U).mulVec
          ((ys.map (returnMatrix M U V)).prod |>.mulVec
            ((V * matrixWord M z).mulVec gamma))) := by
  rw [matrixWord_boundary_resetSandwichWord M h x z U V hfac ys]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

end IndependentZeroBlocks
