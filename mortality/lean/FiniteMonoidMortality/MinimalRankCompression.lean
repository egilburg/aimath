import FiniteMonoidMortality.ReachableSpanMortality
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace FiniteMonoidMortality

variable {F A ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]

def matrixWord {R : Type*} [Semiring R] (M : A → Matrix ι ι R) (w : List A) : Matrix ι ι R :=
  (w.map M).prod

@[simp] theorem matrixWord_nil (M : A → Matrix ι ι F) :
    matrixWord M [] = 1 := by
  simp [matrixWord]

@[simp] theorem matrixWord_append (M : A → Matrix ι ι F) (x y : List A) :
    matrixWord M (x ++ y) = matrixWord M x * matrixWord M y := by
  simp [matrixWord]

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

def compressedReturn {r : ℕ} (M : A → Matrix ι ι F)
    (U : Matrix ι (Fin r) F) (V : Matrix (Fin r) ι F)
    (y : List A) : Matrix (Fin r) (Fin r) F :=
  V * matrixWord M y * U

theorem isUnit_of_rank_eq_card {n : Type*} [Fintype n] [DecidableEq n]
    (K : Matrix n n F) (hK : K.rank = Fintype.card n) : IsUnit K := by
  rw [← Matrix.mulVec_surjective_iff_isUnit]
  change Function.Surjective K.mulVecLin
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  simpa [Matrix.rank, Module.finrank_fintype_fun_eq_card] using hK

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

theorem compressedReturn_mul {r : ℕ}
    (M : A → Matrix ι ι F) (h : List A)
    (U : Matrix ι (Fin r) F) (V : Matrix (Fin r) ι F)
    (hfac : matrixWord M h = U * V) (y z : List A) :
    compressedReturn M U V y * compressedReturn M U V z =
      compressedReturn M U V (y ++ h ++ z) := by
  simp only [compressedReturn, matrixWord_append, hfac]
  simp only [Matrix.mul_assoc]

end FiniteMonoidMortality
