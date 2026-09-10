import FiniteMonoidMortality.FiniteDimensionDetection
import FiniteMonoidMortality.MinimalRankCompression
import FiniteMonoidMortality.ReachableSpanMortality
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace

set_option autoImplicit false

noncomputable section

namespace FiniteMonoidMortality

def symmetricMatrixSubmodule (n : ℕ) :
    Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) where
  carrier := {X | X.IsSymm}
  zero_mem' := Matrix.isSymm_zero
  add_mem' := fun hX hY => hX.add hY
  smul_mem' := fun c _ hX => hX.smul c

abbrev SymmetricMatrix (n : ℕ) := symmetricMatrixSubmodule n

def matrixOfSym2Coords {n : ℕ} (q : Sym2 (Fin n) → ℝ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => q s(i, j)

theorem matrixOfSym2Coords_isSymm {n : ℕ} (q : Sym2 (Fin n) → ℝ) :
    (matrixOfSym2Coords q).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  exact congrArg q Sym2.eq_swap

def sym2CoordsOfMatrix {n : ℕ} (X : SymmetricMatrix n) : Sym2 (Fin n) → ℝ :=
  Sym2.lift ⟨X.1, fun i j => (X.2.apply i j).symm⟩

def symmetricMatrixEquivSym2 (n : ℕ) :
    SymmetricMatrix n ≃ₗ[ℝ] (Sym2 (Fin n) → ℝ) where
  toFun := sym2CoordsOfMatrix
  invFun q := ⟨matrixOfSym2Coords q, matrixOfSym2Coords_isSymm q⟩
  left_inv X := by
    apply Subtype.ext
    ext i j
    rfl
  right_inv q := by
    funext p
    induction p using Sym2.ind with
    | _ i j => rfl
  map_add' X Y := by
    funext p
    induction p using Sym2.ind with
    | _ i j => rfl
  map_smul' c X := by
    funext p
    induction p using Sym2.ind with
    | _ i j => rfl

theorem finrank_symmetricMatrix (n : ℕ) :
    Module.finrank ℝ (SymmetricMatrix n) = n * (n + 1) / 2 := by
  rw [LinearEquiv.finrank_eq (symmetricMatrixEquivSym2 n)]
  rw [Module.finrank_fintype_fun_eq_card, Sym2.card, Fintype.card_fin,
    Nat.choose_two_right]
  simp only [Nat.add_sub_cancel]
  rw [Nat.mul_comm]

def symmetricConjugate {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.IsSymm) : SymmetricMatrix n :=
  ⟨P * X * P.transpose, by
    change (P * X * P.transpose).transpose = P * X * P.transpose
    rw [Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, hX.eq]
    simp only [Matrix.mul_assoc]⟩

@[simp] theorem symmetricConjugate_coe {n : ℕ}
    (P X : Matrix (Fin n) (Fin n) ℝ) (hX : X.IsSymm) :
    (symmetricConjugate P X hX : Matrix (Fin n) (Fin n) ℝ) =
      P * X * P.transpose := rfl

def symmetricConjugateEnd {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) :
    Module.End ℝ (SymmetricMatrix n) where
  toFun X := symmetricConjugate P X.1 X.2
  map_add' X Y := by
    apply Subtype.ext
    change P * ((X + Y : SymmetricMatrix n) : Matrix (Fin n) (Fin n) ℝ) * P.transpose =
      P * (X : Matrix (Fin n) (Fin n) ℝ) * P.transpose +
        P * (Y : Matrix (Fin n) (Fin n) ℝ) * P.transpose
    rw [Submodule.coe_add]
    rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by
    apply Subtype.ext
    change P * ((c • X : SymmetricMatrix n) : Matrix (Fin n) (Fin n) ℝ) * P.transpose =
      c • (P * (X : Matrix (Fin n) (Fin n) ℝ) * P.transpose)
    rw [Submodule.coe_smul]
    rw [Matrix.mul_smul, Matrix.smul_mul]

abbrev QuadraticObservationState (n : ℕ) := ℝ × SymmetricMatrix n

def quadraticObservationLetter {A : Type*} {n : ℕ}
    (M : A → Matrix (Fin n) (Fin n) ℝ) (a : A) :
    Module.End ℝ (QuadraticObservationState n) where
  toFun z := (z.1, symmetricConjugateEnd (M a) z.2)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

theorem linearWord_quadraticObservationLetter {A : Type*} {n : ℕ}
    (M : A → Matrix (Fin n) (Fin n) ℝ) (c : ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) (w : List A) :
    linearWord (quadraticObservationLetter M) w (c, ⟨B, hB⟩) =
      (c, symmetricConjugate (matrixWord M w) B hB) := by
  induction w with
  | nil =>
      simp [symmetricConjugate]
  | cons a w ih =>
      rw [linearWord_cons, Module.End.mul_apply, ih]
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        simp only [quadraticObservationLetter, symmetricConjugateEnd,
          symmetricConjugate_coe]
        simp [matrixWord, Matrix.transpose_mul, Matrix.mul_assoc]

end FiniteMonoidMortality
