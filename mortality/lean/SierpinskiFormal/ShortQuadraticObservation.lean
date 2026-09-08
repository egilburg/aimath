import SierpinskiFormal.FiniteDimensionDetection
import SierpinskiFormal.MinimalRankCompression
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace

set_option autoImplicit false

/-!
# Short witnesses for quadratic matrix observations

A symmetric `n × n` matrix has `n(n+1)/2` independent entries. Adjoining a
constant coordinate turns an affine quadratic observation into a linear one;
the finite-word reachable-span theorem then gives a witness of length at most
`n(n+1)/2`.
-/

noncomputable section

namespace IndependentZeroBlocks

/-- The real vector space of symmetric `n × n` matrices. -/
def symmetricMatrixSubmodule (n : ℕ) :
    Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) where
  carrier := {X | X.IsSymm}
  zero_mem' := Matrix.isSymm_zero
  add_mem' := fun hX hY => hX.add hY
  smul_mem' := fun c _ hX => hX.smul c

/-- Symmetric matrices, as a bundled vector space. -/
abbrev SymmetricMatrix (n : ℕ) := symmetricMatrixSubmodule n

/-- Reconstruct a symmetric matrix from its entries indexed by unordered pairs. -/
def matrixOfSym2Coords {n : ℕ} (q : Sym2 (Fin n) → ℝ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => q s(i, j)

@[simp] theorem matrixOfSym2Coords_apply {n : ℕ} (q : Sym2 (Fin n) → ℝ)
    (i j : Fin n) : matrixOfSym2Coords q i j = q s(i, j) := rfl

theorem matrixOfSym2Coords_isSymm {n : ℕ} (q : Sym2 (Fin n) → ℝ) :
    (matrixOfSym2Coords q).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  exact congrArg q Sym2.eq_swap

/-- Read the entries of a symmetric matrix on unordered pairs. -/
def sym2CoordsOfMatrix {n : ℕ} (X : SymmetricMatrix n) : Sym2 (Fin n) → ℝ :=
  Sym2.lift ⟨X.1, fun i j => (X.2.apply i j).symm⟩

@[simp] theorem sym2CoordsOfMatrix_mk {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℝ) (hX : X.IsSymm) (i j : Fin n) :
    sym2CoordsOfMatrix ⟨X, hX⟩ s(i, j) = X i j := rfl

/-- Linear coordinates for symmetric matrices, indexed by unordered pairs. -/
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

/-- The exact number of independent entries in a real symmetric matrix. -/
theorem finrank_symmetricMatrix (n : ℕ) :
    Module.finrank ℝ (SymmetricMatrix n) = n * (n + 1) / 2 := by
  rw [LinearEquiv.finrank_eq (symmetricMatrixEquivSym2 n)]
  rw [Module.finrank_fintype_fun_eq_card, Sym2.card, Fintype.card_fin,
    Nat.choose_two_right]
  simp only [Nat.add_sub_cancel]
  rw [Nat.mul_comm]

/-- Congruence by `P`, bundled as a symmetric matrix. -/
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

/-- The linear action `X ↦ P X Pᵀ` on symmetric matrices. -/
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

/-- The affine observation state: a fixed scalar and a symmetric matrix. -/
abbrev QuadraticObservationState (n : ℕ) := ℝ × SymmetricMatrix n

/-- A digit fixes the scalar coordinate and acts by matrix congruence. -/
def quadraticObservationDigit {A : Type*} {n : ℕ}
    (M : A → Matrix (Fin n) (Fin n) ℝ) (a : A) :
    Module.End ℝ (QuadraticObservationState n) where
  toFun z := (z.1, symmetricConjugateEnd (M a) z.2)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

/-- Exact evaluation of the lifted orbit. The chronological convention for
`matrixWord` agrees with the fact that `linearWord` prepends endomorphisms. -/
theorem linearWord_quadraticObservationDigit {A : Type*} {n : ℕ}
    (M : A → Matrix (Fin n) (Fin n) ℝ) (c : ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm) (w : List A) :
    linearWord (quadraticObservationDigit M) w (c, ⟨B, hB⟩) =
      (c, symmetricConjugate (matrixWord M w) B hB) := by
  induction w with
  | nil =>
      simp [symmetricConjugate]
  | cons a w ih =>
      rw [linearWord_cons, Module.End.mul_apply, ih]
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        simp only [quadraticObservationDigit, symmetricConjugateEnd,
          symmetricConjugate_coe]
        simp [matrixWord, Matrix.transpose_mul, Matrix.mul_assoc]

/-- If an affine quadratic observation is nonzero somewhere in the word
orbit, it is already nonzero on a word of length at most `n(n+1)/2`. -/
theorem exists_short_quadratic_observation_ne_zero
    {A : Type*} {n : ℕ} (M : A → Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm)
    (ell : Module.Dual ℝ (SymmetricMatrix n)) (c : ℝ)
    (h : ∃ w : List A, c - ell (symmetricConjugate (matrixWord M w) B hB) ≠ 0) :
    ∃ w : List A, w.length ≤ n * (n + 1) / 2 ∧
      c - ell (symmetricConjugate (matrixWord M w) B hB) ≠ 0 := by
  let T := quadraticObservationDigit M
  let seed : QuadraticObservationState n := (c, ⟨B, hB⟩)
  let obs : Module.Dual ℝ (QuadraticObservationState n) :=
    LinearMap.fst ℝ ℝ (SymmetricMatrix n) -
      ell.comp (LinearMap.snd ℝ ℝ (SymmetricMatrix n))
  obtain ⟨long, hlong⟩ := h
  have horbit : obs (linearWord T long seed) ≠ 0 := by
    simpa [T, seed, obs, linearWord_quadraticObservationDigit] using hlong
  have hmem := linearWord_mem_linearReachableSpan T seed long
  rw [← boundedLinearOrbitSpan_finrank_eq_reachable T seed] at hmem
  by_contra hshort
  push Not at hshort
  have hzero : ∀ x ∈ boundedLinearOrbitSpan T seed
      (Module.finrank ℝ (QuadraticObservationState n)), obs x = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨w, rfl⟩ := hx
        have hwle : w.1.length ≤ n * (n + 1) / 2 := by
          have hwlt := w.2
          simp [QuadraticObservationState, finrank_symmetricMatrix] at hwlt
          omega
        have hwzero := hshort w.1 hwle
        simpa [T, seed, obs, linearWord_quadraticObservationDigit] using hwzero
    | zero => simp
    | add x y hx hy ihx ihy => simp [map_add, ihx, ihy]
    | smul a x hx ih => simp [map_smul, ih]
  exact horbit (hzero _ hmem)

/-- Restrict a linear functional on all matrices to symmetric matrices. -/
def symmetricMatrixDualOfMatrixDual {n : ℕ}
    (ell : Module.Dual ℝ (Matrix (Fin n) (Fin n) ℝ)) :
    Module.Dual ℝ (SymmetricMatrix n) :=
  ell.comp (symmetricMatrixSubmodule n).subtype

@[simp] theorem symmetricMatrixDualOfMatrixDual_apply {n : ℕ}
    (ell : Module.Dual ℝ (Matrix (Fin n) (Fin n) ℝ))
    (X : SymmetricMatrix n) :
    symmetricMatrixDualOfMatrixDual ell X = ell (X : Matrix (Fin n) (Fin n) ℝ) := rfl

/-- Matrix-space wrapper for `exists_short_quadratic_observation_ne_zero`.
This is convenient when the observation (for example, a trace sandwich) is
already defined linearly on all matrices. -/
theorem exists_short_quadratic_observation_matrixDual_ne_zero
    {A : Type*} {n : ℕ} (M : A → Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.IsSymm)
    (ell : Module.Dual ℝ (Matrix (Fin n) (Fin n) ℝ)) (c : ℝ)
    (h : ∃ w : List A,
      c - ell (matrixWord M w * B * (matrixWord M w).transpose) ≠ 0) :
    ∃ w : List A, w.length ≤ n * (n + 1) / 2 ∧
      c - ell (matrixWord M w * B * (matrixWord M w).transpose) ≠ 0 := by
  have h' : ∃ w : List A,
      c - symmetricMatrixDualOfMatrixDual ell
        (symmetricConjugate (matrixWord M w) B hB) ≠ 0 := by
    simpa using h
  obtain ⟨w, hwlen, hw⟩ := exists_short_quadratic_observation_ne_zero
    M B hB (symmetricMatrixDualOfMatrixDual ell) c h'
  exact ⟨w, hwlen, by simpa using hw⟩

/-- The trace sandwich `X ↦ trace (V X Vᵀ)` as a linear functional on
square matrices. The row index of `V` may be any finite type. -/
def traceSandwichMatrixDual {n : ℕ} {κ : Type*} [Fintype κ]
    (V : Matrix κ (Fin n) ℝ) :
    Module.Dual ℝ (Matrix (Fin n) (Fin n) ℝ) where
  toFun X := Matrix.trace (V * X * V.transpose)
  map_add' X Y := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]
  map_smul' c X := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul]
    rfl

@[simp] theorem traceSandwichMatrixDual_apply {n : ℕ} {κ : Type*} [Fintype κ]
    (V : Matrix κ (Fin n) ℝ) (X : Matrix (Fin n) (Fin n) ℝ) :
    traceSandwichMatrixDual V X = Matrix.trace (V * X * V.transpose) := rfl

end IndependentZeroBlocks
