import SierpinskiFormal.ArtinianCoefficientDescent
import Mathlib.Algebra.LinearRecurrence
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Matrix.Kronecker

set_option autoImplicit false

/-!
# Matrix-power representations of polynomial recurrence observations

This file works over an arbitrary commutative ring.  It constructs a companion
matrix for every `LinearRecurrence.IsSolution`, and proves that scalar
matrix-power coefficients are closed under constants, addition, multiplication,
and multivariable-polynomial evaluation.  No invertibility hypothesis is used.
-/

noncomputable section

namespace IndependentZeroBlocks

open scoped Matrix Kronecker
open Finset

universe uR

/-- A finite scalar matrix-power realization of a sequence. -/
structure ScalarMatrixPowerRepresentation
    (R : Type uR) [CommRing R] (f : ℕ → R) where
  carrier : Type
  [fintype : Fintype carrier]
  [decidableEq : DecidableEq carrier]
  transition : Matrix carrier carrier R
  left : carrier → R
  seed : carrier → R
  coefficient : ∀ n, ∑ i, left i * ((transition ^ n).mulVec seed) i = f n

namespace ScalarMatrixPowerRepresentation

variable {R : Type uR} [CommRing R]

/-- The constant sequence as a one-state matrix system. -/
def const (c : R) : ScalarMatrixPowerRepresentation R (fun _ ↦ c) where
  carrier := Unit
  fintype := inferInstance
  decidableEq := inferInstance
  transition := 1
  left := fun _ ↦ c
  seed := fun _ ↦ 1
  coefficient := by
    intro n
    simp

/-- Block-diagonal sum of two transition matrices. -/
def sumTransition {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι ι R) (B : Matrix κ κ R) :
    Matrix (Sum ι κ) (Sum ι κ) R
  | Sum.inl i, Sum.inl j => A i j
  | Sum.inr i, Sum.inr j => B i j
  | _, _ => 0

/-- Sum of two state vectors on a disjoint-union state space. -/
def sumVector {ι κ : Type*} (x : ι → R) (y : κ → R) : Sum ι κ → R
  | Sum.inl i => x i
  | Sum.inr j => y j

@[simp] theorem sumTransition_mulVec_sumVector_left
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι ι R) (B : Matrix κ κ R) (x : ι → R) (y : κ → R)
    (i : ι) :
    (sumTransition A B).mulVec (sumVector x y) (Sum.inl i) = A.mulVec x i := by
  simp [Matrix.mulVec, dotProduct, sumTransition, sumVector]

@[simp] theorem sumTransition_mulVec_sumVector_right
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι ι R) (B : Matrix κ κ R) (x : ι → R) (y : κ → R)
    (j : κ) :
    (sumTransition A B).mulVec (sumVector x y) (Sum.inr j) = B.mulVec y j := by
  simp [Matrix.mulVec, dotProduct, sumTransition, sumVector]

theorem sumTransition_pow_mulVec
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι ι R) (B : Matrix κ κ R) (x : ι → R) (y : κ → R) (n : ℕ) :
    ((sumTransition A B) ^ n).mulVec (sumVector x y) =
      sumVector ((A ^ n).mulVec x) ((B ^ n).mulVec y) := by
  induction n with
  | zero =>
      simp only [pow_zero, Matrix.one_mulVec]
  | succ n ih =>
      rw [pow_succ', pow_succ', pow_succ', ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ih]
      ext i
      cases i <;> simp [sumVector]

/-- Scalar matrix coefficients are closed under pointwise addition. -/
def add {f g : ℕ → R}
    (D₁ : ScalarMatrixPowerRepresentation R f)
    (D₂ : ScalarMatrixPowerRepresentation R g) :
    ScalarMatrixPowerRepresentation R (fun n ↦ f n + g n) := by
  letI := D₁.fintype
  letI := D₁.decidableEq
  letI := D₂.fintype
  letI := D₂.decidableEq
  exact
    { carrier := Sum D₁.carrier D₂.carrier
      fintype := inferInstance
      decidableEq := inferInstance
      transition := sumTransition D₁.transition D₂.transition
      left := sumVector D₁.left D₂.left
      seed := sumVector D₁.seed D₂.seed
      coefficient := by
        intro n
        rw [sumTransition_pow_mulVec]
        simp only [sumVector, Fintype.sum_sum_type]
        rw [D₁.coefficient, D₂.coefficient] }

theorem kronecker_pow
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι ι R) (B : Matrix κ κ R) (n : ℕ) :
    (A ⊗ₖ B) ^ n = (A ^ n) ⊗ₖ (B ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ, pow_succ, ih, Matrix.mul_kronecker_mul]

theorem kronecker_mulVec
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι R) (B : Matrix κ κ R) (x : ι → R) (y : κ → R) :
    (A ⊗ₖ B).mulVec (fun ij ↦ x ij.1 * y ij.2) =
      fun ij ↦ A.mulVec x ij.1 * B.mulVec y ij.2 := by
  ext ij
  rcases ij with ⟨i₀, j₀⟩
  simp only [Matrix.mulVec, dotProduct]
  rw [show (Finset.univ : Finset (ι × κ)) = Finset.univ ×ˢ Finset.univ by
    ext; simp]
  simp only [Matrix.kronecker_apply, Finset.sum_product]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Scalar matrix coefficients are closed under pointwise multiplication,
using the Kronecker product. -/
def mul {f g : ℕ → R}
    (D₁ : ScalarMatrixPowerRepresentation R f)
    (D₂ : ScalarMatrixPowerRepresentation R g) :
    ScalarMatrixPowerRepresentation R (fun n ↦ f n * g n) := by
  letI := D₁.fintype
  letI := D₁.decidableEq
  letI := D₂.fintype
  letI := D₂.decidableEq
  exact
    { carrier := D₁.carrier × D₂.carrier
      fintype := inferInstance
      decidableEq := inferInstance
      transition := D₁.transition ⊗ₖ D₂.transition
      left := fun ij ↦ D₁.left ij.1 * D₂.left ij.2
      seed := fun ij ↦ D₁.seed ij.1 * D₂.seed ij.2
      coefficient := by
        intro n
        rw [kronecker_pow, kronecker_mulVec]
        simp only [← Finset.univ_product_univ, Finset.sum_product]
        calc
          _ = (∑ i, D₁.left i * ((D₁.transition ^ n).mulVec D₁.seed) i) *
              (∑ j, D₂.left j * ((D₂.transition ^ n).mulVec D₂.seed) j) := by
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro i hi
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j hj
                ring
          _ = f n * g n := by rw [D₁.coefficient, D₂.coefficient] }

/-- Simultaneous finite polynomial evaluation of represented sequences.  The
construction follows the `C`/addition/`P * Xᵢ` induction for multivariable
polynomials, so every existential witness is built from `const`, `add`, and
the Kronecker-product `mul`. -/
theorem mvPolynomial_family
    {I : Type*} {f : I → ℕ → R}
    (D : ∀ i, ScalarMatrixPowerRepresentation R (f i))
    (P : MvPolynomial I R) :
    Nonempty (ScalarMatrixPowerRepresentation R
      (fun n ↦ MvPolynomial.eval (fun i ↦ f i n) P)) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      exact ⟨by simpa only [MvPolynomial.eval_C] using const c⟩
  | add P Q hP hQ =>
      obtain ⟨DP⟩ := hP
      obtain ⟨DQ⟩ := hQ
      exact ⟨by simpa only [MvPolynomial.eval_add] using DP.add DQ⟩
  | mul_X P i hP =>
      obtain ⟨DP⟩ := hP
      let DX := D i
      exact ⟨by simpa only [MvPolynomial.eval_mul, MvPolynomial.eval_X] using
        ScalarMatrixPowerRepresentation.mul DP DX⟩

/-- A constant unary matrix word of length `n` is the `n`th matrix power. -/
theorem commRingMatrixWord_replicate_unit
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι R) (n : ℕ) :
    commRingMatrixWord (fun _ : Unit ↦ M) (List.replicate n ()) = M ^ n := by
  simp [commRingMatrixWord]

/-- Interface from a power representation to the project's scalar
matrix-word observation, specialized to the singleton alphabet. -/
theorem commRingMatrixCoefficient_replicate_unit
    {f : ℕ → R} (D : ScalarMatrixPowerRepresentation R f) (n : ℕ) :
    letI := D.fintype
    letI := D.decidableEq
    commRingMatrixCoefficient (fun _ : Unit ↦ D.transition)
      D.left D.seed (List.replicate n ()) = f n := by
  letI := D.fintype
  letI := D.decidableEq
  rw [commRingMatrixCoefficient, commRingMatrixWord_replicate_unit,
    D.coefficient]

/-- A common-state matrix-power realization of a finite family of scalar
sequences.  This is the interface consumed by unary Boolean density results. -/
structure Family (J : Type) (f : J → ℕ → R) where
  carrier : Type
  [fintype : Fintype carrier]
  [decidableEq : DecidableEq carrier]
  transition : J → Matrix carrier carrier R
  left : J → carrier → R
  seed : J → carrier → R
  coefficient : ∀ j n,
    ∑ i, left j i * (((transition j) ^ n).mulVec (seed j)) i = f j n

/-- Embed a transition matrix into one diagonal block of a dependent sum. -/
def familyTransition {J : Type} [DecidableEq J]
    {f : J → ℕ → R} (D : ∀ j, ScalarMatrixPowerRepresentation R (f j))
    (j : J) : Matrix (Σ k, (D k).carrier) (Σ k, (D k).carrier) R
  | ⟨k, a⟩, ⟨l, b⟩ =>
      if hk : k = j then
        if hl : l = j then (D j).transition (hk ▸ a) (hl ▸ b) else 0
      else 0

/-- The same vector embedding, with the actual represented family left
implicit in its sequence parameter. -/
def familyVector' {J : Type} [DecidableEq J]
    {f : J → ℕ → R} (D : ∀ j, ScalarMatrixPowerRepresentation R (f j))
    (j : J) (x : (D j).carrier → R) : (Σ k, (D k).carrier) → R
  | ⟨k, a⟩ => if h : k = j then x (h ▸ a) else 0

theorem familyTransition_mulVec_familyVector
    {J : Type} [Fintype J] [DecidableEq J]
    {f : J → ℕ → R} (D : ∀ j, ScalarMatrixPowerRepresentation R (f j))
    (j : J) (x : (D j).carrier → R) :
    letI : ∀ k, Fintype (D k).carrier := fun k ↦ (D k).fintype
    (familyTransition D j).mulVec (familyVector' D j x) =
      familyVector' D j ((D j).transition.mulVec x) := by
  letI : ∀ k, Fintype (D k).carrier := fun k ↦ (D k).fintype
  funext p
  rcases p with ⟨k, a⟩
  by_cases hk : k = j
  · subst k
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sigma]
    rw [Finset.sum_eq_single j]
    · simp [familyTransition, familyVector', Matrix.mulVec, dotProduct]
    · intro l hl hlj
      simp [familyTransition, familyVector', hlj]
    · simp
  · simp [Matrix.mulVec, dotProduct, familyTransition, familyVector', hk]

theorem familyTransition_pow_mulVec_familyVector
    {J : Type} [Fintype J] [DecidableEq J]
    {f : J → ℕ → R} (D : ∀ j, ScalarMatrixPowerRepresentation R (f j))
    (j : J) (x : (D j).carrier → R) (n : ℕ) :
    letI : ∀ k, Fintype (D k).carrier := fun k ↦ (D k).fintype
    letI : ∀ k, DecidableEq (D k).carrier := fun k ↦ (D k).decidableEq
    ((familyTransition D j) ^ n).mulVec (familyVector' D j x) =
      familyVector' D j (((D j).transition ^ n).mulVec x) := by
  letI : ∀ k, Fintype (D k).carrier := fun k ↦ (D k).fintype
  letI : ∀ k, DecidableEq (D k).carrier := fun k ↦ (D k).decidableEq
  induction n with
  | zero => simp only [pow_zero, Matrix.one_mulVec]
  | succ n ih =>
      rw [pow_succ', pow_succ', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        ih, familyTransition_mulVec_familyVector]

theorem sum_familyVector'_mul
    {J : Type} [Fintype J] [DecidableEq J]
    {f : J → ℕ → R} (D : ∀ j, ScalarMatrixPowerRepresentation R (f j))
    (j : J) (x y : (D j).carrier → R) :
    letI : ∀ k, Fintype (D k).carrier := fun k ↦ (D k).fintype
    ∑ p, familyVector' D j x p * familyVector' D j y p =
      ∑ i, x i * y i := by
  letI : ∀ k, Fintype (D k).carrier := fun k ↦ (D k).fintype
  simp only [Fintype.sum_sigma]
  rw [Finset.sum_eq_single j]
  · simp [familyVector']
  · intro k hk hkj
    simp [familyVector', hkj]
  · simp

/-- Pack dependent finite state spaces into the common finite state type
`Σ j, (D j).carrier`, preserving every scalar coefficient. -/
def packFamily {J : Type} [Fintype J] [DecidableEq J]
    {f : J → ℕ → R} (D : ∀ j, ScalarMatrixPowerRepresentation R (f j)) :
    Family J f := by
  letI : ∀ j, Fintype (D j).carrier := fun j ↦ (D j).fintype
  letI : ∀ j, DecidableEq (D j).carrier := fun j ↦ (D j).decidableEq
  exact
    { carrier := Σ j, (D j).carrier
      fintype := inferInstance
      decidableEq := inferInstance
      transition := familyTransition D
      left := fun j ↦ familyVector' D j (D j).left
      seed := fun j ↦ familyVector' D j (D j).seed
      coefficient := by
        intro j n
        rw [familyTransition_pow_mulVec_familyVector,
          sum_familyVector'_mul, (D j).coefficient] }

end ScalarMatrixPowerRepresentation

namespace LinearRecurrence

variable {R : Type uR} [CommRing R]

/-- The companion transition.  Rows below the last row shift the recurrence
window; the last row is the coefficient row. -/
def companionTransition (E : LinearRecurrence R) :
    Matrix (Fin E.order) (Fin E.order) R := fun i j ↦
  if h : i.val + 1 < E.order then
    if j = ⟨i.val + 1, h⟩ then 1 else 0
  else E.coeffs j

theorem companionTransition_mulVec_window
    (E : LinearRecurrence R) (u : ℕ → R) (hu : E.IsSolution u)
    (n : ℕ) (i : Fin E.order) :
    (companionTransition E).mulVec (fun j ↦ u (n + j.val)) i =
      u (n + 1 + i.val) := by
  by_cases h : i.val + 1 < E.order
  · simp only [Matrix.mulVec, dotProduct, companionTransition, dif_pos h]
    rw [Finset.sum_eq_single ⟨i.val + 1, h⟩]
    · simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    · intro j hj hne
      simp [hne]
    · simp
  · simp only [Matrix.mulVec, dotProduct, companionTransition, dif_neg h]
    rw [← hu n]
    congr 1
    omega

theorem companionTransition_pow_mulVec_initial
    (E : LinearRecurrence R) (u : ℕ → R) (hu : E.IsSolution u)
    (n : ℕ) (i : Fin E.order) :
    ((companionTransition E) ^ n).mulVec (fun j ↦ u j.val) i = u (n + i.val) := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec]
      have hstate : ((companionTransition E) ^ n).mulVec (fun j ↦ u j.val) =
          fun j ↦ u (n + j.val) := funext fun j ↦ ih j
      rw [hstate, companionTransition_mulVec_window E u hu]

/-- Every solution of a Mathlib linear recurrence over an arbitrary
commutative ring has an explicitly constructed finite companion-matrix
realization.  Order zero is handled by the forced zero sequence. -/
theorem exists_scalarMatrixPowerRepresentation
    (E : LinearRecurrence R) (u : ℕ → R) (hu : E.IsSolution u) :
    Nonempty (ScalarMatrixPowerRepresentation R u) := by
  cases horder : E.order with
  | zero =>
      have huzero : ∀ n, u n = 0 := by
        intro n
        calc
          u n = u (n + E.order) := by congr 1 <;> omega
          _ = ∑ i, E.coeffs i * u (n + i.val) := hu n
          _ = 0 := by
            apply Finset.sum_eq_zero
            intro i hi
            have := i.isLt
            omega
      have hfun : u = fun _ ↦ 0 := funext huzero
      rw [hfun]
      exact ⟨ScalarMatrixPowerRepresentation.const (0 : R)⟩
  | succ d =>
      let i0 : Fin E.order := ⟨0, by omega⟩
      exact ⟨
        { carrier := Fin E.order
          fintype := inferInstance
          decidableEq := inferInstance
          transition := companionTransition E
          left := fun i ↦ if i = i0 then 1 else 0
          seed := fun i ↦ u i.val
          coefficient := by
            intro n
            rw [Finset.sum_eq_single i0]
            · simp [companionTransition_pow_mulVec_initial E u hu, i0]
            · intro i hi hne
              simp [hne]
            · simp } ⟩

/-- A polynomial in any family of (independently specified) recurrence
solutions has a constructed scalar matrix-power realization. -/
theorem exists_mvPolynomial_scalarMatrixPowerRepresentation
    {I : Type*} (E : I → LinearRecurrence R) (u : I → ℕ → R)
    (hu : ∀ i, (E i).IsSolution (u i)) (P : MvPolynomial I R) :
    Nonempty (ScalarMatrixPowerRepresentation R
      (fun n ↦ MvPolynomial.eval (fun i ↦ u i n) P)) := by
  let D : ∀ i, ScalarMatrixPowerRepresentation R (u i) := fun i ↦
    Classical.choice (exists_scalarMatrixPowerRepresentation (E i) (u i) (hu i))
  exact ScalarMatrixPowerRepresentation.mvPolynomial_family D P

/-- A finite family of polynomial observations of independent recurrence
solutions can be packed into one common finite state type. -/
theorem exists_commonFamily_mvPolynomial_scalarMatrixPowerRepresentation
    {I : Type*} {m : ℕ} (E : I → LinearRecurrence R) (u : I → ℕ → R)
    (hu : ∀ i, (E i).IsSolution (u i)) (P : Fin m → MvPolynomial I R) :
    Nonempty (ScalarMatrixPowerRepresentation.Family (Fin m)
      (fun j n ↦ MvPolynomial.eval (fun i ↦ u i n) (P j))) := by
  let D : ∀ j, ScalarMatrixPowerRepresentation R
      (fun n ↦ MvPolynomial.eval (fun i ↦ u i n) (P j)) := fun j ↦
    Classical.choice
      (exists_mvPolynomial_scalarMatrixPowerRepresentation E u hu (P j))
  exact ⟨ScalarMatrixPowerRepresentation.packFamily D⟩

end LinearRecurrence

end IndependentZeroBlocks
