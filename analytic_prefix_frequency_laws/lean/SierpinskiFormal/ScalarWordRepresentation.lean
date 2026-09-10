import SierpinskiFormal.PolynomialRecurrenceRepresentation

set_option autoImplicit false

/-!
# Finite scalar matrix-word representations

This file packages recognizable scalar-valued functions on words and proves
that they form an algebra under pointwise operations.  The alphabet is not
assumed finite: only the state space of each representation is finite.
-/

noncomputable section

namespace IndependentZeroBlocks

open scoped Matrix Kronecker
open Finset

universe uR uA

/-- A finite scalar matrix-word realization of a function on words. -/
structure ScalarWordRepresentation
    (R : Type uR) [CommRing R] (A : Type uA) (f : List A → R) where
  carrier : Type
  [fintype : Fintype carrier]
  [decidableEq : DecidableEq carrier]
  transition : A → Matrix carrier carrier R
  left : carrier → R
  seed : carrier → R
  coefficient : ∀ w, commRingMatrixCoefficient transition left seed w = f w

namespace ScalarWordRepresentation

variable {R : Type uR} [CommRing R] {A : Type uA}

/-- The constant word function as a one-state matrix system. -/
def const (c : R) : ScalarWordRepresentation R A (fun _ ↦ c) where
  carrier := Unit
  fintype := inferInstance
  decidableEq := inferInstance
  transition := fun _ ↦ 1
  left := fun _ ↦ c
  seed := fun _ ↦ 1
  coefficient := by
    intro w
    simp [commRingMatrixCoefficient, commRingMatrixWord]

/-- A block-diagonal word acts componentwise on a pair of state vectors. -/
theorem sumTransition_word_mulVec
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (M : A → Matrix ι ι R) (N : A → Matrix κ κ R)
    (x : ι → R) (y : κ → R) (w : List A) :
    (commRingMatrixWord (fun a ↦
        ScalarMatrixPowerRepresentation.sumTransition (M a) (N a)) w).mulVec
      (ScalarMatrixPowerRepresentation.sumVector x y) =
      ScalarMatrixPowerRepresentation.sumVector
        ((commRingMatrixWord M w).mulVec x)
        ((commRingMatrixWord N w).mulVec y) := by
  induction w with
  | nil =>
      change (1 : Matrix (Sum ι κ) (Sum ι κ) R).mulVec
          (ScalarMatrixPowerRepresentation.sumVector x y) =
        ScalarMatrixPowerRepresentation.sumVector
          ((1 : Matrix ι ι R).mulVec x) ((1 : Matrix κ κ R).mulVec y)
      rw [Matrix.one_mulVec, Matrix.one_mulVec, Matrix.one_mulVec]
  | cons a w ih =>
      change
        (ScalarMatrixPowerRepresentation.sumTransition (M a) (N a) *
            commRingMatrixWord (fun b ↦
              ScalarMatrixPowerRepresentation.sumTransition (M b) (N b)) w).mulVec
            (ScalarMatrixPowerRepresentation.sumVector x y) =
          ScalarMatrixPowerRepresentation.sumVector
            ((M a * commRingMatrixWord M w).mulVec x)
            ((N a * commRingMatrixWord N w).mulVec y)
      rw [← Matrix.mulVec_mulVec, ih]
      ext i
      cases i <;> simp [ScalarMatrixPowerRepresentation.sumVector,
        Matrix.mulVec_mulVec]

/-- Recognizable scalar word functions are closed under pointwise addition. -/
def add {f g : List A → R}
    (D₁ : ScalarWordRepresentation R A f)
    (D₂ : ScalarWordRepresentation R A g) :
    ScalarWordRepresentation R A (fun w ↦ f w + g w) := by
  letI := D₁.fintype
  letI := D₁.decidableEq
  letI := D₂.fintype
  letI := D₂.decidableEq
  exact
    { carrier := Sum D₁.carrier D₂.carrier
      fintype := inferInstance
      decidableEq := inferInstance
      transition := fun a ↦
        ScalarMatrixPowerRepresentation.sumTransition
          (D₁.transition a) (D₂.transition a)
      left := ScalarMatrixPowerRepresentation.sumVector D₁.left D₂.left
      seed := ScalarMatrixPowerRepresentation.sumVector D₁.seed D₂.seed
      coefficient := by
        intro w
        rw [commRingMatrixCoefficient, sumTransition_word_mulVec]
        simp only [ScalarMatrixPowerRepresentation.sumVector,
          Fintype.sum_sum_type]
        rw [← commRingMatrixCoefficient, ← commRingMatrixCoefficient,
          D₁.coefficient, D₂.coefficient] }

/-- A word of Kronecker products is the Kronecker product of the two words. -/
theorem kronecker_word
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (M : A → Matrix ι ι R) (N : A → Matrix κ κ R) (w : List A) :
    commRingMatrixWord (fun a ↦ M a ⊗ₖ N a) w =
      commRingMatrixWord M w ⊗ₖ commRingMatrixWord N w := by
  induction w with
  | nil =>
      change (1 : Matrix (ι × κ) (ι × κ) R) =
        (1 : Matrix ι ι R) ⊗ₖ (1 : Matrix κ κ R)
      simp
  | cons a w ih =>
      change (M a ⊗ₖ N a) *
          commRingMatrixWord (fun b ↦ M b ⊗ₖ N b) w =
        (M a * commRingMatrixWord M w) ⊗ₖ
          (N a * commRingMatrixWord N w)
      rw [ih, Matrix.mul_kronecker_mul]

/-- Recognizable scalar word functions are closed under pointwise
multiplication, using the Kronecker product. -/
def mul {f g : List A → R}
    (D₁ : ScalarWordRepresentation R A f)
    (D₂ : ScalarWordRepresentation R A g) :
    ScalarWordRepresentation R A (fun w ↦ f w * g w) := by
  letI := D₁.fintype
  letI := D₁.decidableEq
  letI := D₂.fintype
  letI := D₂.decidableEq
  exact
    { carrier := D₁.carrier × D₂.carrier
      fintype := inferInstance
      decidableEq := inferInstance
      transition := fun a ↦ D₁.transition a ⊗ₖ D₂.transition a
      left := fun ij ↦ D₁.left ij.1 * D₂.left ij.2
      seed := fun ij ↦ D₁.seed ij.1 * D₂.seed ij.2
      coefficient := by
        intro w
        rw [commRingMatrixCoefficient, kronecker_word,
          ScalarMatrixPowerRepresentation.kronecker_mulVec]
        simp only [← Finset.univ_product_univ, Finset.sum_product]
        calc
          _ = (∑ i, D₁.left i *
                  (commRingMatrixWord D₁.transition w).mulVec D₁.seed i) *
              (∑ j, D₂.left j *
                  (commRingMatrixWord D₂.transition w).mulVec D₂.seed j) := by
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro i hi
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j hj
                ring
          _ = f w * g w := by
            rw [← commRingMatrixCoefficient, ← commRingMatrixCoefficient,
              D₁.coefficient, D₂.coefficient] }

/-- Multiply a recognizable scalar word function by a fixed scalar. -/
def smul (c : R) {f : List A → R}
    (D : ScalarWordRepresentation R A f) :
    ScalarWordRepresentation R A (fun w ↦ c * f w) :=
  (const c).mul D

/-- Pointwise negation of a recognizable scalar word function. -/
def neg {f : List A → R} (D : ScalarWordRepresentation R A f) :
    ScalarWordRepresentation R A (fun w ↦ -f w) := by
  simpa only [neg_one_mul] using D.smul (-1)

/-- Pointwise subtraction of recognizable scalar word functions. -/
def sub {f g : List A → R}
    (D₁ : ScalarWordRepresentation R A f)
    (D₂ : ScalarWordRepresentation R A g) :
    ScalarWordRepresentation R A (fun w ↦ f w - g w) := by
  simpa only [sub_eq_add_neg] using D₁.add D₂.neg

/-- Exact-value shifts remain recognizable: this representation vanishes
exactly on the words where the original coefficient is `c`. -/
def sub_const (c : R) {f : List A → R}
    (D : ScalarWordRepresentation R A f) :
    ScalarWordRepresentation R A (fun w ↦ f w - c) :=
  D.sub (const c)

/-- The shifted realization encodes the exact level set `f(w) = c` as a
zero coefficient. -/
theorem sub_const_coefficient_eq_zero_iff (c : R) {f : List A → R}
    (D : ScalarWordRepresentation R A f) (w : List A) :
    let E := D.sub_const c
    letI := E.fintype
    letI := E.decidableEq
    commRingMatrixCoefficient E.transition E.left E.seed w = 0 ↔ f w = c := by
  dsimp only
  rw [(D.sub_const c).coefficient]
  exact sub_eq_zero

/-- Polynomial evaluation of any family of recognizable word functions is
recognizable.  Every witness is built by finite polynomial induction. -/
theorem mvPolynomial_family
    {I : Type*} {f : I → List A → R}
    (D : ∀ i, ScalarWordRepresentation R A (f i))
    (P : MvPolynomial I R) :
    Nonempty (ScalarWordRepresentation R A
      (fun w ↦ MvPolynomial.eval (fun i ↦ f i w) P)) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      exact ⟨by simpa only [MvPolynomial.eval_C] using (const (A := A) c)⟩
  | add P Q hP hQ =>
      obtain ⟨DP⟩ := hP
      obtain ⟨DQ⟩ := hQ
      exact ⟨by simpa only [MvPolynomial.eval_add] using DP.add DQ⟩
  | mul_X P i hP =>
      obtain ⟨DP⟩ := hP
      exact ⟨by simpa only [MvPolynomial.eval_mul, MvPolynomial.eval_X] using
        ScalarWordRepresentation.mul DP (D i)⟩

end ScalarWordRepresentation

namespace ScalarMatrixPowerRepresentation

variable {R : Type uR} [CommRing R]

/-- Regard a unary matrix-power representation as a scalar representation on
the singleton alphabet.  The represented value depends only on word length. -/
def toScalarWordRepresentation {f : ℕ → R}
    (D : ScalarMatrixPowerRepresentation R f) :
    ScalarWordRepresentation R Unit (fun w ↦ f w.length) := by
  letI := D.fintype
  letI := D.decidableEq
  exact
    { carrier := D.carrier
      fintype := D.fintype
      decidableEq := D.decidableEq
      transition := fun _ ↦ D.transition
      left := D.left
      seed := D.seed
      coefficient := by
        intro w
        rw [commRingMatrixCoefficient]
        have hword : commRingMatrixWord (fun _ : Unit ↦ D.transition) w =
            D.transition ^ w.length := by
          induction w with
          | nil => rfl
          | cons a w ih =>
              change D.transition *
                  commRingMatrixWord (fun _ : Unit ↦ D.transition) w =
                D.transition ^ (w.length + 1)
              rw [ih, pow_succ']
        rw [hword, D.coefficient] }

end ScalarMatrixPowerRepresentation

namespace ScalarWordRepresentation

variable {R : Type uR} [CommRing R] {A : Type uA}

/-- A common-state matrix-word realization of a family of scalar functions. -/
structure Family (J : Type) (f : J → List A → R) where
  carrier : Type
  [fintype : Fintype carrier]
  [decidableEq : DecidableEq carrier]
  transition : J → A → Matrix carrier carrier R
  left : J → carrier → R
  seed : J → carrier → R
  coefficient : ∀ j w,
    commRingMatrixCoefficient (transition j) (left j) (seed j) w = f j w

/-- Embed one member's letter transition into its block of a dependent sum. -/
def familyTransition {J : Type} [DecidableEq J]
    {f : J → List A → R} (D : ∀ j, ScalarWordRepresentation R A (f j))
    (j : J) (a : A) :
    Matrix (Σ k, (D k).carrier) (Σ k, (D k).carrier) R
  | ⟨k, x⟩, ⟨l, y⟩ =>
      if hk : k = j then
        if hl : l = j then (D j).transition a (hk ▸ x) (hl ▸ y) else 0
      else 0

/-- Embed a state vector into one block of a dependent sum. -/
def familyVector {J : Type} [DecidableEq J]
    {f : J → List A → R} (D : ∀ j, ScalarWordRepresentation R A (f j))
    (j : J) (x : (D j).carrier → R) : (Σ k, (D k).carrier) → R
  | ⟨k, y⟩ => if h : k = j then x (h ▸ y) else 0

/-- One embedded transition acts on its embedded vector exactly as the
original transition. -/
theorem familyTransition_mulVec_familyVector
    {J : Type} [Fintype J] [DecidableEq J]
    {f : J → List A → R} (D : ∀ j, ScalarWordRepresentation R A (f j))
    (j : J) (a : A) (x : (D j).carrier → R) :
    letI : ∀ k, Fintype (D k).carrier := fun k ↦ (D k).fintype
    (familyTransition D j a).mulVec (familyVector D j x) =
      familyVector D j (((D j).transition a).mulVec x) := by
  letI : ∀ k, Fintype (D k).carrier := fun k ↦ (D k).fintype
  funext p
  rcases p with ⟨k, y⟩
  by_cases hk : k = j
  · subst k
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_sigma]
    rw [Finset.sum_eq_single j]
    · simp [familyTransition, familyVector, Matrix.mulVec, dotProduct]
    · intro l hl hlj
      simp [familyTransition, familyVector, hlj]
    · simp
  · simp [Matrix.mulVec, dotProduct, familyTransition, familyVector, hk]

/-- An embedded matrix word acts on its block exactly as the original word. -/
theorem familyTransition_word_mulVec_familyVector
    {J : Type} [Fintype J] [DecidableEq J]
    {f : J → List A → R} (D : ∀ j, ScalarWordRepresentation R A (f j))
    (j : J) (x : (D j).carrier → R) (w : List A) :
    letI : ∀ k, Fintype (D k).carrier := fun k ↦ (D k).fintype
    letI : ∀ k, DecidableEq (D k).carrier := fun k ↦ (D k).decidableEq
    (commRingMatrixWord (familyTransition D j) w).mulVec (familyVector D j x) =
      familyVector D j ((commRingMatrixWord (D j).transition w).mulVec x) := by
  letI : ∀ k, Fintype (D k).carrier := fun k ↦ (D k).fintype
  letI : ∀ k, DecidableEq (D k).carrier := fun k ↦ (D k).decidableEq
  induction w with
  | nil =>
      change (1 : Matrix (Σ k, (D k).carrier) (Σ k, (D k).carrier) R).mulVec
          (familyVector D j x) =
        familyVector D j ((1 : Matrix (D j).carrier (D j).carrier R).mulVec x)
      rw [Matrix.one_mulVec, Matrix.one_mulVec]
  | cons a w ih =>
      change
        (familyTransition D j a * commRingMatrixWord (familyTransition D j) w).mulVec
            (familyVector D j x) =
          familyVector D j
            (((D j).transition a * commRingMatrixWord (D j).transition w).mulVec x)
      rw [← Matrix.mulVec_mulVec, ih, familyTransition_mulVec_familyVector,
        ← Matrix.mulVec_mulVec]

/-- The scalar pairing of two vectors embedded in one block is their original
scalar pairing. -/
theorem sum_familyVector_mul
    {J : Type} [Fintype J] [DecidableEq J]
    {f : J → List A → R} (D : ∀ j, ScalarWordRepresentation R A (f j))
    (j : J) (x y : (D j).carrier → R) :
    letI : ∀ k, Fintype (D k).carrier := fun k ↦ (D k).fintype
    ∑ p, familyVector D j x p * familyVector D j y p =
      ∑ i, x i * y i := by
  letI : ∀ k, Fintype (D k).carrier := fun k ↦ (D k).fintype
  simp only [Fintype.sum_sigma]
  rw [Finset.sum_eq_single j]
  · simp [familyVector]
  · intro k hk hkj
    simp [familyVector, hkj]
  · simp

/-- Pack finitely many independently represented word functions into one
common finite state type. -/
def packFamily {J : Type} [Fintype J] [DecidableEq J]
    {f : J → List A → R} (D : ∀ j, ScalarWordRepresentation R A (f j)) :
    Family (R := R) (A := A) J f := by
  letI : ∀ j, Fintype (D j).carrier := fun j ↦ (D j).fintype
  letI : ∀ j, DecidableEq (D j).carrier := fun j ↦ (D j).decidableEq
  exact
    { carrier := Σ j, (D j).carrier
      fintype := inferInstance
      decidableEq := inferInstance
      transition := familyTransition D
      left := fun j ↦ familyVector D j (D j).left
      seed := fun j ↦ familyVector D j (D j).seed
      coefficient := by
        intro j w
        rw [commRingMatrixCoefficient,
          familyTransition_word_mulVec_familyVector, sum_familyVector_mul,
          ← commRingMatrixCoefficient, (D j).coefficient] }

end ScalarWordRepresentation

/-- Public name for a common-carrier finite family of scalar word
representations. -/
abbrev ScalarWordFamilyRepresentation
    (R : Type uR) [CommRing R] (A : Type uA)
    (J : Type) (f : J → List A → R) :=
  ScalarWordRepresentation.Family (R := R) (A := A) J f

end IndependentZeroBlocks
