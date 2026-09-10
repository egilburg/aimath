import SierpinskiFormal.BooleanDoubleLimitClosure
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-! # Finite Boolean operations as linear combinations of union indicators -/

noncomputable section

set_option autoImplicit false

open scoped BigOperators

namespace IndependentZeroBlocks

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Möbius coefficient on the Boolean lattice of finite subsets. -/
def powersetMobiusCoefficient (g : Finset J → ℝ) (s : Finset J) : ℝ :=
  ∑ t ∈ s.powerset, (-1 : ℝ) ^ (s \ t).card * g t

omit [Fintype J] in theorem powersetMobiusCoefficient_insert
    (g : Finset J → ℝ) {a : J} {s : Finset J} (ha : a ∉ s) :
    powersetMobiusCoefficient g (insert a s) =
      powersetMobiusCoefficient (fun t ↦ g (insert a t)) s -
        powersetMobiusCoefficient g s := by
  classical
  simp only [powersetMobiusCoefficient, Finset.sum_powerset_insert ha]
  have hleft :
      (∑ t ∈ s.powerset, (-1 : ℝ) ^ (insert a s \ t).card * g t) =
        -(∑ t ∈ s.powerset, (-1 : ℝ) ^ (s \ t).card * g t) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    have hat : a ∉ t := fun h ↦ ha ((Finset.mem_powerset.mp ht) h)
    have hdiff : insert a s \ t = insert a (s \ t) := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_insert]
      aesop
    have haDiff : a ∉ s \ t := by simp [ha]
    rw [hdiff, Finset.card_insert_of_notMem haDiff]
    rw [pow_succ]
    ring
  have hright :
      (∑ t ∈ s.powerset,
        (-1 : ℝ) ^ (insert a s \ insert a t).card * g (insert a t)) =
      ∑ t ∈ s.powerset, (-1 : ℝ) ^ (s \ t).card * g (insert a t) := by
    apply Finset.sum_congr rfl
    intro t ht
    have hdiff : insert a s \ insert a t = s \ t := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_insert]
      aesop
    rw [hdiff]
  rw [hleft, hright]
  ring

omit [Fintype J] in
/-- Boolean-lattice Möbius inversion in a form suited to indicator expansions. -/
theorem sum_powersetMobiusCoefficient
    (g : Finset J → ℝ) (s : Finset J) :
    ∑ t ∈ s.powerset, powersetMobiusCoefficient g t = g s := by
  classical
  induction s using Finset.induction generalizing g with
  | empty => simp [powersetMobiusCoefficient]
  | @insert a s ha ih =>
      rw [Finset.sum_powerset_insert ha]
      have hsecond :
          (∑ t ∈ s.powerset, powersetMobiusCoefficient g (insert a t)) =
            ∑ t ∈ s.powerset,
              (powersetMobiusCoefficient (fun u ↦ g (insert a u)) t -
                powersetMobiusCoefficient g t) := by
        apply Finset.sum_congr rfl
        intro t ht
        exact powersetMobiusCoefficient_insert g
          (fun hat ↦ ha ((Finset.mem_powerset.mp ht) hat))
      rw [hsecond, Finset.sum_sub_distrib, ih, ih]
      ring

/-- The set of coordinates on which a Boolean assignment is false. -/
def booleanFalseSet (b : J → Bool) : Finset J :=
  Finset.univ.filter fun j ↦ b j = false

/-- The canonical Boolean assignment whose false set is `s`. -/
def booleanAssignmentOfFalseSet (s : Finset J) : J → Bool :=
  fun j ↦ decide (j ∉ s)

@[simp] theorem booleanAssignmentOfFalseSet_falseSet (b : J → Bool) :
    booleanAssignmentOfFalseSet (booleanFalseSet b) = b := by
  funext j
  simp only [booleanAssignmentOfFalseSet, booleanFalseSet, Finset.mem_filter,
    Finset.mem_univ, true_and]
  cases h : b j <;> simp [h]

/-- Real indicator that all coordinates in `s` are false. -/
def booleanAllZeroIndicator (s : Finset J) (b : J → Bool) : ℝ :=
  if s ⊆ booleanFalseSet b then 1 else 0

/-- Real indicator that at least one coordinate in `s` is true. -/
def booleanUnionIndicator (s : Finset J) (b : J → Bool) : ℝ :=
  boolIndicator (decide (∃ j ∈ s, b j = true))

theorem booleanAllZeroIndicator_eq_one_sub_union
    (s : Finset J) (b : J → Bool) :
    booleanAllZeroIndicator s b = 1 - booleanUnionIndicator s b := by
  classical
  simp only [booleanAllZeroIndicator, booleanUnionIndicator, booleanFalseSet,
    Finset.subset_iff, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases h : ∃ j ∈ s, b j = true
  · have hz : ¬∀ ⦃a⦄, a ∈ s → b a = false := by
      rintro hall
      obtain ⟨j, hjs, hj⟩ := h
      simpa [hj] using hall hjs
    simp [h, hz, boolIndicator]
  · have hz : ∀ ⦃a⦄, a ∈ s → b a = false := by
      intro a ha
      cases hb : b a with
      | false => rfl
      | true => exact (h ⟨a, ha, hb⟩).elim
    simp [h, hz, boolIndicator]

/-- Möbius coefficient of a Boolean operation in the all-zero basis. -/
def booleanAllZeroCoefficient (op : (J → Bool) → Bool) (s : Finset J) : ℝ :=
  powersetMobiusCoefficient
    (fun t ↦ boolIndicator (op (booleanAssignmentOfFalseSet t))) s

/-- Every finite Boolean operation is a linear combination of the indicators
that selected groups of inputs are all false. -/
theorem boolIndicator_eq_sum_allZeroIndicators
    (op : (J → Bool) → Bool) (b : J → Bool) :
    boolIndicator (op b) =
      ∑ s : Finset J, booleanAllZeroCoefficient op s * booleanAllZeroIndicator s b := by
  classical
  let g : Finset J → ℝ :=
    fun t ↦ boolIndicator (op (booleanAssignmentOfFalseSet t))
  let C : Finset J := booleanFalseSet b
  have hsum :
      (∑ s : Finset J,
        booleanAllZeroCoefficient op s * booleanAllZeroIndicator s b) =
        ∑ s ∈ C.powerset, powersetMobiusCoefficient g s := by
    simp only [booleanAllZeroCoefficient, booleanAllZeroIndicator, g, C]
    simp_rw [mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext s
      simp [C]
    · intro s hs
      simp
  rw [hsum, sum_powersetMobiusCoefficient]
  simp only [g, C, booleanAssignmentOfFalseSet_falseSet]

/-- Constant coefficient in the union-indicator expansion. -/
def booleanUnionConstant (op : (J → Bool) → Bool) : ℝ :=
  ∑ s : Finset J, booleanAllZeroCoefficient op s

/-- Coefficient of one union indicator. -/
def booleanUnionCoefficient (op : (J → Bool) → Bool) (s : Finset J) : ℝ :=
  -booleanAllZeroCoefficient op s

/-- Every operation on finitely many Boolean inputs is a constant plus a finite
real linear combination of indicators that at least one input in `s` is true.
The coefficients depend only on `op`. -/
theorem boolIndicator_eq_constant_add_sum_unionIndicators
    (op : (J → Bool) → Bool) (b : J → Bool) :
    boolIndicator (op b) = booleanUnionConstant op +
      ∑ s : Finset J, booleanUnionCoefficient op s * booleanUnionIndicator s b := by
  rw [boolIndicator_eq_sum_allZeroIndicators]
  simp_rw [booleanAllZeroIndicator_eq_one_sub_union, mul_sub, mul_one]
  rw [Finset.sum_sub_distrib]
  simp only [booleanUnionConstant, booleanUnionCoefficient, neg_mul]
  rw [Finset.sum_neg_distrib]
  ring

end IndependentZeroBlocks
