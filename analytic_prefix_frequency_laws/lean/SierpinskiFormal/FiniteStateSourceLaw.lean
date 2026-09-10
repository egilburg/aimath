import SierpinskiFormal.FiniteStateTransducer
import SierpinskiFormal.FiniteSourceAnalyticWeights
import SierpinskiFormal.WeightedWordEnumeration

set_option autoImplicit false

/-! # Finite-state sources as IID selector transducers

A finite-state source chooses an outgoing edge from its current state.  An IID
selector chooses one outgoing edge at every state; reading only the coordinate
of the current state realizes the source as a deterministic transducer.  The
main theorem below proves the actual finite path law from the edge-by-edge
recursion, rather than taking the selector average as its definition.
-/

noncomputable section
open scoped BigOperators

namespace IndependentZeroBlocks

/-- A finite directed source whose edges carry output letters. -/
structure FiniteStateSource (Q A : Type*) [Fintype Q] where
  Edge : Q → Type*
  edgeFintype : ∀ q, Fintype (Edge q)
  edgeNonempty : ∀ q, Nonempty (Edge q)
  target : (q : Q) → Edge q → Q
  label : (q : Q) → Edge q → A

namespace FiniteStateSource

variable {Q A : Type*} [Fintype Q]

instance (S : FiniteStateSource Q A) (q : Q) : Fintype (S.Edge q) :=
  S.edgeFintype q

instance (S : FiniteStateSource Q A) (q : Q) : Nonempty (S.Edge q) :=
  S.edgeNonempty q

/-- A selector specifies one outgoing edge at every state. -/
abbrev Selector (S : FiniteStateSource Q A) := (q : Q) → S.Edge q

noncomputable instance selectorFintype (S : FiniteStateSource Q A) :
    Fintype S.Selector :=
  @Pi.instFintype Q S.Edge (Classical.decEq Q) _ (fun q ↦ S.edgeFintype q)

noncomputable instance selectorDecidableEq (S : FiniteStateSource Q A) :
    DecidableEq S.Selector :=
  Classical.decEq S.Selector

/-- The deterministic transducer driven by IID selectors. -/
def transducer (S : FiniteStateSource Q A) :
    FiniteStateTransducer Q S.Selector A where
  next q f := S.target q (f q)
  emit q f := S.label q (f q)

@[simp] theorem transducer_next (S : FiniteStateSource Q A)
    (q : Q) (f : S.Selector) :
    S.transducer.next q f = S.target q (f q) := rfl

@[simp] theorem transducer_emit (S : FiniteStateSource Q A)
    (q : Q) (f : S.Selector) :
    S.transducer.emit q f = S.label q (f q) := rfl

theorem selectorWeight_pos (S : FiniteStateSource Q A)
    (p : (q : Q) → S.Edge q → ℝ) (hp : ∀ q e, 0 < p q e)
    (f : S.Selector) :
    0 < sourceSelectorWeights p f := by
  exact Finset.prod_pos fun q _ ↦ hp q (f q)

/-- The total selector mass factors into the row masses. -/
theorem sum_selectorWeight (S : FiniteStateSource Q A)
    (p : (q : Q) → S.Edge q → ℝ) :
    (∑ f : S.Selector, sourceSelectorWeights p f) =
      ∏ q, ∑ e : S.Edge q, p q e := by
  classical
  unfold sourceSelectorWeights
  exact (Fintype.prod_sum p).symm

theorem sum_selectorWeight_eq_one (S : FiniteStateSource Q A)
    (p : (q : Q) → S.Edge q → ℝ)
    (hp1 : ∀ q, ∑ e : S.Edge q, p q e = 1) :
    (∑ f : S.Selector, sourceSelectorWeights p f) = 1 := by
  rw [sum_selectorWeight]
  simp [hp1]

/-- Under normalized rows, averaging a function of one selector coordinate
gives the corresponding row average. -/
theorem sum_selectorWeight_mul_apply (S : FiniteStateSource Q A)
    (p : (q : Q) → S.Edge q → ℝ)
    (hp1 : ∀ q, ∑ e : S.Edge q, p q e = 1)
    (q : Q) (g : S.Edge q → ℝ) :
    (∑ f : S.Selector, sourceSelectorWeights p f * g (f q)) =
      ∑ e : S.Edge q, p q e * g e := by
  classical
  let p' : (r : Q) → S.Edge r → ℝ :=
    Function.update p q (fun e ↦ p q e * g e)
  have hweight (f : S.Selector) :
      sourceSelectorWeights p' f = sourceSelectorWeights p f * g (f q) := by
    unfold sourceSelectorWeights
    rw [← Finset.mul_prod_erase Finset.univ (fun r ↦ p' r (f r))
      (Finset.mem_univ q)]
    rw [← Finset.mul_prod_erase Finset.univ (fun r ↦ p r (f r))
      (Finset.mem_univ q)]
    simp only [p', Function.update_self]
    have hrest :
        (∏ r ∈ Finset.univ.erase q, p' r (f r)) =
          ∏ r ∈ Finset.univ.erase q, p r (f r) := by
      apply Finset.prod_congr rfl
      intro r hr
      have hrq : r ≠ q := (Finset.mem_erase.mp hr).1
      simp [p', Function.update_of_ne hrq]
    rw [hrest]
    ring
  have hrow :
      (∏ r, ∑ e : S.Edge r, p' r e) =
        ∑ e : S.Edge q, p q e * g e := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun r ↦ ∑ e : S.Edge r, p' r e) (Finset.mem_univ q)]
    simp only [p', Function.update_self]
    have hrest :
        (∏ r ∈ Finset.univ.erase q, ∑ e : S.Edge r, p' r e) = 1 := by
      apply Finset.prod_eq_one
      intro r hr
      have hrq : r ≠ q := (Finset.mem_erase.mp hr).1
      simpa [p', Function.update_of_ne hrq] using hp1 r
    rw [hrest, mul_one]
  calc
    (∑ f : S.Selector, sourceSelectorWeights p f * g (f q)) =
        ∑ f : S.Selector, sourceSelectorWeights p' f := by
          apply Finset.sum_congr rfl
          intro f _
          exact (hweight f).symm
    _ = ∏ r, ∑ e : S.Edge r, p' r e := S.sum_selectorWeight p'
    _ = ∑ e : S.Edge q, p q e * g e := hrow

/-- The genuine finite-path expectation of a source, defined by choosing only
an outgoing edge of the current state at each step. -/
def sourceExpectation (S : FiniteStateSource Q A)
    (p : (q : Q) → S.Edge q → ℝ) (F : List A → ℝ) : Q → ℕ → ℝ
  | _, 0 => F []
  | q, n + 1 =>
      ∑ e : S.Edge q,
        p q e * S.sourceExpectation p (fun w ↦ F (S.label q e :: w))
          (S.target q e) n

@[simp] theorem sourceExpectation_zero (S : FiniteStateSource Q A)
    (p : (q : Q) → S.Edge q → ℝ) (F : List A → ℝ) (q : Q) :
    S.sourceExpectation p F q 0 = F [] := rfl

@[simp] theorem sourceExpectation_succ (S : FiniteStateSource Q A)
    (p : (q : Q) → S.Edge q → ℝ) (F : List A → ℝ) (q : Q) (n : ℕ) :
    S.sourceExpectation p F q (n + 1) =
      ∑ e : S.Edge q,
        p q e * S.sourceExpectation p (fun w ↦ F (S.label q e :: w))
          (S.target q e) n := rfl

/-- Exact finite path law: the state-recursive source expectation equals the
IID selector average of the output of its deterministic transducer. -/
theorem sourceExpectation_eq_selector_tuple_sum (S : FiniteStateSource Q A)
    (p : (q : Q) → S.Edge q → ℝ)
    (hp1 : ∀ q, ∑ e : S.Edge q, p q e = 1)
    (F : List A → ℝ) (q : Q) (n : ℕ) :
    S.sourceExpectation p F q n =
      ∑ w : Fin n → S.Selector,
        wordWeight (sourceSelectorWeights p) (List.ofFn w) *
          F (S.transducer.outputWord q (List.ofFn w)) := by
  classical
  induction n generalizing q F with
  | zero => simp [sourceExpectation, wordWeight]
  | succ n ih =>
      rw [sourceExpectation_succ]
      simp_rw [ih]
      rw [Fintype.sum_equiv (finSuccTupleEquiv n)
        (fun w : Fin (n + 1) → S.Selector ↦
          wordWeight (sourceSelectorWeights p) (List.ofFn w) *
            F (S.transducer.outputWord q (List.ofFn w)))
        (fun fw : S.Selector × (Fin n → S.Selector) ↦
          sourceSelectorWeights p fw.1 *
            (wordWeight (sourceSelectorWeights p) (List.ofFn fw.2) *
              F (S.label q (fw.1 q) ::
                S.transducer.outputWord (S.target q (fw.1 q))
                  (List.ofFn fw.2))))]
      · rw [Fintype.sum_prod_type]
        simp_rw [← Finset.mul_sum]
        exact (S.sum_selectorWeight_mul_apply p hp1 q _).symm
      · intro w
        simp [List.ofFn_succ, finSuccTupleEquiv, mul_assoc]

end FiniteStateSource
end IndependentZeroBlocks
