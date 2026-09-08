import Mathlib.Data.List.OfFn

set_option autoImplicit false

/-! # Finite-state transducers

Deterministic letter-to-letter transducers, with their word output and final
state.  Finiteness assumptions are deliberately absent from the basic API;
they are needed only by constructions that turn states into matrix indices.
-/

namespace IndependentZeroBlocks

/-- A deterministic letter-to-letter transducer. -/
structure FiniteStateTransducer (Q B A : Type*) where
  next : Q → B → Q
  emit : Q → B → A

namespace FiniteStateTransducer

/-- The output word produced from an initial state. -/
def outputWord {Q B A : Type*} (T : FiniteStateTransducer Q B A) :
    Q → List B → List A
  | _, [] => []
  | q, b :: w => T.emit q b :: T.outputWord (T.next q b) w

/-- The state reached after reading a word. -/
def stateAfter {Q B A : Type*} (T : FiniteStateTransducer Q B A) :
    Q → List B → Q
  | q, [] => q
  | q, b :: w => T.stateAfter (T.next q b) w

@[simp] theorem outputWord_nil {Q B A : Type*}
    (T : FiniteStateTransducer Q B A) (q : Q) :
    T.outputWord q [] = [] := rfl

@[simp] theorem outputWord_cons {Q B A : Type*}
    (T : FiniteStateTransducer Q B A) (q : Q) (b : B) (w : List B) :
    T.outputWord q (b :: w) =
      T.emit q b :: T.outputWord (T.next q b) w := rfl

@[simp] theorem stateAfter_nil {Q B A : Type*}
    (T : FiniteStateTransducer Q B A) (q : Q) :
    T.stateAfter q [] = q := rfl

@[simp] theorem stateAfter_cons {Q B A : Type*}
    (T : FiniteStateTransducer Q B A) (q : Q) (b : B) (w : List B) :
    T.stateAfter q (b :: w) = T.stateAfter (T.next q b) w := rfl

@[simp] theorem stateAfter_append {Q B A : Type*}
    (T : FiniteStateTransducer Q B A) (q : Q) (u v : List B) :
    T.stateAfter q (u ++ v) = T.stateAfter (T.stateAfter q u) v := by
  induction u generalizing q with
  | nil => rfl
  | cons b u ih => exact ih (T.next q b)

@[simp] theorem outputWord_append {Q B A : Type*}
    (T : FiniteStateTransducer Q B A) (q : Q) (u v : List B) :
    T.outputWord q (u ++ v) =
      T.outputWord q u ++ T.outputWord (T.stateAfter q u) v := by
  induction u generalizing q with
  | nil => rfl
  | cons b u ih =>
      simp only [List.cons_append, outputWord_cons, stateAfter_cons]
      rw [ih]

@[simp] theorem length_outputWord {Q B A : Type*}
    (T : FiniteStateTransducer Q B A) (q : Q) (w : List B) :
    (T.outputWord q w).length = w.length := by
  induction w generalizing q with
  | nil => rfl
  | cons b w ih => simp [ih]

/-- Sequential composition.  The product state remembers the states of both
transducers while the output of the first feeds the second letter by letter. -/
def comp {Q P B A C : Type*} (U : FiniteStateTransducer P A C)
    (T : FiniteStateTransducer Q B A) : FiniteStateTransducer (Q × P) B C where
  next qp b := (T.next qp.1 b, U.next qp.2 (T.emit qp.1 b))
  emit qp b := U.emit qp.2 (T.emit qp.1 b)

@[simp] theorem stateAfter_comp {Q P B A C : Type*}
    (U : FiniteStateTransducer P A C) (T : FiniteStateTransducer Q B A)
    (q : Q) (p : P) (w : List B) :
    (U.comp T).stateAfter (q, p) w =
      (T.stateAfter q w, U.stateAfter p (T.outputWord q w)) := by
  induction w generalizing q p with
  | nil => rfl
  | cons b w ih => exact ih (T.next q b) (U.next p (T.emit q b))

@[simp] theorem outputWord_comp {Q P B A C : Type*}
    (U : FiniteStateTransducer P A C) (T : FiniteStateTransducer Q B A)
    (q : Q) (p : P) (w : List B) :
    (U.comp T).outputWord (q, p) w =
      U.outputWord p (T.outputWord q w) := by
  induction w generalizing q p with
  | nil => rfl
  | cons b w ih =>
      change U.emit p (T.emit q b) ::
          (U.comp T).outputWord
            (T.next q b, U.next p (T.emit q b)) w =
        U.emit p (T.emit q b) ::
          U.outputWord (U.next p (T.emit q b))
            (T.outputWord (T.next q b) w)
      rw [ih]

/-- The one-state identity transducer. -/
def identity (A : Type*) : FiniteStateTransducer PUnit A A where
  next _ _ := PUnit.unit
  emit _ a := a

@[simp] theorem outputWord_identity (A : Type*) (q : PUnit) (w : List A) :
    (identity A).outputWord q w = w := by
  induction w generalizing q with
  | nil => rfl
  | cons a w ih =>
      change a :: (identity A).outputWord PUnit.unit w = a :: w
      rw [ih]

@[simp] theorem outputWord_comp_identity_left {Q B A : Type*}
    (T : FiniteStateTransducer Q B A) (q : Q) (u : PUnit) (w : List B) :
    ((identity A).comp T).outputWord (q, u) w = T.outputWord q w := by
  rw [outputWord_comp, outputWord_identity]

@[simp] theorem outputWord_comp_identity_right {Q B A : Type*}
    (T : FiniteStateTransducer Q B A) (u : PUnit) (q : Q) (w : List B) :
    (T.comp (identity B)).outputWord (u, q) w = T.outputWord q w := by
  rw [outputWord_comp, outputWord_identity]

end FiniteStateTransducer

end IndependentZeroBlocks
