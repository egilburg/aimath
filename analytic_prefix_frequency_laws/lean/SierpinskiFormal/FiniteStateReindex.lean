import SierpinskiFormal.ScalarWordTransduction

/-! # Reindexing finite-state transport

Finite source state types may live in any universe. Reindexing through their
finite enumeration lets the common scalar representation interface retain its
small carrier without restricting the source state type.
-/

noncomputable section
namespace IndependentZeroBlocks
namespace FiniteStateTransducer

variable {Q P B A : Type*}

/-- Change only the names of transducer states. -/
def reindex (T : FiniteStateTransducer Q B A) (e : Q ≃ P) :
    FiniteStateTransducer P B A where
  next p b := e (T.next (e.symm p) b)
  emit p b := T.emit (e.symm p) b

@[simp] theorem outputWord_reindex (T : FiniteStateTransducer Q B A)
    (e : Q ≃ P) (q : Q) (w : List B) :
    (T.reindex e).outputWord (e q) w = T.outputWord q w := by
  induction w generalizing q with
  | nil => rfl
  | cons b w ih =>
      simp only [outputWord_cons, reindex, Equiv.symm_apply_apply]
      exact congrArg (List.cons (T.emit q b)) (ih (T.next q b))

@[simp] theorem stateAfter_reindex (T : FiniteStateTransducer Q B A)
    (e : Q ≃ P) (q : Q) (w : List B) :
    (T.reindex e).stateAfter (e q) w = e (T.stateAfter q w) := by
  induction w generalizing q with
  | nil => rfl
  | cons b w ih =>
      simp only [stateAfter_cons, reindex, Equiv.symm_apply_apply]
      exact ih (T.next q b)

end FiniteStateTransducer
namespace ScalarWordRepresentation

variable {R A B Q : Type*} [CommRing R] [Fintype Q]

/-- Pullback through any finite state type, without a universe restriction on
the states. The represented scalar function is unchanged by reindexing. -/
def pullbackFinite {f : List A → R} (D : ScalarWordRepresentation R A f)
    (T : FiniteStateTransducer Q B A) (q : Q) :
    ScalarWordRepresentation R B (fun w ↦ f (T.outputWord q w)) := by
  let E := D.pullback (T.reindex (Fintype.equivFin Q)) (Fintype.equivFin Q q)
  exact { E with coefficient := by intro w; simpa using E.coefficient w }

end ScalarWordRepresentation
end IndependentZeroBlocks
