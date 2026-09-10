import SierpinskiFormal.ScalarWordRepresentation
import SierpinskiFormal.FiniteStateMatrixObservation

set_option autoImplicit false

/-!
# Pullback of scalar word representations through finite-state transducers

The transducer state is adjoined to the observation state.  This realizes the
literal pullback of the represented scalar function along the emitted-word
map, over an arbitrary commutative ring.
-/

noncomputable section

namespace IndependentZeroBlocks
namespace ScalarWordRepresentation

universe uR uA uB

variable {R : Type uR} [CommRing R] {A : Type uA} {B : Type uB}

/-- Pull a recognizable scalar function back along a finite-state transducer
from a chosen initial state. -/
def pullback {Q : Type} [Fintype Q] [DecidableEq Q]
    {f : List A → R} (D : ScalarWordRepresentation R A f)
    (T : FiniteStateTransducer Q B A) (q₀ : Q) :
    ScalarWordRepresentation R B (fun w ↦ f (T.outputWord q₀ w)) := by
  letI := D.fintype
  letI := D.decidableEq
  exact
    { carrier := Q × D.carrier
      fintype := inferInstance
      decidableEq := inferInstance
      transition := T.matrixLift D.transition
      left := FiniteStateTransducer.leftLift q₀ D.left
      seed := FiniteStateTransducer.seedLift D.seed
      coefficient := by
        intro w
        rw [FiniteStateTransducer.coefficient_matrixLift, D.coefficient] }

/-- The coefficient of the constructed pullback is the original observation
of the word emitted by the transducer. -/
theorem pullback_coefficient {Q : Type} [Fintype Q] [DecidableEq Q]
    {f : List A → R} (D : ScalarWordRepresentation R A f)
    (T : FiniteStateTransducer Q B A) (q₀ : Q) (w : List B) :
    let E := D.pullback T q₀
    letI := E.fintype
    letI := E.decidableEq
    commRingMatrixCoefficient E.transition E.left E.seed w =
      f (T.outputWord q₀ w) := by
  exact (D.pullback T q₀).coefficient w

/-- Pulling back once through a composite transducer and pulling back through
the two transducers successively have the same scalar observation. -/
theorem pullback_comp_coefficient
    {Q P : Type} [Fintype Q] [DecidableEq Q]
    [Fintype P] [DecidableEq P]
    {C : Type*} {f : List C → R}
    (D : ScalarWordRepresentation R C f)
    (U : FiniteStateTransducer P A C)
    (T : FiniteStateTransducer Q B A)
    (q₀ : Q) (p₀ : P) (w : List B) :
    let direct := D.pullback (U.comp T) (q₀, p₀)
    let successive := (D.pullback U p₀).pullback T q₀
    letI := direct.fintype
    letI := direct.decidableEq
    letI := successive.fintype
    letI := successive.decidableEq
    commRingMatrixCoefficient direct.transition direct.left direct.seed w =
      commRingMatrixCoefficient successive.transition successive.left
        successive.seed w := by
  dsimp only
  rw [(D.pullback (U.comp T) (q₀, p₀)).coefficient,
    ((D.pullback U p₀).pullback T q₀).coefficient,
    FiniteStateTransducer.outputWord_comp]

end ScalarWordRepresentation
end IndependentZeroBlocks
