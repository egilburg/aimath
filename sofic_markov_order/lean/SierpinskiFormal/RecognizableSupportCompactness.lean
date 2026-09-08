import SierpinskiFormal.SupportLogDensityExistence

/-!
# Compactness and IID density for recognizable Boolean word supports

This file packages the structural endpoint for a finite Boolean combination
of finite matrix-word coefficients over a common commutative ring.
-/

noncomputable section

open Filter Set Topology
open scoped Topology

namespace IndependentZeroBlocks

variable {K ι : Type*} [CommRing K] [Fintype ι]
  {b d : ℕ}

/-- A Boolean combination of supports of finitely many recognizable word
series, using a common alphabet, coefficient ring, and coordinate module. -/
def recognizableBooleanWordSupport
    (op : (Fin d → Bool) → Bool)
    (M : Fin d → Fin b → Matrix ι ι K)
    (u a : Fin d → ι → K) (w : List (Fin b)) : Bool :=
  op (fun i ↦ nonzeroBool
    (coordinateRowDual (a i)
      (linearWord (fun r ↦ Matrix.mulVecLin (M i r)) w (u i))))

/-- The right-translation kernel of a recognizable Boolean word support has
the sequential Boolean double-limit property. -/
theorem recognizableBooleanWordSupport_rightKernel_hasBooleanDoubleLimitProperty
    (op : (Fin d → Bool) → Bool)
    (M : Fin d → Fin b → Matrix ι ι K)
    (u a : Fin d → ι → K) :
    HasBooleanDoubleLimitProperty (fun w z : List (Fin b) ↦
      recognizableBooleanWordSupport op M u a (z ++ w)) := by
  have h :=
    (matrixWordsNonzeroBool_booleanCombine_hasBooleanDoubleLimitProperty
      op M u a).swap
  simpa only [recognizableBooleanWordSupport, booleanCombine,
    matrixWordsNonzeroBool] using h

/-- The bounded-function row closure of a recognizable Boolean word support
is weakly compact and countable. -/
theorem recognizableBooleanWordSupport_rowClosure_weakly_compact_and_countable
    (hb : 0 < b) (op : (Fin d → Bool) → Bool)
    (M : Fin d → Fin b → Matrix ι ι K)
    (u a : Fin d → ι → K) :
    IsCompact (toWeakSpace ℝ (BoundedWordFunction (Fin b)) ''
      boundedBooleanWordRowClosure
        (recognizableBooleanWordSupport op M u a)) ∧
    (boundedBooleanWordRowClosure
      (recognizableBooleanWordSupport op M u a)).Countable := by
  letI : Nonempty (Fin b) := ⟨⟨0, hb⟩⟩
  let q := recognizableBooleanWordSupport op M u a
  have hDLP : HasBooleanDoubleLimitProperty (fun w z ↦ q (z ++ w)) :=
    recognizableBooleanWordSupport_rightKernel_hasBooleanDoubleLimitProperty
      op M u a
  obtain ⟨hcompact, hcount⟩ :=
    booleanRowClosure_weakly_compact_and_countable (booleanWordRow q) (by
      change HasBooleanDoubleLimitProperty (fun w z ↦ q (z ++ w))
      exact hDLP)
  constructor
  · apply isCompact_boundedBooleanWordRowClosure_of_extended q
    simpa only [extendedBooleanWordRowClosure, booleanWordRowClosure,
      booleanRowExtensionClosure] using hcompact
  · apply countable_boundedBooleanWordRowClosure_of_extended q
    simpa only [extendedBooleanWordRowClosure, booleanWordRowClosure,
      booleanRowExtensionClosure] using hcount

/-- Uniform IID word-length Cesaro averages of every recognizable Boolean
word support converge. -/
theorem exists_tendsto_recognizableBooleanWordSupport_uniform_iid_word_cesaro
    (hb : 0 < b) (op : (Fin d → Bool) → Bool)
    (M : Fin d → Fin b → Matrix ι ι K)
    (u a : Fin d → ι → K) :
    ∃ L : ℝ, Tendsto
      (@uniformIidWordCesaro (Fin b) inferInstance inferInstance ⟨⟨0, hb⟩⟩
        (booleanWordIndicator (recognizableBooleanWordSupport op M u a)))
      atTop (𝓝 L) := by
  letI : Nonempty (Fin b) := ⟨⟨0, hb⟩⟩
  exact exists_tendsto_boolean_uniform_iid_word_cesaro
    (recognizableBooleanWordSupport op M u a)
    (recognizableBooleanWordSupport_rightKernel_hasBooleanDoubleLimitProperty
      op M u a)

end IndependentZeroBlocks
