import SierpinskiFormal.MinimalRankCompression

set_option autoImplicit false

namespace IndependentZeroBlocks

section ScalarExtension
variable {F K A ι : Type*} [Field F] [Field K] [Fintype ι] [DecidableEq ι]

/-- Scalar extension commutes with chronological matrix-word evaluation. -/
theorem matrixWord_map (f : F →+* K) (M : A → Matrix ι ι F) (w : List A) :
    matrixWord (fun a => (M a).map f) w = (matrixWord M w).map f := by
  induction w with
  | nil => simp
  | cons a w ih =>
      simpa [matrixWord] using congrArg (fun X => (M a).map f * X) ih

/-- A finite word monoid remains finite after scalar extension. -/
theorem finite_matrixWord_range_map (f : F →+* K) (M : A → Matrix ι ι F)
    (hfinite : (Set.range (matrixWord M)).Finite) :
    (Set.range (matrixWord (fun a => (M a).map f))).Finite := by
  have hrange : Set.range (matrixWord (fun a => (M a).map f)) =
      (fun X : Matrix ι ι F => X.map f) '' Set.range (matrixWord M) := by
    rw [← Set.range_comp]
    congr 1
    funext w
    exact matrixWord_map f M w
  rw [hrange]
  exact hfinite.image _

/-- Scalar extension between fields preserves and reflects zero words. -/
theorem matrixWord_map_eq_zero_iff (f : F →+* K) (M : A → Matrix ι ι F)
    (w : List A) :
    matrixWord (fun a => (M a).map f) w = 0 ↔ matrixWord M w = 0 := by
  rw [matrixWord_map]
  constructor
  · intro h
    ext i j
    apply f.injective
    simpa using congrFun (congrFun h i) j
  · intro h
    simp [h]
end ScalarExtension
end IndependentZeroBlocks
