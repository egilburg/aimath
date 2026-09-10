import SierpinskiFormal.FiniteModuleWordRepresentation

set_option autoImplicit false

/-!
# Reversible actions through signed words

An inverse letter is evaluated by the inverse linear equivalence on the
original finite module.  Its chosen matrix lift on a finite free cover need
not itself be invertible.
-/

noncomputable section

namespace IndependentZeroBlocks

/-- A generator letter or a formal inverse-generator letter. -/
abbrev SignedLetter (A : Type*) := A ⊕ A

/-- The endomorphism represented by a signed letter in a family of linear
automorphisms. -/
def signedLinearAction {K V A : Type*} [CommRing K] [AddCommGroup V]
    [Module K V] (T : A → V ≃ₗ[K] V) : SignedLetter A → Module.End K V
  | Sum.inl r => (T r).toLinearMap
  | Sum.inr r => (T r).symm.toLinearMap

@[simp] theorem signedLinearAction_positive
    {K V A : Type*} [CommRing K] [AddCommGroup V] [Module K V]
    (T : A → V ≃ₗ[K] V) (r : A) :
    signedLinearAction T (Sum.inl r) = (T r).toLinearMap := rfl

@[simp] theorem signedLinearAction_negative
    {K V A : Type*} [CommRing K] [AddCommGroup V] [Module K V]
    (T : A → V ≃ₗ[K] V) (r : A) :
    signedLinearAction T (Sum.inr r) = (T r).symm.toLinearMap := rfl

/-- Signed words in automorphisms have finite coordinate matrices preserving
every scalar evaluation.  The resulting inverse-letter matrices are lifts
through a finite free cover and are not claimed to be invertible. -/
theorem finiteModule_exists_signed_matrix_word_representation
    {K V A : Type*} [CommRing K] [AddCommGroup V] [Module K V]
    [Module.Finite K V]
    (T : A → V ≃ₗ[K] V) (l : Module.Dual K V) (v : V) :
    ∃ (d : ℕ)
      (M : SignedLetter A → Matrix (Fin d) (Fin d) K)
      (u a : Fin d → K),
      ∀ w : List (SignedLetter A),
        coordinateRowDual a
            (linearWord (fun r ↦ Matrix.mulVecLin (M r)) w u) =
          l (linearWord (signedLinearAction T) w v) :=
  finiteModule_exists_matrix_word_representation (signedLinearAction T) l v

/-- Every scalar support kernel formed from signed words in automorphisms of
a finite module has the Boolean double-limit property.  No invertibility is
required of the coordinate matrices supplied by the proof. -/
theorem finiteModule_signedWordNonzeroBool_hasBooleanDoubleLimitProperty
    {K V A : Type*} [CommRing K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] [Fintype A]
    (T : A → V ≃ₗ[K] V) (l : Module.Dual K V) (v : V) :
    HasBooleanDoubleLimitProperty
      (fun x y : List (SignedLetter A) ↦
        nonzeroBool (l (linearWord (signedLinearAction T) (x ++ y) v))) :=
  finiteModule_wordNonzeroBool_hasBooleanDoubleLimitProperty
    (signedLinearAction T) l v

/-- Evaluation of a signed letter in a group. -/
def signedGroupLetter {A Γ : Type*} [Group Γ] (g : A → Γ) :
    SignedLetter A → Γ
  | Sum.inl r => g r
  | Sum.inr r => (g r)⁻¹

/-- Ordered product of a signed word.  This order agrees with `linearWord`:
the leftmost letter acts last on vectors because multiplication of
endomorphisms is composition. -/
def signedWordProduct {A Γ : Type*} [Group Γ] (g : A → Γ)
    (w : List (SignedLetter A)) : Γ :=
  (w.map (signedGroupLetter g)).prod

@[simp] theorem signedWordProduct_nil
    {A Γ : Type*} [Group Γ] (g : A → Γ) :
    signedWordProduct g [] = 1 := by
  simp [signedWordProduct]

@[simp] theorem signedWordProduct_cons
    {A Γ : Type*} [Group Γ] (g : A → Γ) (r : SignedLetter A)
    (w : List (SignedLetter A)) :
    signedWordProduct g (r :: w) = signedGroupLetter g r * signedWordProduct g w := by
  simp [signedWordProduct]

theorem signedWordProduct_append
    {A Γ : Type*} [Group Γ] (g : A → Γ)
    (x y : List (SignedLetter A)) :
    signedWordProduct g (x ++ y) = signedWordProduct g x * signedWordProduct g y := by
  simp [signedWordProduct]

/-- A group action by linear equivalences, viewed as an endomorphism family. -/
def groupLinearAction {K V Γ : Type*} [CommRing K] [AddCommGroup V]
    [Module K V] [Group Γ] (ρ : Γ →* (V ≃ₗ[K] V)) : Γ → Module.End K V :=
  fun γ ↦ (ρ γ).toLinearMap

/-- A signed word in chosen group elements acts as its group product. -/
theorem linearWord_signedGroupAction
    {K V A Γ : Type*} [CommRing K] [AddCommGroup V] [Module K V]
    [Group Γ] (ρ : Γ →* (V ≃ₗ[K] V)) (g : A → Γ)
    (w : List (SignedLetter A)) :
    linearWord (signedLinearAction fun r ↦ ρ (g r)) w =
      (ρ (signedWordProduct g w)).toLinearMap := by
  induction w with
  | nil =>
      rw [linearWord_nil, signedWordProduct_nil, map_one]
      rfl
  | cons r w ih =>
      rw [linearWord_cons, ih, signedWordProduct_cons, map_mul]
      cases r with
      | inl r => rfl
      | inr r =>
          simp only [signedLinearAction, signedGroupLetter]
          rw [map_inv]
          rfl

/-- Under chosen signed-word representatives, the same finite matrices give
the scalar observation of every element of the represented group. -/
theorem finiteModule_exists_signed_matrix_group_representation
    {K V A Γ : Type*} [CommRing K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] [Group Γ]
    (ρ : Γ →* (V ≃ₗ[K] V)) (g : A → Γ)
    (wordRep : Γ → List (SignedLetter A))
    (hrep : ∀ γ, signedWordProduct g (wordRep γ) = γ)
    (l : Module.Dual K V) (v : V) :
    ∃ (d : ℕ)
      (M : SignedLetter A → Matrix (Fin d) (Fin d) K)
      (u a : Fin d → K),
      ∀ γ : Γ,
        coordinateRowDual a
            (linearWord (fun r ↦ Matrix.mulVecLin (M r)) (wordRep γ) u) =
          l ((ρ γ) v) := by
  obtain ⟨d, M, u, a, hM⟩ :=
    finiteModule_exists_signed_matrix_word_representation
      (fun r ↦ ρ (g r)) l v
  refine ⟨d, M, u, a, ?_⟩
  intro γ
  rw [hM, linearWord_signedGroupAction, hrep]
  rfl

/-- A chosen signed-word representative for every group element pulls the
signed-word double-limit theorem back to the intrinsic group multiplication
kernel. -/
theorem finiteModule_groupNonzeroBool_hasBooleanDoubleLimitProperty_of_signed_reps
    {K V A Γ : Type*} [CommRing K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] [Fintype A] [Group Γ]
    (ρ : Γ →* (V ≃ₗ[K] V)) (g : A → Γ)
    (wordRep : Γ → List (SignedLetter A))
    (hrep : ∀ γ, signedWordProduct g (wordRep γ) = γ)
    (l : Module.Dual K V) (v : V) :
    HasBooleanDoubleLimitProperty
      (fun γ δ : Γ ↦ nonzeroBool (l ((ρ (γ * δ)) v))) := by
  have hsigned :=
    finiteModule_signedWordNonzeroBool_hasBooleanDoubleLimitProperty
      (fun r ↦ ρ (g r)) l v
  intro x y rowLimit columnLimit rowOuter columnOuter
    hrow hcolumn hrowOuter hcolumnOuter
  apply hsigned (wordRep ∘ x) (wordRep ∘ y)
    rowLimit columnLimit rowOuter columnOuter
  · simpa only [Function.comp_apply, linearWord_signedGroupAction,
      signedWordProduct_append, hrep, LinearEquiv.coe_coe] using hrow
  · simpa only [Function.comp_apply, linearWord_signedGroupAction,
      signedWordProduct_append, hrep, LinearEquiv.coe_coe] using hcolumn
  · exact hrowOuter
  · exact hcolumnOuter

/-- Intrinsically, an action of the whole group needs no choice of generator
words: singleton words already give its multiplication kernel. -/
theorem finiteModule_groupNonzeroBool_hasBooleanDoubleLimitProperty
    {K V Γ : Type*} [CommRing K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] [Group Γ] [Fintype Γ]
    (ρ : Γ →* (V ≃ₗ[K] V)) (l : Module.Dual K V) (v : V) :
    HasBooleanDoubleLimitProperty
      (fun γ δ : Γ ↦ nonzeroBool (l ((ρ (γ * δ)) v))) := by
  have hwords := finiteModule_wordNonzeroBool_hasBooleanDoubleLimitProperty
    (groupLinearAction ρ) l v
  intro x y rowLimit columnLimit rowOuter columnOuter
    hrow hcolumn hrowOuter hcolumnOuter
  apply hwords (fun i ↦ [x i]) (fun j ↦ [y j])
    rowLimit columnLimit rowOuter columnOuter
  · simpa [groupLinearAction, linearWord] using hrow
  · simpa [groupLinearAction, linearWord] using hcolumn
  · exact hrowOuter
  · exact hcolumnOuter

end IndependentZeroBlocks
