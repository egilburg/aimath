import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Noetherian.Orzech

set_option autoImplicit false

/-!
# Compression at a minimum-length word

This is the finite-length module analogue of minimum-rank compression. Word
products use the project's chronological convention: the product attached to
`x ++ y` is the product for `x` multiplied by the product for `y`.
-/

noncomputable section

namespace IndependentZeroBlocks

variable {R A V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- Chronological product of an endomorphism-labelled word. -/
def endoWord (M : A → Module.End R V) (w : List A) : Module.End R V :=
  (w.map M).prod

@[simp] theorem endoWord_nil (M : A → Module.End R V) :
    endoWord M [] = 1 := by
  simp [endoWord]

@[simp] theorem endoWord_cons (M : A → Module.End R V) (a : A) (w : List A) :
    endoWord M (a :: w) = M a * endoWord M w := by
  simp [endoWord]

@[simp] theorem endoWord_append (M : A → Module.End R V) (x y : List A) :
    endoWord M (x ++ y) = endoWord M x * endoWord M y := by
  simp [endoWord]

/-- There is a nonempty word whose image has minimum composition length among
all nonempty word images. -/
theorem exists_minLengthWord [Nonempty A] [IsArtinian R V] [IsNoetherian R V]
    (M : A → Module.End R V) :
    ∃ h : List A, h ≠ [] ∧
      ∀ w : List A, w ≠ [] →
        Module.length R (LinearMap.range (endoWord M h)) ≤
          Module.length R (LinearMap.range (endoWord M w)) := by
  let lengths : Set ℕ∞ :=
    {n | ∃ w : List A, w ≠ [] ∧
      Module.length R (LinearMap.range (endoWord M w)) = n}
  have hlengths : lengths.Nonempty := by
    let a : A := Classical.choice inferInstance
    exact ⟨Module.length R (LinearMap.range (endoWord M [a])), [a], by simp, rfl⟩
  obtain ⟨n, hn, hnmin⟩ :=
    (IsWellFounded.wf : WellFounded ((· < ·) : ℕ∞ → ℕ∞ → Prop)).has_min lengths hlengths
  rcases hn with ⟨h, hh, rfl⟩
  refine ⟨h, hh, fun w hw ↦ ?_⟩
  exact le_of_not_gt (hnmin _ ⟨w, hw, rfl⟩)

/-- The image of the chosen reset word, used as the return module. -/
abbrev ReturnSpace (M : A → Module.End R V) (h : List A) :=
  LinearMap.range (endoWord M h)

/-- The reset endomorphism with codomain restricted to its image. -/
def resetCorestrict (M : A → Module.End R V) (h : List A) :
    V →ₗ[R] ReturnSpace M h :=
  (endoWord M h).rangeRestrict

/-- Inclusion of the return module into the ambient module. -/
def returnInclusion (M : A → Module.End R V) (h : List A) :
    ReturnSpace M h →ₗ[R] V :=
  (LinearMap.range (endoWord M h)).subtype

@[simp] theorem returnInclusion_apply (M : A → Module.End R V) (h : List A)
    (b : ReturnSpace M h) :
    returnInclusion M h b = b.1 :=
  rfl

@[simp] theorem resetCorestrict_coe (M : A → Module.End R V) (h : List A) (v : V) :
    (resetCorestrict M h v : V) = endoWord M h v :=
  rfl

/-- The reset factors as inclusion after corestriction to its image. -/
theorem reset_factorization (M : A → Module.End R V) (h : List A) :
    endoWord M h = (returnInclusion M h).comp (resetCorestrict M h) := by
  rfl

/-- Compression of a word through arbitrary boundary maps. -/
def compressedReturn {B : Type*} [AddCommGroup B] [Module R B]
    (M : A → Module.End R V) (U : B →ₗ[R] V) (V0 : V →ₗ[R] B)
    (y : List A) : Module.End R B :=
  V0.comp ((endoWord M y).comp U)

/-- Multiplication of compressed returns inserts the reset word. -/
theorem compressedReturn_mul {B : Type*} [AddCommGroup B] [Module R B]
    (M : A → Module.End R V) (h : List A)
    (U : B →ₗ[R] V) (V0 : V →ₗ[R] B)
    (hfac : endoWord M h = U.comp V0) (y z : List A) :
    compressedReturn M U V0 y * compressedReturn M U V0 z =
      compressedReturn M U V0 (y ++ h ++ z) := by
  ext b
  simp only [compressedReturn, Module.End.mul_apply, LinearMap.comp_apply,
    endoWord_append, Module.End.mul_apply, hfac]

/-- A nonempty product of compressed returns is the compressed return of the
word obtained by placing the reset between consecutive words. -/
theorem compressedReturn_prod_intercalate {B : Type*} [AddCommGroup B] [Module R B]
    (M : A → Module.End R V) (h : List A)
    (U : B →ₗ[R] V) (V0 : V →ₗ[R] B)
    (hfac : endoWord M h = U.comp V0)
    (g : List A) (gs : List (List A)) :
    ((g :: gs).map (compressedReturn M U V0)).prod =
      compressedReturn M U V0 (h.intercalate (g :: gs)) := by
  induction gs generalizing g with
  | nil => simp [List.intercalate]
  | cons z zs ih =>
      rw [show h.intercalate (g :: z :: zs) =
        g ++ h ++ h.intercalate (z :: zs) by simp [List.intercalate]]
      rw [List.map_cons, List.prod_cons, ih]
      exact compressedReturn_mul M h U V0 hfac _ _

/-- The word consisting of an initial reset, followed by each supplied word
and another reset. -/
def endoResetSandwichWord (h : List A) : List (List A) → List A
  | [] => h
  | y :: ys => h ++ y ++ endoResetSandwichWord h ys

/-- A reset-sandwich word factors through the product of its compressed
returns. -/
theorem endoWord_endoResetSandwichWord {B : Type*} [AddCommGroup B] [Module R B]
    (M : A → Module.End R V) (h : List A)
    (U : B →ₗ[R] V) (V0 : V →ₗ[R] B)
    (hfac : endoWord M h = U.comp V0) (ys : List (List A)) :
    endoWord M (endoResetSandwichWord h ys) =
      U.comp (((ys.map (compressedReturn M U V0)).prod).comp V0) := by
  induction ys with
  | nil =>
      rw [endoResetSandwichWord, hfac]
      ext b
      rfl
  | cons y ys ih =>
      ext v
      simp only [endoResetSandwichWord, endoWord_append, Module.End.mul_apply,
        hfac, LinearMap.comp_apply, ih, List.map_cons, List.prod_cons,
        compressedReturn]

/-- Whole-endomorphism factorization with arbitrary words outside a sequence
of reset-separated returns. -/
theorem endoWord_boundary_endoResetSandwichWord
    {B : Type*} [AddCommGroup B] [Module R B]
    (M : A → Module.End R V) (h x z : List A)
    (U : B →ₗ[R] V) (V0 : V →ₗ[R] B)
    (hfac : endoWord M h = U.comp V0) (ys : List (List A)) :
    endoWord M (x ++ endoResetSandwichWord h ys ++ z) =
      (endoWord M x).comp
        (U.comp (((ys.map (compressedReturn M U V0)).prod).comp
          (V0.comp (endoWord M z)))) := by
  rw [endoWord_append, endoWord_append,
    endoWord_endoResetSandwichWord M h U V0 hfac ys]
  ext v
  simp only [Module.End.mul_apply, LinearMap.comp_apply]

/-- Left boundary functional induced on the compressed module. -/
def compressedBoundaryLeft {B : Type*} [AddCommGroup B] [Module R B]
    (M : A → Module.End R V) (U : B →ₗ[R] V)
    (left : Module.Dual R V) (x : List A) : Module.Dual R B :=
  left.comp ((endoWord M x).comp U)

/-- Right boundary seed induced in the compressed module. -/
def compressedBoundarySeed {B : Type*} [AddCommGroup B] [Module R B]
    (M : A → Module.End R V) (V0 : V →ₗ[R] B)
    (seed : V) (z : List A) : B :=
  V0 (endoWord M z seed)

/-- Scalar form of the multiple-return boundary factorization. -/
theorem coefficient_boundary_endoResetSandwichWord
    {B : Type*} [AddCommGroup B] [Module R B]
    (M : A → Module.End R V) (h x z : List A)
    (U : B →ₗ[R] V) (V0 : V →ₗ[R] B)
    (hfac : endoWord M h = U.comp V0) (ys : List (List A))
    (left : Module.Dual R V) (seed : V) :
    left (endoWord M (x ++ endoResetSandwichWord h ys ++ z) seed) =
      compressedBoundaryLeft M U left x
        ((ys.map (compressedReturn M U V0)).prod
          (compressedBoundarySeed M V0 seed z)) := by
  rw [endoWord_boundary_endoResetSandwichWord M h x z U V0 hfac ys]
  rfl

/-- Compression of an arbitrary word to the return module. -/
def returnEnd (M : A → Module.End R V) (h y : List A) :
    Module.End R (ReturnSpace M h) :=
  (resetCorestrict M h).comp ((endoWord M y).comp (returnInclusion M h))

@[simp] theorem returnEnd_apply_coe (M : A → Module.End R V) (h y : List A)
    (b : ReturnSpace M h) :
    ((returnEnd M h y b : ReturnSpace M h) : V) =
      endoWord M h (endoWord M y b.1) :=
  rfl

/-- Return multiplication inserts the chosen reset word. -/
theorem returnEnd_mul (M : A → Module.End R V) (h y z : List A) :
    returnEnd M h y * returnEnd M h z =
      returnEnd M h (y ++ h ++ z) := by
  exact compressedReturn_mul M h (returnInclusion M h) (resetCorestrict M h)
    (reset_factorization M h) y z

/-- A nonempty product of return endomorphisms is a single return endomorphism
at the reset-intercalated word. -/
theorem returnEnd_prod_intercalate (M : A → Module.End R V) (h : List A)
    (g : List A) (gs : List (List A)) :
    ((g :: gs).map (returnEnd M h)).prod =
      returnEnd M h (h.intercalate (g :: gs)) := by
  exact compressedReturn_prod_intercalate M h (returnInclusion M h)
    (resetCorestrict M h) (reset_factorization M h) g gs

/-- Sandwiched word images remain inside the reset image. -/
theorem range_endoWord_append_self_le (M : A → Module.End R V) (h y : List A) :
    LinearMap.range (endoWord M (h ++ y ++ h)) ≤
      LinearMap.range (endoWord M h) := by
  rintro _ ⟨v, rfl⟩
  refine ⟨endoWord M y (endoWord M h v), ?_⟩
  simp only [endoWord_append, Module.End.mul_apply]

/-- Minimum image length forces every reset sandwich to have exactly the reset
image. -/
theorem range_endoWord_append_self_eq_of_minLength
    [IsArtinian R V] [IsNoetherian R V]
    (M : A → Module.End R V) (h : List A) (hh : h ≠ [])
    (hmin : ∀ w : List A, w ≠ [] →
      Module.length R (LinearMap.range (endoWord M h)) ≤
        Module.length R (LinearMap.range (endoWord M w)))
    (y : List A) :
    LinearMap.range (endoWord M (h ++ y ++ h)) =
      LinearMap.range (endoWord M h) := by
  apply le_antisymm (range_endoWord_append_self_le M h y)
  by_contra hnot
  have hne : LinearMap.range (endoWord M (h ++ y ++ h)) ≠
      LinearMap.range (endoWord M h) := by
    intro heq
    exact hnot heq.ge
  have hlt : LinearMap.range (endoWord M (h ++ y ++ h)) <
      LinearMap.range (endoWord M h) :=
    lt_of_le_of_ne (range_endoWord_append_self_le M h y) hne
  have hlengthlt :
      Module.length R (LinearMap.range (endoWord M (h ++ y ++ h))) <
        Module.length R (LinearMap.range (endoWord M h)) := by
    simpa only [Module.length_submodule] using Submodule.height_strictMono hlt
  have hword : h ++ y ++ h ≠ [] := by
    intro heq
    rcases List.append_eq_nil_iff.mp heq with ⟨hhy, -⟩
    rcases List.append_eq_nil_iff.mp hhy with ⟨hh0, -⟩
    exact hh hh0
  exact (not_lt_of_ge (hmin _ hword)) hlengthlt

/-- Every return compression at a minimum-length reset is surjective. -/
theorem returnEnd_surjective_of_minLength
    [IsArtinian R V] [IsNoetherian R V]
    (M : A → Module.End R V) (h : List A) (hh : h ≠ [])
    (hmin : ∀ w : List A, w ≠ [] →
      Module.length R (LinearMap.range (endoWord M h)) ≤
        Module.length R (LinearMap.range (endoWord M w)))
    (y : List A) :
    Function.Surjective (returnEnd M h y) := by
  intro b
  have hb : (b.1 : V) ∈ LinearMap.range (endoWord M h) := b.2
  rw [← range_endoWord_append_self_eq_of_minLength M h hh hmin y] at hb
  rcases hb with ⟨v, hv⟩
  refine ⟨resetCorestrict M h v, ?_⟩
  apply Subtype.ext
  simpa only [returnEnd_apply_coe, resetCorestrict_coe, endoWord_append,
    Module.End.mul_apply] using hv

/-- Every return compression at a minimum-length reset is bijective. -/
theorem returnEnd_bijective_of_minLength
    [IsArtinian R V] [IsNoetherian R V]
    (M : A → Module.End R V) (h : List A) (hh : h ≠ [])
    (hmin : ∀ w : List A, w ≠ [] →
      Module.length R (LinearMap.range (endoWord M h)) ≤
        Module.length R (LinearMap.range (endoWord M w)))
    (y : List A) :
    Function.Bijective (returnEnd M h y) := by
  apply IsNoetherian.bijective_of_surjective_endomorphism
  exact returnEnd_surjective_of_minLength M h hh hmin y

/-- A return compression packaged as a linear automorphism. -/
def returnLinearEquiv
    [IsArtinian R V] [IsNoetherian R V]
    (M : A → Module.End R V) (h : List A) (hh : h ≠ [])
    (hmin : ∀ w : List A, w ≠ [] →
      Module.length R (LinearMap.range (endoWord M h)) ≤
        Module.length R (LinearMap.range (endoWord M w)))
    (y : List A) : ReturnSpace M h ≃ₗ[R] ReturnSpace M h :=
  LinearEquiv.ofBijective (returnEnd M h y)
    (returnEnd_bijective_of_minLength M h hh hmin y)

@[simp] theorem returnLinearEquiv_toLinearMap
    [IsArtinian R V] [IsNoetherian R V]
    (M : A → Module.End R V) (h : List A) (hh : h ≠ [])
    (hmin : ∀ w : List A, w ≠ [] →
      Module.length R (LinearMap.range (endoWord M h)) ≤
        Module.length R (LinearMap.range (endoWord M w)))
    (y : List A) :
    (returnLinearEquiv M h hh hmin y).toLinearMap = returnEnd M h y := by
  rfl

@[simp] theorem returnLinearEquiv_apply
    [IsArtinian R V] [IsNoetherian R V]
    (M : A → Module.End R V) (h : List A) (hh : h ≠ [])
    (hmin : ∀ w : List A, w ≠ [] →
      Module.length R (LinearMap.range (endoWord M h)) ≤
        Module.length R (LinearMap.range (endoWord M w)))
    (y : List A) (b : ReturnSpace M h) :
    returnLinearEquiv M h hh hmin y b = returnEnd M h y b := by
  rfl

/-- Return linear equivalences obey the same reset multiplication law as their
underlying endomorphisms. -/
theorem returnLinearEquiv_mul
    [IsArtinian R V] [IsNoetherian R V]
    (M : A → Module.End R V) (h : List A) (hh : h ≠ [])
    (hmin : ∀ w : List A, w ≠ [] →
      Module.length R (LinearMap.range (endoWord M h)) ≤
        Module.length R (LinearMap.range (endoWord M w)))
    (y z : List A) :
    returnLinearEquiv M h hh hmin y * returnLinearEquiv M h hh hmin z =
      returnLinearEquiv M h hh hmin (y ++ h ++ z) := by
  apply LinearEquiv.ext
  intro b
  simp only [LinearEquiv.mul_apply, returnLinearEquiv_apply]
  exact LinearMap.congr_fun (returnEnd_mul M h y z) b

/-- A minimum-length reset exists and all of its return compressions are
bijective. -/
theorem exists_minLengthWord_returnEnd_bijective
    [Nonempty A] [IsArtinian R V] [IsNoetherian R V]
    (M : A → Module.End R V) :
    ∃ h : List A, h ≠ [] ∧
      (∀ w : List A, w ≠ [] →
        Module.length R (LinearMap.range (endoWord M h)) ≤
          Module.length R (LinearMap.range (endoWord M w))) ∧
      ∀ y : List A, Function.Bijective (returnEnd M h y) := by
  obtain ⟨h, hh, hmin⟩ := exists_minLengthWord M
  exact ⟨h, hh, hmin, returnEnd_bijective_of_minLength M h hh hmin⟩

end IndependentZeroBlocks
