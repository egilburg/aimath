import SierpinskiFormal.ArtinianBlockDensity
import SierpinskiFormal.ModuleBooleanReturnMean

/-!
# One reset and one rational boundary family for finite Boolean observations

All scalar rows below observe one endomorphism action and one seed.  Hence a
minimum-length word is selected from the action alone, before the Boolean
operation, the rows, and every positive letter law are evaluated.  The
resulting blocked return action supplies rational central Boolean means and
the explicit full word-Cesaro boundary formula.
-/

set_option autoImplicit false
noncomputable section

open Filter Set
open scoped BigOperators Topology

namespace IndependentZeroBlocks

variable {R A V B : Type*} [CommRing R]
variable [AddCommGroup V] [Module R V]
variable [AddCommGroup B] [Module R B]

/-- A finite Boolean operation on scalar rows of one module word action. -/
def moduleBooleanCoefficientNonzero {d : ℕ}
    (op : (Fin d → Bool) → Bool) (M : A → Module.End R V)
    (left : Fin d → Module.Dual R V) (seed : V) (w : List A) : Bool :=
  op (fun j ↦ moduleCoefficientNonzero M (left j) seed w)

/-- With fixed exterior gaps, apply the same Boolean operation to all
compressed boundary rows. -/
def moduleBooleanBoundaryCentralPredicate {d : ℕ}
    (op : (Fin d → Bool) → Bool)
    (M : A → Module.End R V) (U : B →ₗ[R] V) (V0 : V →ₗ[R] B)
    (left : Fin d → Module.Dual R V) (seed : V)
    (x z y : List A) : Bool :=
  op (fun j ↦ moduleBoundaryCentralPredicate M U V0 (left j) seed x z y)

/-- The reset boundary identity holds simultaneously for all Boolean rows. -/
theorem moduleBooleanCoefficientNonzero_boundary {d : ℕ}
    (op : (Fin d → Bool) → Bool)
    (M : A → Module.End R V) (e : A)
    (U : B →ₗ[R] V) (V0 : V →ₗ[R] B)
    (hfac : endoWord M [e] = U.comp V0)
    (left : Fin d → Module.Dual R V) (seed : V) (x y z : List A) :
    moduleBooleanCoefficientNonzero op M left seed
        (x ++ [e] ++ y ++ [e] ++ z) =
      moduleBooleanBoundaryCentralPredicate op M U V0 left seed x z y := by
  apply congrArg op
  funext j
  exact moduleCoefficientNonzero_boundary
    M e U V0 hfac (left j) seed x y z

variable [TopologicalSpace A] [DiscreteTopology A]
variable [Fintype A] [Nonempty A] [DecidableEq A]

/-- Exact middle-word averages for a fixed pair of exterior marker gaps. -/
def moduleBooleanBoundaryCentralSequence {d : ℕ}
    (op : (Fin d → Bool) → Bool) {e : A} (p : A → ℝ)
    (M : A → Module.End R V) (U : B →ₗ[R] V) (V0 : V →ₗ[R] B)
    (left : Fin d → Module.Dual R V) (seed : V)
    (i : GapWords e × GapWords e) (n : ℕ) : ℝ :=
  abstractBoundaryCentralSequence p
    (moduleBooleanBoundaryCentralPredicate op M U V0 left seed) i n

/-- A Boolean boundary central sequence is the common-seed Boolean central
return average with its exterior-gap rows and seed. -/
theorem moduleBooleanBoundaryCentralSequence_eq_centralReturnExactAverage
    {d : ℕ} (op : (Fin d → Bool) → Bool) {e : A} (p : A → ℝ)
    (M : A → Module.End R V) (U : B →ₗ[R] V) (V0 : V →ₗ[R] B)
    (left : Fin d → Module.Dual R V) (seed : V)
    (i : GapWords e × GapWords e) :
    moduleBooleanBoundaryCentralSequence op p M U V0 left seed i =
      moduleBooleanCentralReturnExactAverage op M U V0
        (fun j ↦ compressedBoundaryLeft M U (left j) i.1.1)
        (compressedBoundarySeed M V0 seed i.2.1) p := by
  rfl

/-- Rational Boolean boundary means for an already supplied reset with
bijective compressed returns, followed by the full boundary mixture. -/
theorem exists_rational_moduleBooleanBoundaryMeans_forall_positive_laws
    [IsNoetherian R V] [IsNoetherian R (Module.Dual R V)]
    [IsNoetherian R B] [IsNoetherian R (Module.Dual R B)]
    {d : ℕ} (op : (Fin d → Bool) → Bool)
    (M : A → Module.End R V) (e : A)
    (U : B →ₗ[R] V) (V0 : V →ₗ[R] B)
    (hfac : endoWord M [e] = U.comp V0)
    (hbij : ∀ y : List A, Function.Bijective (compressedReturn M U V0 y))
    (left : Fin d → Module.Dual R V) (seed : V) :
    ∃ m : GapWords e × GapWords e → ℚ,
      ∀ (p : A → ℝ), (∀ a, 0 < p a) → (∑ a, p a = 1) →
        ((∀ i, Tendsto
          (realCesaroMean
            (moduleBooleanBoundaryCentralSequence
              op p M U V0 left seed i))
          atTop (nhds (m i : ℝ))) ∧
        Tendsto
          (realCesaroMean (fun n ↦ weightedWordExtensionAverage p
            (booleanWordIndicator
              (moduleBooleanCoefficientNonzero op M left seed)) n []))
          atTop (nhds (∑' i,
            moduleBoundaryWeight p e i * (m i : ℝ)))) := by
  let K : List A → (B ≃ₗ[R] B) := fun y ↦
    LinearEquiv.ofBijective (compressedReturn M U V0 y) (hbij y)
  have hK : ∀ y, (K y).toLinearMap = compressedReturn M U V0 y := by
    intro y
    rfl
  have hcentral : ∀ i : GapWords e × GapWords e,
      ∃ q : ℚ, ∀ (p : A → ℝ), (∀ a, 0 < p a) → (∑ a, p a = 1) →
        Tendsto
          (realCesaroMean
            (moduleBooleanBoundaryCentralSequence
              op p M U V0 left seed i))
          atTop (nhds (q : ℝ)) := by
    intro i
    simpa only [
      moduleBooleanBoundaryCentralSequence_eq_centralReturnExactAverage]
      using exists_rational_forall_tendsto_moduleBooleanCentralReturnCesaro
        op M e U V0 hfac K hK
        (fun j ↦ compressedBoundaryLeft M U (left j) i.1.1)
        (compressedBoundarySeed M V0 seed i.2.1)
  choose m hm using hcentral
  refine ⟨m, ?_⟩
  intro p hp hp1
  have hm' : ∀ i, Tendsto
      (realCesaroMean
        (moduleBooleanBoundaryCentralSequence op p M U V0 left seed i))
      atTop (nhds (m i : ℝ)) := fun i ↦ hm i p hp hp1
  refine ⟨hm', ?_⟩
  exact tendsto_weightedPredicate_of_boundary_cesaro
    p (fun a ↦ (hp a).le) hp1 e (hp e)
    (moduleBooleanCoefficientNonzero op M left seed)
    (moduleBooleanBoundaryCentralPredicate op M U V0 left seed)
    (moduleBooleanCoefficientNonzero_boundary op M e U V0 hfac left seed)
    (fun i ↦ (m i : ℝ)) hm'

/-- Boolean block observations move a residual suffix into the common seed. -/
@[simp] theorem moduleBoolean_block_suffix {d : ℕ}
    (op : (Fin d → Bool) → Bool) (T : A → Module.End R V) (ell : ℕ)
    (left : Fin d → Module.Dual R V) (seed : V)
    (w : List (Fin ell → A)) (xi : List A) :
    moduleBooleanCoefficientNonzero op (blockEndomorphism T ell) left
        (moduleSuffixSeed T xi seed) w =
      moduleBooleanCoefficientNonzero op T left seed
        (flattenBlocks ell w ++ xi) := by
  apply congrArg op
  funext j
  exact nonzeroBool_block_suffix T ell (left j) seed w xi

section ResidueLimit

/-- Block-word Boolean limits determine the limit along one physical residue
class after summing over residual suffixes. -/
theorem tendsto_moduleBoolean_residue_of_blockLimits {d : ℕ}
    (op : (Fin d → Bool) → Bool)
    (p : A → ℝ) (T : A → Module.End R V)
    (left : Fin d → Module.Dual R V) (seed : V)
    (ell s : ℕ) (L : (Fin s → A) → ℝ)
    (hL : ∀ xi : Fin s → A,
      Tendsto
        (realCesaroMean (fun N ↦
          weightedWordExtensionAverage (blockWeight p ell)
            (booleanWordIndicator
              (moduleBooleanCoefficientNonzero op
                (blockEndomorphism T ell) left
                (moduleSuffixSeed T (List.ofFn xi) seed))) N []))
        atTop (nhds (L xi))) :
    Tendsto
      (realCesaroMean (fun N ↦ weightedWordExtensionAverage p
        (booleanWordIndicator
          (moduleBooleanCoefficientNonzero op T left seed))
        (N * ell + s) []))
      atTop (nhds (∑ xi : Fin s → A,
        wordWeight p (List.ofFn xi) * L xi)) := by
  let q : List A → Bool := moduleBooleanCoefficientNonzero op T left seed
  let c : (Fin s → A) → ℕ → ℝ := fun xi N ↦
    weightedWordExtensionAverage (blockWeight p ell)
      (booleanWordIndicator (fun w : List (Fin ell → A) ↦
        q (flattenBlocks ell w ++ List.ofFn xi))) N []
  have hc : ∀ xi : Fin s → A,
      Tendsto (realCesaroMean (c xi)) atTop (nhds (L xi)) := by
    intro xi
    have hpred : (fun w : List (Fin ell → A) ↦
        q (flattenBlocks ell w ++ List.ofFn xi)) =
        moduleBooleanCoefficientNonzero op (blockEndomorphism T ell) left
          (moduleSuffixSeed T (List.ofFn xi) seed) := by
      funext w
      exact (moduleBoolean_block_suffix op T ell left seed w
        (List.ofFn xi)).symm
    simpa only [c, hpred] using hL xi
  have heq : (fun N ↦ weightedWordExtensionAverage p
      (booleanWordIndicator q) (N * ell + s) []) =
      fun N ↦ ∑ xi : Fin s → A,
        wordWeight p (List.ofFn xi) * c xi N := by
    funext N
    exact weightedBooleanWordExtension_mul_add_eq_block_suffix p q N ell s
  change Tendsto
    (realCesaroMean (fun N ↦ weightedWordExtensionAverage p
      (booleanWordIndicator q) (N * ell + s) [])) _ _
  rw [heq]
  have hmean (N : ℕ) :
      realCesaroMean (fun n ↦ ∑ xi : Fin s → A,
        wordWeight p (List.ofFn xi) * c xi n) N =
      ∑ xi : Fin s → A,
        wordWeight p (List.ofFn xi) * realCesaroMean (c xi) N := by
    rw [realCesaroMean_finset_sum Finset.univ
      (fun xi n ↦ wordWeight p (List.ofFn xi) * c xi n)]
    apply Finset.sum_congr rfl
    intro xi hxi
    unfold realCesaroMean
    rw [← Finset.mul_sum]
    ring
  have ht : Tendsto
      (fun N ↦ ∑ xi : Fin s → A,
        wordWeight p (List.ofFn xi) * realCesaroMean (c xi) N)
      atTop (nhds (∑ xi : Fin s → A,
        wordWeight p (List.ofFn xi) * L xi)) := by
    apply tendsto_finset_sum Finset.univ
    intro xi hxi
    exact (hc xi).const_mul _
  convert ht using 1
  funext N
  exact hmean N

/-- If the unrestricted Boolean Cesaro limit exists, all suffix block limits
identify it as the arithmetic average of their residue mixtures. -/
theorem moduleBooleanLimit_eq_average_blockLimits {d : ℕ}
    (op : (Fin d → Bool) → Bool)
    (p : A → ℝ) (T : A → Module.End R V)
    (left : Fin d → Module.Dual R V) (seed : V)
    (ell : ℕ) (hell : 0 < ell) (L : ℝ)
    (Q : (s : Fin ell) → (Fin (s : ℕ) → A) → ℝ)
    (hfull : Tendsto
      (realCesaroMean (fun n ↦ weightedWordExtensionAverage p
        (booleanWordIndicator
          (moduleBooleanCoefficientNonzero op T left seed)) n []))
      atTop (nhds L))
    (hblock : ∀ (s : Fin ell) (xi : Fin (s : ℕ) → A),
      Tendsto
        (realCesaroMean (fun N ↦
          weightedWordExtensionAverage (blockWeight p ell)
            (booleanWordIndicator
              (moduleBooleanCoefficientNonzero op
                (blockEndomorphism T ell) left
                (moduleSuffixSeed T (List.ofFn xi) seed))) N []))
        atTop (nhds (Q s xi))) :
    L = (∑ s : Fin ell, ∑ xi : Fin (s : ℕ) → A,
      wordWeight p (List.ofFn xi) * Q s xi) / (ell : ℝ) := by
  apply cesaroLimit_eq_average_residueLimits
    (fun n ↦ weightedWordExtensionAverage p
      (booleanWordIndicator
        (moduleBooleanCoefficientNonzero op T left seed)) n [])
    ell hell L
    (fun s ↦ ∑ xi : Fin (s : ℕ) → A,
      wordWeight p (List.ofFn xi) * Q s xi) hfull
  intro s
  exact tendsto_moduleBoolean_residue_of_blockLimits
    op p T left seed ell s (Q s) (fun xi ↦ hblock s xi)

end ResidueLimit

section ArtinianBooleanFormula

variable [IsArtinianRing R] [Module.Finite R V]

/-- A single minimum-length reset for an Artinian module action, chosen
before the size, operation, rows, common seed, and every positive letter law.
Each later Boolean observation has one rational central family, and its full
physical word-Cesaro density is the displayed boundary expression. -/
theorem exists_commonReset_moduleBooleanBoundaryMeans_forall_positive_laws
    (T : A → Module.End R V) :
    ∃ h : List A, h ≠ [] ∧
      (∀ w : List A, w ≠ [] →
        Module.length R (LinearMap.range (endoWord T h)) ≤
          Module.length R (LinearMap.range (endoWord T w))) ∧
      ∃ (U : ReturnSpace T h →ₗ[R] V) (V0 : V →ₗ[R] ReturnSpace T h),
        endoWord T h = U.comp V0 ∧
        (∀ y : List (Fin h.length → A),
          Function.Bijective
            (compressedReturn (blockEndomorphism T h.length) U V0 y)) ∧
        ∀ (d : ℕ) (op : (Fin d → Bool) → Bool)
            (left : Fin d → Module.Dual R V) (seed : V),
          ∃ m : (s : Fin h.length) → (Fin (s : ℕ) → A) →
              GapWords (endoMarkerBlock h) × GapWords (endoMarkerBlock h) → ℚ,
            ∀ (p : A → ℝ), (∀ a, 0 < p a) → (∑ a, p a = 1) →
            ((∀ (s : Fin h.length) (xi : Fin (s : ℕ) → A)
                (i : GapWords (endoMarkerBlock h) ×
                  GapWords (endoMarkerBlock h)),
                Tendsto
                  (realCesaroMean (moduleBooleanBoundaryCentralSequence op
                    (blockWeight p h.length) (blockEndomorphism T h.length)
                    U V0 left (moduleSuffixSeed T (List.ofFn xi) seed) i))
                  atTop (nhds (m s xi i : ℝ))) ∧
              Tendsto
                (realCesaroMean (fun n ↦ weightedWordExtensionAverage p
                  (booleanWordIndicator
                    (moduleBooleanCoefficientNonzero op T left seed)) n []))
                atTop (nhds ((∑ s : Fin h.length,
                  ∑ xi : Fin (s : ℕ) → A,
                    wordWeight p (List.ofFn xi) *
                      (∑' i : GapWords (endoMarkerBlock h) ×
                          GapWords (endoMarkerBlock h),
                        moduleBoundaryWeight (blockWeight p h.length)
                          (endoMarkerBlock h) i * (m s xi i : ℝ))) /
                  (h.length : ℝ)))) := by
  classical
  obtain ⟨h, hh, hmin⟩ := exists_minLengthWord T
  let U : ReturnSpace T h →ₗ[R] V := returnInclusion T h
  let V0 : V →ₗ[R] ReturnSpace T h := resetCorestrict T h
  have hfac : endoWord T h = U.comp V0 := reset_factorization T h
  have hell : 0 < h.length := List.length_pos_iff.mpr hh
  have hfacBlock :
      endoWord (blockEndomorphism T h.length) [endoMarkerBlock h] =
        U.comp V0 := block_reset_factorization T h
  have hbijBlock : ∀ y : List (Fin h.length → A),
      Function.Bijective
        (compressedReturn (blockEndomorphism T h.length) U V0 y) := by
    intro y
    exact blockReturn_bijective_of_minLength T h hh hmin y
  refine ⟨h, hh, hmin, U, V0, hfac, hbijBlock, ?_⟩
  intro d op left seed
  have hall : ∀ (s : Fin h.length) (xi : Fin (s : ℕ) → A),
      ∃ m : GapWords (endoMarkerBlock h) × GapWords (endoMarkerBlock h) → ℚ,
        ∀ (pblock : (Fin h.length → A) → ℝ),
          (∀ c, 0 < pblock c) → (∑ c, pblock c = 1) →
            ((∀ i, Tendsto
              (realCesaroMean (moduleBooleanBoundaryCentralSequence op
                pblock (blockEndomorphism T h.length) U V0 left
                (moduleSuffixSeed T (List.ofFn xi) seed) i))
              atTop (nhds (m i : ℝ))) ∧
            Tendsto
              (realCesaroMean (fun n ↦ weightedWordExtensionAverage pblock
                (booleanWordIndicator (moduleBooleanCoefficientNonzero op
                  (blockEndomorphism T h.length) left
                  (moduleSuffixSeed T (List.ofFn xi) seed))) n []))
              atTop (nhds (∑' i : GapWords (endoMarkerBlock h) ×
                  GapWords (endoMarkerBlock h),
                moduleBoundaryWeight pblock (endoMarkerBlock h) i *
                  (m i : ℝ)))) := by
    intro s xi
    exact exists_rational_moduleBooleanBoundaryMeans_forall_positive_laws
      op (blockEndomorphism T h.length) (endoMarkerBlock h)
      U V0 hfacBlock hbijBlock left
      (moduleSuffixSeed T (List.ofFn xi) seed)
  choose m hm using hall
  refine ⟨m, ?_⟩
  intro p hp hp1
  have hblockPos : ∀ c : Fin h.length → A,
      0 < blockWeight p h.length c := by
    intro c
    simp only [blockWeight, wordWeight]
    induction List.ofFn c with
    | nil => simp
    | cons a w ih =>
        simp only [List.map_cons, List.prod_cons]
        exact mul_pos (hp a) ih
  have hblockSum : ∑ c : Fin h.length → A,
      blockWeight p h.length c = 1 :=
    sum_blockWeight_eq_one p hp1 h.length
  have hcentral : ∀ (s : Fin h.length) (xi : Fin (s : ℕ) → A)
      (i : GapWords (endoMarkerBlock h) × GapWords (endoMarkerBlock h)),
      Tendsto
        (realCesaroMean (moduleBooleanBoundaryCentralSequence op
          (blockWeight p h.length) (blockEndomorphism T h.length)
          U V0 left (moduleSuffixSeed T (List.ofFn xi) seed) i))
        atTop (nhds (m s xi i : ℝ)) := by
    intro s xi i
    exact (hm s xi (blockWeight p h.length) hblockPos hblockSum).1 i
  have hblock : ∀ (s : Fin h.length) (xi : Fin (s : ℕ) → A),
      Tendsto
        (realCesaroMean (fun N ↦
          weightedWordExtensionAverage (blockWeight p h.length)
            (booleanWordIndicator (moduleBooleanCoefficientNonzero op
              (blockEndomorphism T h.length) left
              (moduleSuffixSeed T (List.ofFn xi) seed))) N []))
        atTop (nhds (∑' i : GapWords (endoMarkerBlock h) ×
            GapWords (endoMarkerBlock h),
          moduleBoundaryWeight (blockWeight p h.length)
            (endoMarkerBlock h) i * (m s xi i : ℝ))) := by
    intro s xi
    exact (hm s xi (blockWeight p h.length) hblockPos hblockSum).2
  obtain ⟨L, hL⟩ := exists_tendsto_boolean_weighted_iid_word_cesaro
    p (fun a ↦ (hp a).le) hp1
    (moduleBooleanCoefficientNonzero op T left seed)
    (by
      change HasBooleanDoubleLimitProperty
        (booleanCombine op (fun j (w z : List A) ↦
          nonzeroBool ((left j) (linearWord T (z ++ w) seed))))
      exact hasBooleanDoubleLimitProperty_booleanCombine op
          (fun j (w z : List A) ↦
            nonzeroBool ((left j) (linearWord T (z ++ w) seed)))
          (fun j ↦ noetherian_linearWord_rightKernel_hasBooleanDoubleLimitProperty
            T (left j) seed))
  have hfull : Tendsto
      (realCesaroMean (fun n ↦ weightedWordExtensionAverage p
        (booleanWordIndicator
          (moduleBooleanCoefficientNonzero op T left seed)) n []))
      atTop (nhds L) := by
    rw [show realCesaroMean (fun n ↦ weightedWordExtensionAverage p
        (booleanWordIndicator
          (moduleBooleanCoefficientNonzero op T left seed)) n []) =
        weightedIidWordCesaro p
          (booleanWordIndicator
            (moduleBooleanCoefficientNonzero op T left seed)) by
      funext N
      simp only [realCesaroMean, weightedIidWordCesaro, div_eq_mul_inv]
      ring]
    exact hL
  let Q : (s : Fin h.length) → (Fin (s : ℕ) → A) → ℝ := fun s xi ↦
    ∑' i : GapWords (endoMarkerBlock h) × GapWords (endoMarkerBlock h),
      moduleBoundaryWeight (blockWeight p h.length) (endoMarkerBlock h) i *
        (m s xi i : ℝ)
  have hEq : L = (∑ s : Fin h.length, ∑ xi : Fin (s : ℕ) → A,
      wordWeight p (List.ofFn xi) * Q s xi) / (h.length : ℝ) :=
    moduleBooleanLimit_eq_average_blockLimits
      op p T left seed h.length hell L Q hfull hblock
  refine ⟨hcentral, ?_⟩
  simpa only [Q, hEq] using hfull

end ArtinianBooleanFormula

end IndependentZeroBlocks
