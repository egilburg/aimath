import SierpinskiFormal.WeightedBlockCoding
import SierpinskiFormal.ModuleReturnGroup
import SierpinskiFormal.FiniteLengthCompression
import SierpinskiFormal.ModuleDensityAssembly
import SierpinskiFormal.CesaroResidueAssembly

/-!
# Block coding for scalar observations on finite Artinian modules

This file transports chronological endomorphism words through fixed-length
block coding.  The final boundary-density theorem is assembled below from
the finite-length compression and module boundary-density interfaces.
-/

set_option autoImplicit false
noncomputable section

open Filter
open scoped BigOperators Topology

namespace IndependentZeroBlocks

variable {R V A : Type*} [CommRing R] [AddCommGroup V] [Module R V]

/-- The endomorphism attached to a fixed-length block. -/
def blockEndomorphism (T : A → Module.End R V) (ell : ℕ)
    (c : Fin ell → A) : Module.End R V :=
  endoWord T (List.ofFn c)

/-- Products of block endomorphisms equal the product over the flattened
letter word, with the same chronological convention. -/
@[simp] theorem endoWord_blockEndomorphism (T : A → Module.End R V)
    (ell : ℕ) (w : List (Fin ell → A)) :
    endoWord (blockEndomorphism T ell) w =
      endoWord T (flattenBlocks ell w) := by
  induction w with
  | nil => simp [flattenBlocks]
  | cons c w ih =>
      rw [endoWord_cons, flattenBlocks_cons, endoWord_append, ih]
      rfl

/-- A nonempty word, viewed as the distinguished letter of its own block
alphabet. -/
def endoMarkerBlock (h : List A) : Fin h.length → A := h.get

@[simp] theorem ofFn_endoMarkerBlock (h : List A) :
    List.ofFn (endoMarkerBlock h) = h := by
  exact List.ofFn_get h

@[simp] theorem blockEndomorphism_endoMarkerBlock
    (T : A → Module.End R V) (h : List A) :
    blockEndomorphism T h.length (endoMarkerBlock h) = endoWord T h := by
  simp [blockEndomorphism]

/-- A nonempty minimum-length word becomes a minimum-length marker letter
after blocking by its own length. -/
theorem minLength_endoMarkerBlock
    (T : A → Module.End R V) (h : List A) (hh : h ≠ [])
    (hmin : ∀ u : List A, u ≠ [] →
      Module.length R (LinearMap.range (endoWord T h)) ≤
        Module.length R (LinearMap.range (endoWord T u))) :
    ∀ w : List (Fin h.length → A), w ≠ [] →
      Module.length R
          (LinearMap.range
            (endoWord (blockEndomorphism T h.length) [endoMarkerBlock h])) ≤
        Module.length R
          (LinearMap.range (endoWord (blockEndomorphism T h.length) w)) := by
  intro w hw
  rw [endoWord_blockEndomorphism, endoWord_blockEndomorphism]
  have hmarkerflat : flattenBlocks h.length [endoMarkerBlock h] = h := by
    simp [flattenBlocks, endoMarkerBlock]
  rw [hmarkerflat]
  apply hmin
  intro hflat
  have hlen : (flattenBlocks h.length w).length = w.length * h.length :=
    length_flattenBlocks h.length w
  rw [hflat] at hlen
  simp only [List.length_nil] at hlen
  have hwlen : 0 < w.length := List.length_pos_iff.mpr hw
  have hhlen : 0 < h.length := List.length_pos_iff.mpr hh
  have hprod : 0 < w.length * h.length := Nat.mul_pos hwlen hhlen
  omega

/-- Every finite-length module action has a positive block length whose
distinguished block is minimum-length among all nonempty block products. -/
theorem exists_minLengthBlockMarker [Nonempty A] [IsArtinian R V]
    [IsNoetherian R V] (T : A → Module.End R V) :
    ∃ h : List A, h ≠ [] ∧ 0 < h.length ∧
      ∀ w : List (Fin h.length → A), w ≠ [] →
        Module.length R
            (LinearMap.range
              (endoWord (blockEndomorphism T h.length) [endoMarkerBlock h])) ≤
          Module.length R
            (LinearMap.range (endoWord (blockEndomorphism T h.length) w)) := by
  obtain ⟨h, hh, hmin⟩ := exists_minLengthWord T
  exact ⟨h, hh, List.length_pos_iff.mpr hh,
    minLength_endoMarkerBlock T h hh hmin⟩

/-- The original reset factorization is also the distinguished-letter
factorization for the block action. -/
theorem block_reset_factorization (T : A → Module.End R V) (h : List A) :
    endoWord (blockEndomorphism T h.length) [endoMarkerBlock h] =
      (returnInclusion T h).comp (resetCorestrict T h) := by
  rw [endoWord_blockEndomorphism]
  have hmarkerflat : flattenBlocks h.length [endoMarkerBlock h] = h := by
    simp [flattenBlocks, endoMarkerBlock]
  rw [hmarkerflat]
  exact reset_factorization T h

/-- Compressing a block word through the original reset image is exactly
the return endomorphism indexed by its flattened letter word. -/
theorem compressedReturn_blockEndomorphism
    (T : A → Module.End R V) (h : List A)
    (y : List (Fin h.length → A)) :
    compressedReturn (blockEndomorphism T h.length)
        (returnInclusion T h) (resetCorestrict T h) y =
      returnEnd T h (flattenBlocks h.length y) := by
  unfold compressedReturn returnEnd
  rw [endoWord_blockEndomorphism]

/-- Minimum reset length makes every block return compression bijective. -/
theorem blockReturn_bijective_of_minLength
    [IsArtinian R V] [IsNoetherian R V]
    (T : A → Module.End R V) (h : List A) (hh : h ≠ [])
    (hmin : ∀ w : List A, w ≠ [] →
      Module.length R (LinearMap.range (endoWord T h)) ≤
        Module.length R (LinearMap.range (endoWord T w)))
    (y : List (Fin h.length → A)) :
    Function.Bijective
      (compressedReturn (blockEndomorphism T h.length)
        (returnInclusion T h) (resetCorestrict T h) y) := by
  rw [compressedReturn_blockEndomorphism]
  exact returnEnd_bijective_of_minLength T h hh hmin (flattenBlocks h.length y)

/-- The state obtained by moving a residual suffix into the seed. -/
def moduleSuffixSeed (T : A → Module.End R V) (xi : List A) (seed : V) : V :=
  endoWord T xi seed

/-- A block observation with the suffix-adjusted seed is the original
observation on the flattened blocks followed by that suffix. -/
theorem blockScalar_suffix (T : A → Module.End R V) (ell : ℕ)
    (left : Module.Dual R V) (seed : V) (w : List (Fin ell → A))
    (xi : List A) :
    left (endoWord (blockEndomorphism T ell) w
      (moduleSuffixSeed T xi seed)) =
      left (endoWord T (flattenBlocks ell w ++ xi) seed) := by
  simp only [moduleSuffixSeed, endoWord_blockEndomorphism,
    endoWord_append, Module.End.mul_apply]

/-- Boolean form of `blockScalar_suffix`. -/
@[simp] theorem nonzeroBool_block_suffix
    (T : A → Module.End R V) (ell : ℕ) (left : Module.Dual R V)
    (seed : V) (w : List (Fin ell → A)) (xi : List A) :
    nonzeroBool (left (endoWord (blockEndomorphism T ell) w
      (moduleSuffixSeed T xi seed))) =
      nonzeroBool (left (endoWord T (flattenBlocks ell w ++ xi) seed)) := by
  rw [blockScalar_suffix]

section ResidueLimit

variable [TopologicalSpace A] [DiscreteTopology A] [Fintype A] [Nonempty A]

/-- Block-word scalar limits determine the limit along one physical residue
class after taking the finite mixture over residual suffixes. -/
theorem tendsto_moduleScalar_residue_of_blockLimits
    (p : A → ℝ) (T : A → Module.End R V) (left : Module.Dual R V)
    (seed : V) (ell s : ℕ) (L : (Fin s → A) → ℝ)
    (hL : ∀ xi : Fin s → A,
      Tendsto
        (realCesaroMean (fun N ↦
          weightedWordExtensionAverage (blockWeight p ell)
            (booleanWordIndicator (fun w : List (Fin ell → A) ↦
              nonzeroBool (left (endoWord (blockEndomorphism T ell) w
                (moduleSuffixSeed T (List.ofFn xi) seed))))) N []))
        atTop (nhds (L xi))) :
    Tendsto
      (realCesaroMean (fun N ↦ weightedWordExtensionAverage p
        (booleanWordIndicator (fun w ↦
          nonzeroBool (left (endoWord T w seed)))) (N * ell + s) []))
      atTop (nhds (∑ xi : Fin s → A, wordWeight p (List.ofFn xi) * L xi)) := by
  let q : List A → Bool := fun w ↦ nonzeroBool (left (endoWord T w seed))
  let c : (Fin s → A) → ℕ → ℝ := fun xi N ↦
    weightedWordExtensionAverage (blockWeight p ell)
      (booleanWordIndicator (fun w : List (Fin ell → A) ↦
        q (flattenBlocks ell w ++ List.ofFn xi))) N []
  have hc : ∀ xi : Fin s → A, Tendsto (realCesaroMean (c xi)) atTop (nhds (L xi)) := by
    intro xi
    have hpred : (fun w : List (Fin ell → A) ↦
        q (flattenBlocks ell w ++ List.ofFn xi)) =
        fun w ↦ nonzeroBool (left (endoWord (blockEndomorphism T ell) w
          (moduleSuffixSeed T (List.ofFn xi) seed))) := by
      funext w
      exact (nonzeroBool_block_suffix T ell left seed w (List.ofFn xi)).symm
    simpa only [c, hpred] using hL xi
  have heq : (fun N ↦ weightedWordExtensionAverage p
      (booleanWordIndicator q) (N * ell + s) []) =
      fun N ↦ ∑ xi : Fin s → A, wordWeight p (List.ofFn xi) * c xi N := by
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

/-- If the unrestricted scalar Cesaro limit exists, all suffix block limits
identify it as the arithmetic average of their residue mixtures. -/
theorem moduleScalarLimit_eq_average_blockLimits
    (p : A → ℝ) (T : A → Module.End R V) (left : Module.Dual R V)
    (seed : V) (ell : ℕ) (hell : 0 < ell) (L : ℝ)
    (B : (s : Fin ell) → (Fin (s : ℕ) → A) → ℝ)
    (hfull : Tendsto
      (realCesaroMean (fun n ↦ weightedWordExtensionAverage p
        (booleanWordIndicator (fun w ↦
          nonzeroBool (left (endoWord T w seed)))) n []))
      atTop (nhds L))
    (hblock : ∀ (s : Fin ell) (xi : Fin (s : ℕ) → A),
      Tendsto
        (realCesaroMean (fun N ↦
          weightedWordExtensionAverage (blockWeight p ell)
            (booleanWordIndicator (fun w : List (Fin ell → A) ↦
              nonzeroBool (left (endoWord (blockEndomorphism T ell) w
                (moduleSuffixSeed T (List.ofFn xi) seed))))) N []))
        atTop (nhds (B s xi))) :
    L = (∑ s : Fin ell, ∑ xi : Fin (s : ℕ) → A,
      wordWeight p (List.ofFn xi) * B s xi) / (ell : ℝ) := by
  apply cesaroLimit_eq_average_residueLimits
    (fun n ↦ weightedWordExtensionAverage p
      (booleanWordIndicator (fun w ↦
        nonzeroBool (left (endoWord T w seed)))) n [])
    ell hell L (fun s ↦ ∑ xi : Fin (s : ℕ) → A,
      wordWeight p (List.ofFn xi) * B s xi) hfull
  intro s
  exact tendsto_moduleScalar_residue_of_blockLimits
    p T left seed ell s (B s) (fun xi ↦ hblock s xi)

end ResidueLimit

section ArtinianBoundaryFormula

variable [IsArtinianRing R] [Module.Finite R V]
variable [TopologicalSpace A] [DiscreteTopology A] [Fintype A] [Nonempty A]
  [DecidableEq A]

/-- Law-independent arbitrary-reset theorem for scalar observations on a
finite module over a commutative Artinian ring.  A single minimum-length
word, its return-space factorization, and all rational contextual means are
chosen before the strictly positive normalized Bernoulli law.

The second conclusion is the density of the original `A`-word scalar
predicate.  Its displayed value is the finite residue/suffix average of the
countable boundary mixtures for the blocked marker. -/
theorem exists_minLengthWord_moduleBoundaryMeans_forall_positive_laws
    (T : A → Module.End R V) (left : Module.Dual R V) (seed : V) :
    ∃ h : List A, h ≠ [] ∧
      (∀ w : List A, w ≠ [] →
        Module.length R (LinearMap.range (endoWord T h)) ≤
          Module.length R (LinearMap.range (endoWord T w))) ∧
      ∃ (U : ReturnSpace T h →ₗ[R] V) (V0 : V →ₗ[R] ReturnSpace T h),
        endoWord T h = U.comp V0 ∧
        (∀ y : List (Fin h.length → A),
          Function.Bijective
            (compressedReturn (blockEndomorphism T h.length) U V0 y)) ∧
        ∃ m : (s : Fin h.length) → (Fin (s : ℕ) → A) →
            GapWords (endoMarkerBlock h) × GapWords (endoMarkerBlock h) → ℚ,
          ∀ (p : A → ℝ), (∀ a, 0 < p a) → (∑ a, p a = 1) →
            ((∀ (s : Fin h.length) (xi : Fin (s : ℕ) → A)
                (i : GapWords (endoMarkerBlock h) ×
                  GapWords (endoMarkerBlock h)),
                Tendsto
                  (realCesaroMean (moduleBoundaryCentralSequence
                    (blockWeight p h.length) (blockEndomorphism T h.length)
                    U V0 left (moduleSuffixSeed T (List.ofFn xi) seed) i))
                  atTop (nhds (m s xi i : ℝ))) ∧
              Tendsto
                (realCesaroMean (fun n ↦ weightedWordExtensionAverage p
                  (booleanWordIndicator (moduleCoefficientNonzero T left seed))
                  n []))
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
  have hfac : endoWord T h = U.comp V0 := by
    exact reset_factorization T h
  have hell : 0 < h.length := List.length_pos_iff.mpr hh
  have hfacBlock :
      endoWord (blockEndomorphism T h.length) [endoMarkerBlock h] =
        U.comp V0 := by
    exact block_reset_factorization T h
  have hbijBlock : ∀ y : List (Fin h.length → A),
      Function.Bijective
        (compressedReturn (blockEndomorphism T h.length) U V0 y) := by
    intro y
    exact blockReturn_bijective_of_minLength T h hh hmin y
  have hall : ∀ (s : Fin h.length) (xi : Fin (s : ℕ) → A),
      ∃ m : GapWords (endoMarkerBlock h) × GapWords (endoMarkerBlock h) → ℚ,
        ∀ (pblock : (Fin h.length → A) → ℝ),
          (∀ c, 0 < pblock c) → (∑ c, pblock c = 1) →
            ((∀ i, Tendsto
              (realCesaroMean (moduleBoundaryCentralSequence
                pblock (blockEndomorphism T h.length) U V0 left
                (moduleSuffixSeed T (List.ofFn xi) seed) i))
              atTop (nhds (m i : ℝ))) ∧
            Tendsto
              (realCesaroMean (fun n ↦ weightedWordExtensionAverage pblock
                (booleanWordIndicator (moduleCoefficientNonzero
                  (blockEndomorphism T h.length) left
                  (moduleSuffixSeed T (List.ofFn xi) seed))) n []))
              atTop (nhds (∑' i : GapWords (endoMarkerBlock h) ×
                  GapWords (endoMarkerBlock h),
                moduleBoundaryWeight pblock (endoMarkerBlock h) i *
                  (m i : ℝ)))) := by
    intro s xi
    exact exists_rational_moduleBoundaryMeans_forall_positive_laws
      (blockEndomorphism T h.length) (endoMarkerBlock h) U V0 hfacBlock
      hbijBlock left (moduleSuffixSeed T (List.ofFn xi) seed)
  choose m hm using hall
  refine ⟨h, hh, hmin, U, V0, hfac, hbijBlock, m, ?_⟩
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
  have hblockSum : ∑ c : Fin h.length → A, blockWeight p h.length c = 1 :=
    sum_blockWeight_eq_one p hp1 h.length
  have hcentral : ∀ (s : Fin h.length) (xi : Fin (s : ℕ) → A)
      (i : GapWords (endoMarkerBlock h) × GapWords (endoMarkerBlock h)),
      Tendsto
        (realCesaroMean (moduleBoundaryCentralSequence
          (blockWeight p h.length) (blockEndomorphism T h.length)
          U V0 left (moduleSuffixSeed T (List.ofFn xi) seed) i))
        atTop (nhds (m s xi i : ℝ)) := by
    intro s xi i
    exact (hm s xi (blockWeight p h.length) hblockPos hblockSum).1 i
  have hblock : ∀ (s : Fin h.length) (xi : Fin (s : ℕ) → A),
      Tendsto
        (realCesaroMean (fun N ↦
          weightedWordExtensionAverage (blockWeight p h.length)
            (booleanWordIndicator (moduleCoefficientNonzero
              (blockEndomorphism T h.length) left
              (moduleSuffixSeed T (List.ofFn xi) seed))) N []))
        atTop (nhds (∑' i : GapWords (endoMarkerBlock h) ×
            GapWords (endoMarkerBlock h),
          moduleBoundaryWeight (blockWeight p h.length)
            (endoMarkerBlock h) i * (m s xi i : ℝ))) := by
    intro s xi
    exact (hm s xi (blockWeight p h.length) hblockPos hblockSum).2
  obtain ⟨L, hL⟩ := exists_tendsto_noetherian_endoWord_weighted_cesaro
    (endoWord T) (endoWord_append T) left seed p (fun a ↦ (hp a).le) hp1
  have hfull : Tendsto
      (realCesaroMean (fun n ↦ weightedWordExtensionAverage p
        (booleanWordIndicator (moduleCoefficientNonzero T left seed)) n []))
      atTop (nhds L) := by
    rw [show realCesaroMean (fun n ↦ weightedWordExtensionAverage p
        (booleanWordIndicator (moduleCoefficientNonzero T left seed)) n []) =
        weightedIidWordCesaro p
          (booleanWordIndicator (moduleCoefficientNonzero T left seed)) by
      funext N
      simp only [realCesaroMean, weightedIidWordCesaro, div_eq_mul_inv]
      ring]
    have hpred : (fun w ↦ nonzeroBool (left (endoWord T w seed))) =
        moduleCoefficientNonzero T left seed := by
      funext w
      rfl
    rw [← hpred]
    exact hL
  let B : (s : Fin h.length) → (Fin (s : ℕ) → A) → ℝ := fun s xi ↦
    ∑' i : GapWords (endoMarkerBlock h) × GapWords (endoMarkerBlock h),
      moduleBoundaryWeight (blockWeight p h.length) (endoMarkerBlock h) i *
        (m s xi i : ℝ)
  have hEq : L = (∑ s : Fin h.length, ∑ xi : Fin (s : ℕ) → A,
      wordWeight p (List.ofFn xi) * B s xi) / (h.length : ℝ) :=
    moduleScalarLimit_eq_average_blockLimits p T left seed h.length hell L B
      hfull hblock
  refine ⟨hcentral, ?_⟩
  simpa only [B, hEq] using hfull

end ArtinianBoundaryFormula

end IndependentZeroBlocks
