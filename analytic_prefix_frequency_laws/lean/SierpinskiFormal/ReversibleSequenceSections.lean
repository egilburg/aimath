import SierpinskiFormal.ReversibleFreeGroup
import SierpinskiFormal.MatrixRadixRegularity
import Mathlib.Algebra.BigOperators.Option

set_option autoImplicit false

/-!
# Reversible radix sections of scalar sequences

This file records a finitely generated module of scalar sequences on which
every digit-section operator is an automorphism.  Since these operators
compose in the order opposite to little-endian digit lists, scalar values are
represented by reversed words.
-/

noncomputable section

namespace IndependentZeroBlocks

open scoped BigOperators

/-- Data witnessing that a scalar sequence lies in a finitely generated
module of sequences whose digit sections act by linear automorphisms. -/
structure ReversibleRadixRegularData (K : Type*) [CommRing K]
    (b : ℕ) (f : ℕ → K) where
  carrier : Submodule K (ℕ → K)
  finite : Module.Finite K carrier
  seed : carrier
  seed_coe : (seed : ℕ → K) = f
  digit : Fin b → carrier ≃ₗ[K] carrier
  digit_apply : ∀ r s n, ((digit r s : carrier) : ℕ → K) n =
    (s : ℕ → K) (b * n + r.val)

/-- Intrinsic reversible radix-regularity. -/
def IsReversibleRadixRegular {K : Type*} [CommRing K]
    (b : ℕ) (f : ℕ → K) : Prop :=
  Nonempty (ReversibleRadixRegularData K b f)

/-- The endomorphism family underlying reversible digit sections. -/
def ReversibleRadixRegularData.digitEnd
    {K : Type*} [CommRing K] {b : ℕ} {f : ℕ → K}
    (D : ReversibleRadixRegularData K b f) :
    Fin b → Module.End K D.carrier :=
  fun r ↦ (D.digit r).toLinearMap

/-- Iterated digit sections evaluate by the reversed little-endian word. -/
theorem ReversibleRadixRegularData.linearWord_digitEnd_apply
    {K : Type*} [CommRing K] {b : ℕ} {f : ℕ → K}
    (D : ReversibleRadixRegularData K b f)
    (w : List (Fin b)) (s : D.carrier) (n : ℕ) :
    ((linearWord D.digitEnd w s : D.carrier) : ℕ → K) n =
      (s : ℕ → K)
        (b ^ w.length * n + Nat.ofDigits b (w.reverse.map Fin.val)) := by
  induction w generalizing n with
  | nil => simp
  | cons r w ih =>
      rw [linearWord_cons, Module.End.mul_apply]
      change (((D.digit r)
        (linearWord D.digitEnd w s) : D.carrier) : ℕ → K) n = _
      rw [D.digit_apply, ih]
      simp only [List.length_cons, List.reverse_cons, List.map_append,
        List.map_singleton, Nat.ofDigits_append, Nat.ofDigits_singleton,
        List.length_map, List.length_reverse, pow_succ]
      ring_nf

/-- At zero, a digit-section word reads the original sequence at the natural
number encoded by the reversed word. -/
theorem ReversibleRadixRegularData.linearWord_seed_eval_zero
    {K : Type*} [CommRing K] {b : ℕ} {f : ℕ → K}
    (D : ReversibleRadixRegularData K b f) (w : List (Fin b)) :
    ((linearWord D.digitEnd w D.seed : D.carrier) : ℕ → K) 0 =
      f (Nat.ofDigits b (w.reverse.map Fin.val)) := by
  rw [D.linearWord_digitEnd_apply, D.seed_coe]
  simp

/-- The positive free-group element encoded by a list of generators. -/
def positiveFreeGroupWord {A : Type*} (w : List A) : FreeGroup A :=
  (w.map FreeGroup.of).prod

/-- The intrinsic free-group action attached to reversible digit sections. -/
def ReversibleRadixRegularData.freeGroupAction
    {K : Type*} [CommRing K] {b : ℕ} {f : ℕ → K}
    (D : ReversibleRadixRegularData K b f) :
    FreeGroup (Fin b) →* (D.carrier ≃ₗ[K] D.carrier) :=
  freeGroupLinearAction D.digit

/-- Positive free-group words act by the corresponding iterated digit
section operators. -/
theorem ReversibleRadixRegularData.freeGroupAction_positiveWord
    {K : Type*} [CommRing K] {b : ℕ} {f : ℕ → K}
    (D : ReversibleRadixRegularData K b f) (w : List (Fin b)) :
    (D.freeGroupAction (positiveFreeGroupWord w)).toLinearMap =
      linearWord D.digitEnd w := by
  induction w with
  | nil =>
      simp [positiveFreeGroupWord, ReversibleRadixRegularData.freeGroupAction]
      rfl
  | cons r w ih =>
      rw [linearWord_cons]
      simp only [positiveFreeGroupWord, List.map_cons, List.prod_cons, map_mul]
      rw [LinearEquiv.coe_toLinearMap_mul]
      have hr : D.freeGroupAction (FreeGroup.of r) = D.digit r := by
        simp [ReversibleRadixRegularData.freeGroupAction]
      rw [hr]
      change (D.digit r).toLinearMap *
          (D.freeGroupAction (positiveFreeGroupWord w)).toLinearMap = _
      rw [ih]
      rfl

/-- Every padded radix section is the action of the reversed positive word
in the intrinsic free-group representation. -/
theorem ReversibleRadixRegularData.freeGroupAction_reverseWord_apply
    {K : Type*} [CommRing K] {b : ℕ} {f : ℕ → K}
    (D : ReversibleRadixRegularData K b f)
    (w : List (Fin b)) (n : ℕ) :
    (((D.freeGroupAction (positiveFreeGroupWord w.reverse)) D.seed :
        D.carrier) : ℕ → K) n = radixWordSection b f w n := by
  rw [show (D.freeGroupAction (positiveFreeGroupWord w.reverse)) D.seed =
      linearWord D.digitEnd w.reverse D.seed by
    rw [← D.freeGroupAction_positiveWord w.reverse]
    rfl]
  rw [D.linearWord_digitEnd_apply, D.seed_coe]
  simp [radixWordSection]

/-- The intrinsic free-group support kernel of reversible radix-section data
has the Boolean double-limit property. -/
theorem ReversibleRadixRegularData.freeGroupRightRow_hasBooleanDoubleLimitProperty
    {K : Type*} [CommRing K] {b : ℕ} {f : ℕ → K}
    (D : ReversibleRadixRegularData K b f) :
    HasBooleanDoubleLimitProperty
      (booleanGroupRightRow (fun γ : FreeGroup (Fin b) ↦
        nonzeroBool
          ((((D.freeGroupAction γ) D.seed : D.carrier) : ℕ → K) 0))) := by
  letI : Module.Finite K D.carrier := D.finite
  let evalZero : Module.Dual K D.carrier :=
    (LinearMap.proj 0).comp D.carrier.subtype
  simpa [ReversibleRadixRegularData.freeGroupAction, evalZero] using
    finiteModule_freeGroup_booleanGroupRightRow_hasBooleanDoubleLimitProperty
      D.digit evalZero D.seed

/-- Finite Boolean combinations of reversible section observations may use
different finite sequence modules in each coordinate. -/
theorem reversibleRadixData_booleanCombine_freeGroupRightRow_hasBooleanDoubleLimitProperty
    {K : Type*} [CommRing K] {b m : ℕ}
    {f : Fin m → ℕ → K}
    (D : ∀ k, ReversibleRadixRegularData K b (f k))
    (op : (Fin m → Bool) → Bool) :
    HasBooleanDoubleLimitProperty
      (booleanGroupRightRow (fun γ : FreeGroup (Fin b) ↦
        op (fun k ↦ nonzeroBool
          (((((D k).freeGroupAction γ) (D k).seed :
            (D k).carrier) : ℕ → K) 0)))) := by
  letI : ∀ k, Module.Finite K (D k).carrier := fun k ↦ (D k).finite
  let evalZero : ∀ k, Module.Dual K (D k).carrier := fun k ↦
    (LinearMap.proj 0).comp (D k).carrier.subtype
  simpa [ReversibleRadixRegularData.freeGroupAction, evalZero] using
    finiteModule_freeGroup_booleanCombine_rightRow_hasBooleanDoubleLimitProperty
      (fun k ↦ (D k).carrier) op (fun k ↦ (D k).digit) evalZero
      (fun k ↦ (D k).seed)

/-- Canonical base-`b` digits bundled with their proof of lying in `Fin b`. -/
def canonicalFinDigits (b : ℕ) (hb : 2 ≤ b) (n : ℕ) : List (Fin b) :=
  letI : NeZero b := ⟨by omega⟩
  (Nat.digits b n).map (Fin.ofNat b)

@[simp] theorem canonicalFinDigits_map_val
    (b : ℕ) (hb : 2 ≤ b) (n : ℕ) :
    (canonicalFinDigits b hb n).map Fin.val = Nat.digits b n := by
  letI : NeZero b := ⟨by omega⟩
  simp only [canonicalFinDigits, List.map_map]
  have hmap (L : List ℕ) (hL : ∀ x ∈ L, x < b) :
      L.map (Fin.val ∘ Fin.ofNat b) = L := by
    induction L with
    | nil => simp
    | cons x L ih =>
        simp only [List.map_cons, List.cons.injEq]
        constructor
        · simp [Fin.val_ofNat, Nat.mod_eq_of_lt (hL x (by simp))]
        · apply ih
          intro y hy
          exact hL y (by simp [hy])
  exact hmap _ (fun x hx ↦ Nat.digits_lt_base (by omega) hx)

@[simp] theorem canonicalFinDigits_zero (b : ℕ) (hb : 2 ≤ b) :
    canonicalFinDigits b hb 0 = [] := by
  simp [canonicalFinDigits]

theorem canonicalFinDigits_radix
    (b : ℕ) (hb : 2 ≤ b) (n : ℕ) (r : Fin b)
    (hnr : n ≠ 0 ∨ r.val ≠ 0) :
    canonicalFinDigits b hb (b * n + r.val) =
      r :: canonicalFinDigits b hb n := by
  have hdigits : Nat.digits b (b * n + r.val) =
      r.val :: Nat.digits b n := by
    rw [add_comm]
    exact Nat.digits_add b (by omega) r.val n r.isLt hnr.symm
  apply (List.map_injective_iff.mpr Fin.val_injective)
  rw [canonicalFinDigits_map_val, List.map_cons,
    canonicalFinDigits_map_val, hdigits]

@[simp] theorem ofDigits_canonicalFinDigits
    (b : ℕ) (hb : 2 ≤ b) (n : ℕ) :
    Nat.ofDigits b ((canonicalFinDigits b hb n).map Fin.val) = n := by
  rw [canonicalFinDigits_map_val, Nat.ofDigits_digits]

/-- Coordinate row obtained by reading a matrix word against an initial row.
It is the transpose-state used to process ordinary little-endian digits. -/
def reversedDigitRowState
    {K ι : Type*} [CommRing K] [Fintype ι]
    (b : ℕ) (hb : 2 ≤ b) (M : Fin b → Matrix ι ι K)
    (a : ι → K) (n : ℕ) : ι → K :=
  fun i ↦ coordinateRowDual a
    (linearWord (fun r ↦ Matrix.mulVecLin (M r))
      (canonicalFinDigits b hb n).reverse (coordinateUnit i))

@[simp] theorem reversedDigitRowState_zero
    {K ι : Type*} [CommRing K] [Fintype ι]
    (b : ℕ) (hb : 2 ≤ b) (M : Fin b → Matrix ι ι K) (a : ι → K) :
    reversedDigitRowState b hb M a 0 = a := by
  classical
  funext i
  simp [reversedDigitRowState, coordinateRowDual_apply, coordinateUnit,
    Pi.single_apply]

/-- Away from the unique leading-zero exception `(n,r)=(0,0)`, reversed
digit rows evolve by the transpose of the next digit matrix. -/
theorem reversedDigitRowState_radix
    {K ι : Type*} [CommRing K] [Fintype ι]
    (b : ℕ) (hb : 2 ≤ b) (M : Fin b → Matrix ι ι K) (a : ι → K)
    (n : ℕ) (r : Fin b) (hnr : n ≠ 0 ∨ r.val ≠ 0) :
    reversedDigitRowState b hb M a (b * n + r.val) =
      Matrix.mulVecLin (Matrix.transpose (M r))
        (reversedDigitRowState b hb M a n) := by
  classical
  funext i
  rw [reversedDigitRowState, canonicalFinDigits_radix b hb n r hnr,
    List.reverse_cons,
    linearWord_append, Module.End.mul_apply]
  simp only [List.reverse_singleton, linearWord_cons, linearWord_nil,
    Module.End.mul_apply, Module.End.one_apply, Matrix.mulVecLin_apply,
    Matrix.mulVec_transpose]
  let P := linearWord (fun r ↦ Matrix.mulVecLin (M r))
    (canonicalFinDigits b hb n).reverse
  let q : Module.Dual K (ι → K) := (coordinateRowDual a).comp P
  have hdual := dual_apply_eq_sum_single q
    (Matrix.mulVecLin (M r) (coordinateUnit i))
  change q (Matrix.mulVecLin (M r) (coordinateUnit i)) =
    Matrix.vecMul (fun j ↦ q (coordinateUnit j)) (M r) i
  rw [hdual]
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, Matrix.vecMul, dotProduct,
    coordinateUnit, Pi.single_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_eq_single i]
  · simp
  · intro k hk hki
    simp [hki]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- A scalar sequence represented by reversed canonical digit words in
finite matrices is radix-regular.  One extra coordinate repairs the sole
leading-zero transition at the index zero. -/
theorem matrix_reversedDigits_isRadixRegular
    {K ι : Type*} [CommRing K] [Fintype ι]
    (b : ℕ) (hb : 2 ≤ b) (M : Fin b → Matrix ι ι K)
    (u a : ι → K) (f : ℕ → K)
    (hrepr : ∀ n,
      coordinateRowDual a
          (linearWord (fun r ↦ Matrix.mulVecLin (M r))
            (canonicalFinDigits b hb n).reverse u) = f n) :
    IsRadixRegular b f := by
  classical
  let q : ℕ → ι → K := reversedDigitRowState b hb M a
  let W : ℕ → Option ι → K := fun n oi ↦ match oi with
    | some i => q n i
    | none => if n = 0 then 1 else 0
  let correction : Fin b → ι → K := fun r i ↦
    if r.val = 0 then
      a i - Matrix.mulVecLin (Matrix.transpose (M r)) a i else 0
  let N : Fin b → Matrix (Option ι) (Option ι) K := fun r oi oj ↦
    match oi, oj with
    | some i, some j => Matrix.transpose (M r) i j
    | some i, none => correction r i
    | none, some _ => 0
    | none, none => if r.val = 0 then 1 else 0
  let L : Module.Dual K (Option ι → K) :=
    coordinateRowDual (fun oi ↦ match oi with | some i => u i | none => 0)
  have hq0 : q 0 = a := reversedDigitRowState_zero b hb M a
  have hrec : ∀ n (r : Fin b),
      W (b * n + r.val) = Matrix.mulVecLin (N r) (W n) := by
    intro n r
    funext oi
    cases oi with
    | some i =>
        change W (b * n + r.val) (some i) =
          ∑ oj, N r (some i) oj * W n oj
        by_cases hn : n = 0
        · subst n
          by_cases hr : r.val = 0
          · have hindex : b * 0 + r.val = 0 := by omega
            rw [hindex]
            simp only [W, N, correction, Matrix.mulVecLin_apply,
              Matrix.mulVec, dotProduct, Fintype.sum_option, hr, if_pos]
            rw [hq0]
            ring
          · have hqrec := reversedDigitRowState_radix b hb M a 0 r (Or.inr hr)
            simp only [W, N, correction, Matrix.mulVecLin_apply,
              Matrix.mulVec, dotProduct, Fintype.sum_option]
            rw [show q (b * 0 + r.val) i =
                Matrix.mulVecLin (Matrix.transpose (M r)) (q 0) i by
              exact congrFun hqrec i]
            simp [hr, Matrix.mulVecLin_apply, Matrix.mulVec, Matrix.vecMul,
              dotProduct, mul_comm]
        · have hqrec := reversedDigitRowState_radix b hb M a n r (Or.inl hn)
          simp only [W, N, correction, Matrix.mulVecLin_apply, Matrix.mulVec,
            dotProduct, Fintype.sum_option]
          rw [show q (b * n + r.val) i =
              Matrix.mulVecLin (Matrix.transpose (M r)) (q n) i by
            exact congrFun hqrec i]
          simp [hn, Matrix.mulVecLin_apply, Matrix.mulVec, Matrix.vecMul,
            dotProduct, mul_comm]
    | none =>
        change W (b * n + r.val) none =
          ∑ oj, N r none oj * W n oj
        by_cases hn : n = 0
        · subst n
          by_cases hr : r.val = 0
          · have hindex : b * 0 + r.val = 0 := by omega
            rw [hindex]
            simp [W, N, hr, Matrix.mulVecLin_apply, Matrix.mulVec,
              dotProduct, Fintype.sum_option]
          · have hindex : b * 0 + r.val ≠ 0 := by omega
            simp [W, N, hr, hindex, Matrix.mulVecLin_apply, Matrix.mulVec,
              dotProduct, Fintype.sum_option]
        · have hindex : b * n + r.val ≠ 0 := by
            exact Nat.ne_of_gt (add_pos_of_pos_of_nonneg
              (Nat.mul_pos (by omega) (Nat.pos_of_ne_zero hn)) (Nat.zero_le _))
          have hb0 : b ≠ 0 := by omega
          simp [W, N, hn, hindex, Matrix.mulVecLin_apply, Matrix.mulVec,
            dotProduct, Fintype.sum_option, hb0]
  have hout : ∀ n, L (W n) = f n := by
    intro n
    let P := linearWord (fun r ↦ Matrix.mulVecLin (M r))
      (canonicalFinDigits b hb n).reverse
    have hdual := dual_apply_eq_sum_single ((coordinateRowDual a).comp P) u
    calc
      L (W n) = ∑ i, u i * q n i := by
        simp [L, W, coordinateRowDual_apply, Fintype.sum_option]
      _ = ∑ i, q n i * u i := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = ((coordinateRowDual a).comp P) u := by
        rw [hdual]
        rfl
      _ = f n := hrepr n
  have hregular := matrix_observation_isRadixRegular b hb N W hrec L
  simpa only [hout] using hregular

/-- Intrinsic reversible radix-regularity implies ordinary radix-regularity
over every commutative coefficient ring. -/
theorem IsReversibleRadixRegular.isRadixRegular
    {K : Type*} [CommRing K] (b : ℕ) (hb : 2 ≤ b) (f : ℕ → K)
    (h : IsReversibleRadixRegular b f) : IsRadixRegular b f := by
  let D := Classical.choice h
  letI : Module.Finite K D.carrier := D.finite
  let evalZero : Module.Dual K D.carrier :=
    (LinearMap.proj 0).comp D.carrier.subtype
  obtain ⟨d, M, u, a, hM⟩ :=
    finiteModule_exists_matrix_word_representation D.digitEnd evalZero D.seed
  apply matrix_reversedDigits_isRadixRegular b hb M u a f
  intro n
  rw [hM]
  change ((linearWord D.digitEnd (canonicalFinDigits b hb n).reverse D.seed :
    D.carrier) : ℕ → K) 0 = f n
  rw [D.linearWord_seed_eval_zero]
  simp only [List.reverse_reverse]
  rw [canonicalFinDigits_map_val, Nat.ofDigits_digits]

end IndependentZeroBlocks
