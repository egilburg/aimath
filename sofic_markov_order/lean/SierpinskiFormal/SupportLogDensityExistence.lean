import SierpinskiFormal.MatrixWordLogDensityBridge
import SierpinskiFormal.BooleanWordCesaro
import SierpinskiFormal.BooleanDoubleLimitClosure
import SierpinskiFormal.LogDensityClassification

set_option autoImplicit false

/-!
# Logarithmic-density existence for regular supports

Boolean double-limit compactness supplies the IID word Cesaro limits required
by the arithmetic radix-shell transfer.  The first part of this file makes
that connection for a finite matrix recurrence over an arbitrary commutative
ring.  The final statements package the result intrinsically for
radix-regular sequences.
-/

noncomputable section

namespace IndependentZeroBlocks

open Filter
open scoped Topology

/-- The Boolean double-limit property is invariant under transposing its two
arguments. -/
theorem HasBooleanDoubleLimitProperty.swap
    {X Y : Type*} {B : X → Y → Bool}
    (hB : HasBooleanDoubleLimitProperty B) :
    HasBooleanDoubleLimitProperty (fun y x ↦ B x y) := by
  intro y x rowLimit columnLimit rowOuter columnOuter
    hrow hcolumn hrowOuter hcolumnOuter
  exact (hB x y columnLimit rowLimit columnOuter rowOuter
    hcolumn hrow hcolumnOuter hrowOuter).symm

/-- A dual on a finite coordinate module equals the coordinate row formed
from its values on the standard coordinate vectors. -/
theorem coordinateRowDual_values_eq
    {K ι : Type*} [CommRing K] [Fintype ι]
    (l : Module.Dual K (ι → K)) :
    coordinateRowDual (fun i ↦ l (coordinateUnit i)) = l := by
  ext x
  rw [coordinateRowDual_apply]
  exact (dual_apply_eq_sum_single l x).symm

/-- The right-translation word-support kernel of an arbitrary coordinate
dual has the Boolean double-limit property.  The established matrix kernel
uses the opposite concatenation order, so this is precisely its transpose. -/
theorem matrixObservedWordNonzero_hasBooleanDoubleLimitProperty
    {K ι : Type*} [CommRing K] [Fintype ι]
    {b : ℕ} (M : Fin b → Matrix ι ι K)
    (l : Module.Dual K (ι → K)) (v : ι → K) :
    HasBooleanDoubleLimitProperty (fun w z : List (Fin b) ↦
      nonzeroBool
        (l (linearWord (fun r ↦ Matrix.mulVecLin (M r)) (z ++ w) v))) := by
  let a : ι → K := fun i ↦ l (coordinateUnit i)
  have h :=
    (matrixWordsNonzeroBool_hasBooleanDoubleLimitProperty M v a).swap
  simpa only [matrixWordsNonzeroBool, a, coordinateRowDual_values_eq l] using h

/-- Intrinsic padded-word support kernels of radix-regular sequences have the
Boolean double-limit property.  This form is convenient for finite Boolean
combinations, since it no longer exposes a chosen matrix representation. -/
theorem radixRegular_paddedSupportKernel_hasBooleanDoubleLimitProperty
    {K : Type*} [CommRing K] (b : ℕ) (hb : 2 ≤ b)
    (f : ℕ → K) (hregular : IsRadixRegular b f) :
    HasBooleanDoubleLimitProperty (fun x y : List (Fin b) ↦
      nonzeroBool (f (Nat.ofDigits b ((x ++ y).map Fin.val)))) := by
  obtain ⟨d, M, u, l, hrec, hout⟩ :=
    radixRegular_exists_matrix_representation b hb f hregular
  let a : Fin d → K := fun i ↦ l (coordinateUnit i)
  have h := matrixWordsNonzeroBool_hasBooleanDoubleLimitProperty M (u 0) a
  have hkernel : matrixWordsNonzeroBool M (u 0) a =
      (fun x y : List (Fin b) ↦
        nonzeroBool (f (Nat.ofDigits b ((x ++ y).map Fin.val)))) := by
    funext x y
    unfold matrixWordsNonzeroBool
    rw [show coordinateRowDual a = l by
      simpa only [a] using coordinateRowDual_values_eq l]
    rw [linearWord_apply_digitRecurrence_seed b
      (fun r ↦ Matrix.mulVecLin (M r)) u hrec, hout]
  rw [hkernel] at h
  exact h

/-- Every finite coordinate matrix recurrence has the IID seed limits needed
by the radix-shell transfer. -/
theorem matrix_hasObservedSeedIidCesaroMeans
    {K ι : Type*} [CommRing K] [Fintype ι]
    (b : ℕ) (hb : 0 < b) (M : Fin b → Matrix ι ι K)
    (l : Module.Dual K (ι → K)) :
    HasObservedSeedIidCesaroMeans hb
      (fun r ↦ Matrix.mulVecLin (M r)) l := by
  intro v
  let q : List (Fin b) → Bool := fun w ↦
    nonzeroBool
      (l (linearWord (fun r ↦ Matrix.mulVecLin (M r)) w v))
  have hDLP : HasBooleanDoubleLimitProperty (fun w z ↦ q (z ++ w)) := by
    simpa only [q] using
      matrixObservedWordNonzero_hasBooleanDoubleLimitProperty M l v
  letI : Nonempty (Fin b) := ⟨⟨0, hb⟩⟩
  obtain ⟨L, hL⟩ :=
    exists_tendsto_boolean_uniform_iid_word_cesaro q hDLP
  refine ⟨L, ?_⟩
  unfold observedSeedUniformIidWordCesaro
  have hfunctions : observedSeedWordSupport
      (fun r ↦ Matrix.mulVecLin (M r)) l v = booleanWordIndicator q := by
    ext w
    classical
    rw [observedSeedWordSupport_apply, booleanWordIndicator_apply,
      boolIndicator_nonzeroBool]
    simp [nonzeroIndicator]
  rw [hfunctions]
  exact hL

/-- Unconditional logarithmic-density existence for the support of a finite
matrix digit recurrence over an arbitrary commutative ring. -/
theorem matrix_observed_support_logDensity_exists
    {K ι : Type*} [CommRing K] [Fintype ι]
    (b : ℕ) (hb : 2 ≤ b) (M : Fin b → Matrix ι ι K)
    (u : ℕ → ι → K)
    (hrec : ∀ n (r : Fin b),
      u (b * n + r.val) = Matrix.mulVecLin (M r) (u n))
    (l : Module.Dual K (ι → K)) :
    ∃ delta : ℝ, HasPredicateLogDensity (fun n ↦ l (u n) ≠ 0) delta := by
  apply exists_logDensity_of_observedSeedIidCesaro b hb
    (fun r ↦ Matrix.mulVecLin (M r)) u hrec l
  exact matrix_hasObservedSeedIidCesaroMeans b (by omega) M l

/-- The support of every radix-regular sequence over a commutative ring has
a logarithmic density. -/
theorem radixRegular_support_logDensity_exists
    {K : Type*} [CommRing K] (b : ℕ) (hb : 2 ≤ b)
    (f : ℕ → K) (hregular : IsRadixRegular b f) :
    ∃ delta : ℝ, HasPredicateLogDensity (fun n ↦ f n ≠ 0) delta := by
  obtain ⟨d, M, u, l, hrec, hout⟩ :=
    radixRegular_exists_matrix_representation b hb f hregular
  obtain ⟨delta, hdelta⟩ :=
    matrix_observed_support_logDensity_exists b hb M u hrec l
  refine ⟨delta, ?_⟩
  simpa only [hout] using hdelta

/-- Existence together with the intrinsic zero-value certificate: the unique
support logarithmic density is zero exactly when a nonempty digit word is
forbidden. -/
theorem radixRegular_support_logDensity_exists_and_zero_iff_forbiddenDigitWord
    {K : Type*} [CommRing K] (b : ℕ) (hb : 2 ≤ b)
    (f : ℕ → K) (hregular : IsRadixRegular b f) :
    ∃ delta : ℝ,
      HasPredicateLogDensity (fun n ↦ f n ≠ 0) delta ∧
      (delta = 0 ↔ HasForbiddenDigitWord b (fun n ↦ f n ≠ 0)) := by
  obtain ⟨delta, hdelta⟩ :=
    radixRegular_support_logDensity_exists b hb f hregular
  refine ⟨delta, hdelta, ?_⟩
  have hzero :=
    (radixRegular_support_five_way_classification b hb f hregular).2.2.2.2
  constructor
  · intro hdelta0
    apply hzero.mp
    change HasPredicateLogDensity (fun n ↦ f n ≠ 0) 0
    simpa only [hdelta0] using hdelta
  · intro hforbidden
    exact tendsto_nhds_unique hdelta (hzero.mpr hforbidden)

end IndependentZeroBlocks
