import SierpinskiFormal.CanonicalSeries
import SierpinskiFormal.PoleEvaluation

set_option autoImplicit false

/-!
# Enlarging the finite-field radix

This file isolates the arithmetic and formal-power-series bridge used when a
canonical series over a finite field is viewed over a finite extension field.
-/

namespace IndependentZeroBlocks

open SierpinskiFormal

/-- The exponent by which a kernel is raised after passing from `K` to `L`. -/
def radixExtensionExponent
    (K L : Type*) [Field K] [Field L] [Fintype K] [Fintype L] : ℕ :=
  (Fintype.card L - 1) / (Fintype.card K - 1)

/-- The cardinality of a finite extension has the form required by the
finite-field dilation bridge. -/
theorem card_eq_pred_mul_radixExtensionExponent_add_one
    (K L : Type*) [Field K] [Field L] [Fintype K] [Fintype L] [Algebra K L] :
    Fintype.card L = (Fintype.card K - 1) * radixExtensionExponent K L + 1 := by
  have hdvd : Fintype.card K - 1 ∣ Fintype.card L - 1 :=
    card_sub_one_dvd_of_finite_extension (K := K) (L := L)
      (Fintype.card K - 1) (dvd_refl _)
  change Fintype.card L =
    (Fintype.card K - 1) *
      ((Fintype.card L - 1) / (Fintype.card K - 1)) + 1
  rw [Nat.mul_div_cancel' hdvd]
  exact (Nat.sub_add_cancel Fintype.card_pos).symm

theorem pred_card_eq_pred_mul_radixExtensionExponent
    (K L : Type*) [Field K] [Field L] [Fintype K] [Fintype L] [Algebra K L] :
    Fintype.card L - 1 =
      (Fintype.card K - 1) * radixExtensionExponent K L := by
  have h := card_eq_pred_mul_radixExtensionExponent_add_one K L
  omega

/-- The mapped branch equation, raised by the quotient of the two
multiplicative-group orders. -/
theorem map_branch_radixExtension
    {K L : Type*} [Field K] [Field L] [Fintype K] [Fintype L] [Algebra K L]
    (A : Polynomial K) (T : PowerSeries K)
    (hbranch : (A : PowerSeries K) * T ^ (Fintype.card K - 1) = 1) :
    (((A.map (algebraMap K L)) ^ radixExtensionExponent K L : Polynomial L) :
        PowerSeries L) *
      (PowerSeries.map (algebraMap K L) T) ^ (Fintype.card L - 1) = 1 := by
  let r := radixExtensionExponent K L
  have hcard := pred_card_eq_pred_mul_radixExtensionExponent K L
  have hmapped := congrArg (PowerSeries.map (algebraMap K L)) hbranch
  have hpowed := congrArg (fun U : PowerSeries L => U ^ r) hmapped
  simp only [map_mul, map_pow, map_one] at hpowed
  rw [mul_pow, ← pow_mul] at hpowed
  rw [show Fintype.card L - 1 = (Fintype.card K - 1) * r by simpa [r] using hcard]
  simpa [r, Polynomial.coe_pow] using hpowed

/-- A finite extension turns the mapped canonical branch into a dilation
equation in the enlarged radix. -/
theorem map_canonicalSeries_radixExtension_dilation
    {K L : Type*} [Field K] [Field L] [Fintype K] [Fintype L] [Algebra K L]
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < Fintype.card K) :
    let r := radixExtensionExponent K L
    let B := (A.map (algebraMap K L)) ^ r
    let T := PowerSeries.map (algebraMap K L)
      (canonicalSeries (Fintype.card K) A)
    T = (B : PowerSeries L) * dilate (Fintype.card L) T := by
  dsimp only
  have hcard : Fintype.card L = (Fintype.card L - 1) * 1 + 1 := by
    have := Fintype.card_pos (α := L)
    omega
  have hbranch := map_branch_radixExtension (L := L) A
    (canonicalSeries (Fintype.card K) A)
    (canonicalSeries_finiteField_branch A hA0 hdegree)
  have hbranch' :
      (A.map (algebraMap K L) : PowerSeries L) ^ radixExtensionExponent K L *
        (PowerSeries.map (algebraMap K L)
          (canonicalSeries (Fintype.card K) A)) ^ (Fintype.card L - 1) = 1 := by
    simpa only [Polynomial.coe_pow] using hbranch
  simpa only [Nat.mul_one] using finiteField_dilation_equation
    (A.map (algebraMap K L))
    (PowerSeries.map (algebraMap K L)
      (canonicalSeries (Fintype.card K) A))
    (radixExtensionExponent K L) (Fintype.card L - 1) 1 hcard hbranch'

/-- The enlarged kernel remains strictly below the enlarged radix whenever
the original kernel was strictly below `q-1`. -/
theorem natDegree_radixExtensionKernel_lt
    {K L : Type*} [Field K] [Field L] [Fintype K] [Fintype L] [Algebra K L]
    (A : Polynomial K) (hdegree : A.natDegree < Fintype.card K - 1) :
    ((A.map (algebraMap K L)) ^ radixExtensionExponent K L).natDegree <
      Fintype.card L - 1 := by
  let r := radixExtensionExponent K L
  have hcard := pred_card_eq_pred_mul_radixExtensionExponent K L
  have hrpos : 0 < r := by
    have hq : 2 ≤ Fintype.card K := Fintype.one_lt_card
    have hQ : 2 ≤ Fintype.card L := Fintype.one_lt_card
    by_contra hr
    have : r = 0 := by omega
    have : radixExtensionExponent K L = 0 := by simpa [r] using this
    rw [this, Nat.mul_zero] at hcard
    omega
  calc
    ((A.map (algebraMap K L)) ^ r).natDegree
        ≤ r * (A.map (algebraMap K L)).natDegree := Polynomial.natDegree_pow_le
    _ ≤ r * A.natDegree := Nat.mul_le_mul_left r Polynomial.natDegree_map_le
    _ < r * (Fintype.card K - 1) := Nat.mul_lt_mul_of_pos_left hdegree hrpos
    _ = Fintype.card L - 1 := by simpa [r, Nat.mul_comm] using hcard.symm

/-- Below the old radix, raising the mapped kernel by the extension exponent
does not change its coefficients.  In particular, the first positive nonzero
digit of the kernel is preserved by radix enlargement. -/
theorem coeff_radixExtensionKernel_of_lt_card
    {K L : Type*} [Field K] [Field L] [Fintype K] [Fintype L] [Algebra K L]
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < Fintype.card K - 1)
    (d : ℕ) (hd : d < Fintype.card K) :
    ((A.map (algebraMap K L)) ^ radixExtensionExponent K L).coeff d =
      algebraMap K L (A.coeff d) := by
  let B := (A.map (algebraMap K L)) ^ radixExtensionExponent K L
  let T := PowerSeries.map (algebraMap K L)
    (canonicalSeries (Fintype.card K) A)
  have hq : 2 ≤ Fintype.card K := Fintype.one_lt_card
  have hcardle : Fintype.card K ≤ Fintype.card L :=
    Fintype.card_le_of_injective (algebraMap K L) (algebraMap K L).injective
  have hdL : d < Fintype.card L := lt_of_lt_of_le hd hcardle
  have hBdegree : B.natDegree < Fintype.card L :=
    lt_trans (natDegree_radixExtensionKernel_lt A hdegree) (by omega)
  have hT : T = (B : PowerSeries L) * dilate (Fintype.card L) T :=
    map_canonicalSeries_radixExtension_dilation A hA0 (by omega)
  have hT0 : PowerSeries.coeff 0 T = 1 := by
    simp [T]
  have hlow := low_coeff_of_dilation_equation
    (Fintype.card L) Fintype.card_pos B hBdegree T hT hT0 d hdL
  have hold : PowerSeries.coeff d
      (canonicalSeries (Fintype.card K) A) = A.coeff d := by
    simpa using coeff_canonicalSeries_mul_add
      (Fintype.card K) hq A hA0 0 d hd
  change B.coeff d = algebraMap K L (A.coeff d)
  rw [← hlow]
  simp only [T, PowerSeries.coeff_map, hold]

/-- Radix enlargement preserves nonconstancy as well as the strict degree
gap.  This is the degree window required by the kernel-prefix machinery. -/
theorem radixExtensionKernel_degree_window
    {K L : Type*} [Field K] [Field L] [Fintype K] [Fintype L] [Algebra K L]
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hpos : 0 < A.natDegree)
    (hdegree : A.natDegree < Fintype.card K - 1) :
    0 < ((A.map (algebraMap K L)) ^ radixExtensionExponent K L).natDegree ∧
      ((A.map (algebraMap K L)) ^ radixExtensionExponent K L).natDegree <
        Fintype.card L - 1 := by
  let B := (A.map (algebraMap K L)) ^ radixExtensionExponent K L
  have hAne : A ≠ 0 := by
    intro hzero
    simp [hzero] at hpos
  have hlead : A.coeff A.natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hAne
  have hcoeff : B.coeff A.natDegree ≠ 0 := by
    rw [show B.coeff A.natDegree = algebraMap K L (A.coeff A.natDegree) by
      exact coeff_radixExtensionKernel_of_lt_card A hA0 hdegree A.natDegree (by omega)]
    exact (map_ne_zero (algebraMap K L)).mpr hlead
  refine ⟨lt_of_lt_of_le hpos (Polynomial.le_natDegree_of_ne_zero hcoeff), ?_⟩
  exact natDegree_radixExtensionKernel_lt A hdegree

/-- The transport facts bundled in the form consumed by the common-kernel
and prefix theorems. -/
theorem mapped_canonicalSeries_radixExtension_data
    {K L : Type*} [Field K] [Field L] [Fintype K] [Fintype L] [Algebra K L]
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hpos : 0 < A.natDegree)
    (hdegree : A.natDegree < Fintype.card K - 1) :
    let B := (A.map (algebraMap K L)) ^ radixExtensionExponent K L
    let T := PowerSeries.map (algebraMap K L)
      (canonicalSeries (Fintype.card K) A)
    PowerSeries.coeff 0 T = 1 ∧
      0 < B.natDegree ∧
      B.natDegree < Fintype.card L - 1 ∧
      T = (B : PowerSeries L) * dilate (Fintype.card L) T := by
  dsimp only
  refine ⟨by simp, ?_, ?_, ?_⟩
  · exact (radixExtensionKernel_degree_window A hA0 hpos hdegree).1
  · exact (radixExtensionKernel_degree_window A hA0 hpos hdegree).2
  · exact map_canonicalSeries_radixExtension_dilation A hA0 (by omega)

end IndependentZeroBlocks

#print axioms IndependentZeroBlocks.map_canonicalSeries_radixExtension_dilation
#print axioms IndependentZeroBlocks.natDegree_radixExtensionKernel_lt
#print axioms IndependentZeroBlocks.coeff_radixExtensionKernel_of_lt_card
#print axioms IndependentZeroBlocks.radixExtensionKernel_degree_window
#print axioms IndependentZeroBlocks.mapped_canonicalSeries_radixExtension_data
