import SierpinskiFormal.DilationInitialZero
import SierpinskiFormal.PrefixDilation

set_option autoImplicit false

/-!
# Finite zero-window criteria for repeated prefix filters

A uniform bound `R` on the number of prefix operations gives a uniform
zero-window threshold `R+1`. The coefficient field and family index type
are arbitrary. No finite-field synchronization condition is used.
-/

namespace IndependentZeroBlocks

open SierpinskiFormal

/-- Repeated prefix filters, with uniformly bounded orders, inherit all
descendant intervals of a common trailing zero window. -/
theorem prefixFilter_family_descendants
    {K ι : Type*} [Field K]
    (A : ι → Polynomial K) (F : ι → PowerSeries K) (r : ι → ℕ)
    (b R n : ℕ) (hb : 2 ≤ b) (hn : R + 1 ≤ n)
    (hr : ∀ i, r i ≤ R) (hdegree : ∀ i, (A i).natDegree < b)
    (hF : ∀ i, F i = (A i : PowerSeries K) * dilate b (F i))
    (hzero : ∀ i t, t < R + 1 → PowerSeries.coeff (n - t)
      (rationalMultiple 1 ((1 - Polynomial.X) ^ r i) (F i)) = 0) :
    ∀ E j, j < b ^ E → ∀ i, PowerSeries.coeff (n * b ^ E + j)
      (rationalMultiple 1 ((1 - Polynomial.X) ^ r i) (F i)) = 0 := by
  apply polynomial_dilation_family_descendants
    (fun i => prefixDilationKernel b (r i) (A i))
    (fun i => rationalMultiple 1 ((1 - Polynomial.X) ^ r i) (F i))
    b (R + 1) n hb (by omega) hn
  · intro i
    calc
      (prefixDilationKernel b (r i) (A i)).natDegree ≤
          (r i + 1) * (b - 1) :=
        prefixDilationKernel_natDegree_le b (r i) hb (A i) (hdegree i)
      _ ≤ (R + 1) * (b - 1) := Nat.mul_le_mul_right _ (by have := hr i; omega)
      _ = (b - 1) * (R + 1) := Nat.mul_comm _ _
  · intro i
    exact prefixFilter_dilation_equation b (r i) hb (A i) (F i) (hF i)
  · exact hzero

/-- An exact finite-window criterion for any family of uniformly bounded
prefix orders. The window may start at zero; its location is not bounded. -/
theorem prefixFilter_family_zeroBlocks_iff
    {K ι : Type*} [Field K]
    (A : ι → Polynomial K) (F : ι → PowerSeries K) (r : ι → ℕ)
    (b R : ℕ) (hb : 2 ≤ b)
    (hr : ∀ i, r i ≤ R) (hdegree : ∀ i, (A i).natDegree < b)
    (hF : ∀ i, F i = (A i : PowerSeries K) * dilate b (F i)) :
    HasArbitrarilyLongZeroBlocks (fun n i => PowerSeries.coeff n
      (rationalMultiple 1 ((1 - Polynomial.X) ^ r i) (F i))) ↔
      ∃ s, ∀ i t, t < R + 1 → PowerSeries.coeff (s + t)
        (rationalMultiple 1 ((1 - Polynomial.X) ^ r i) (F i)) = 0 := by
  apply polynomial_dilation_family_zeroBlocks_iff_any_window
    (fun i => prefixDilationKernel b (r i) (A i))
    (fun i => rationalMultiple 1 ((1 - Polynomial.X) ^ r i) (F i))
    b (R + 1) hb (by omega)
  · intro i
    calc
      (prefixDilationKernel b (r i) (A i)).natDegree ≤
          (r i + 1) * (b - 1) :=
        prefixDilationKernel_natDegree_le b (r i) hb (A i) (hdegree i)
      _ ≤ (R + 1) * (b - 1) := Nat.mul_le_mul_right _ (by have := hr i; omega)
      _ = (b - 1) * (R + 1) := Nat.mul_comm _ _
  · intro i
    exact prefixFilter_dilation_equation b (r i) hb (A i) (F i) (hF i)

/-- Constructed digit-product series need no assumed representation. For
`r` prefix operations, one common block of `r+1` zeros is necessary and sufficient. -/
theorem canonical_repeatedPrefix_family_zeroBlocks_iff
    {K ι : Type*} [Field K]
    (A : ι → Polynomial K) (b r : ℕ) (hb : 2 ≤ b)
    (hA0 : ∀ i, (A i).coeff 0 = 1)
    (hdegree : ∀ i, (A i).natDegree < b) :
    HasArbitrarilyLongZeroBlocks (fun n i => PowerSeries.coeff n
      (rationalMultiple 1 ((1 - Polynomial.X) ^ r) (canonicalSeries b (A i)))) ↔
      ∃ s, ∀ i t, t < r + 1 → PowerSeries.coeff (s + t)
        (rationalMultiple 1 ((1 - Polynomial.X) ^ r) (canonicalSeries b (A i))) = 0 := by
  exact prefixFilter_family_zeroBlocks_iff A (fun i => canonicalSeries b (A i))
    (fun _ => r) b r hb (fun _ => le_rfl) hdegree
    (fun i => canonicalSeries_dilation_equation b hb (A i) (hA0 i) (hdegree i))

/-- In particular, ordinary inclusive prefix sums have arbitrary common long
late zero blocks exactly when they have two common consecutive zeros, at any starting index. -/
theorem canonical_prefix_family_zeroBlocks_iff
    {K ι : Type*} [Field K]
    (A : ι → Polynomial K) (b : ℕ) (hb : 2 ≤ b)
    (hA0 : ∀ i, (A i).coeff 0 = 1)
    (hdegree : ∀ i, (A i).natDegree < b) :
    HasArbitrarilyLongZeroBlocks (fun n i => PowerSeries.coeff n
      (rationalMultiple 1 (1 - Polynomial.X) (canonicalSeries b (A i)))) ↔
      ∃ s, ∀ i,
        PowerSeries.coeff s
          (rationalMultiple 1 (1 - Polynomial.X) (canonicalSeries b (A i))) = 0 ∧
        PowerSeries.coeff (s + 1)
          (rationalMultiple 1 (1 - Polynomial.X) (canonicalSeries b (A i))) = 0 := by
  have h := canonical_repeatedPrefix_family_zeroBlocks_iff A b 1 hb hA0 hdegree
  simp only [pow_one] at h
  rw [h]
  constructor
  · rintro ⟨s, hz⟩
    exact ⟨s, fun i => ⟨by simpa using hz i 0 (by omega), hz i 1 (by omega)⟩⟩
  · rintro ⟨s, hz⟩
    refine ⟨s, ?_⟩
    intro i t ht
    have ht' : t = 0 ∨ t = 1 := by omega
    rcases ht' with rfl | rfl
    · simpa using (hz i).1
    · exact (hz i).2

end IndependentZeroBlocks
