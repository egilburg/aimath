import SierpinskiFormal.SeedBlocks

set_option autoImplicit false

/-!
# Finite families of seed blocks and rational denominators

This file packages two elementary finite-family operations: choosing uniform
trim/depth data for seed blocks, and replacing finitely many rational
denominators by their product.
-/

namespace IndependentZeroBlocks

open scoped BigOperators
open SierpinskiFormal

/-- A finite collection of seed-block witnesses admits one common left trim
and one common starting depth. -/
theorem exists_common_seedBlock_data_finset
    {K ι : Type*} [Semiring K] {q seed : ℕ}
    (s : Finset ι) (T : ι → PowerSeries K)
    (hT : ∀ i ∈ s, HasSeedBlocks q seed (T i)) :
    ∃ h depth : ℕ, ∀ i ∈ s, ∀ E, depth ≤ E →
      ∀ j, h ≤ j → j < q ^ E →
        PowerSeries.coeff (seed * q ^ E + j) (T i) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨0, 0, by simp⟩
  | @insert a s ha ih =>
      obtain ⟨haTrim, haDepth, haBlocks⟩ := hT a (Finset.mem_insert_self a s)
      obtain ⟨hsTrim, hsDepth, hsBlocks⟩ :=
        ih (fun i hi => hT i (Finset.mem_insert_of_mem hi))
      refine ⟨max haTrim hsTrim, max haDepth hsDepth, ?_⟩
      intro i hi E hE j hj hjq
      rw [Finset.mem_insert] at hi
      rcases hi with rfl | hi
      · exact haBlocks E (by omega) j (by omega) hjq
      · exact hsBlocks i hi E (by omega) j (by omega) hjq

/-- A `Fintype`-indexed family of seed blocks has uniform trim/depth data. -/
theorem exists_common_seedBlock_data
    {K ι : Type*} [Semiring K] [Fintype ι] {q seed : ℕ}
    (T : ι → PowerSeries K) (hT : ∀ i, HasSeedBlocks q seed (T i)) :
    ∃ h depth : ℕ, ∀ i, ∀ E, depth ≤ E →
      ∀ j, h ≤ j → j < q ^ E →
        PowerSeries.coeff (seed * q ^ E + j) (T i) = 0 := by
  classical
  obtain ⟨h, depth, hblocks⟩ :=
    exists_common_seedBlock_data_finset Finset.univ T
      (fun i _ => hT i)
  exact ⟨h, depth, fun i => hblocks i (Finset.mem_univ i)⟩

/-- Finitely many series with the same seed have simultaneous arbitrarily
late zero intervals. -/
theorem exists_simultaneous_zeroBlock
    {K ι : Type*} [Semiring K] [Fintype ι] {q seed : ℕ}
    (T : ι → PowerSeries K) (hT : ∀ i, HasSeedBlocks q seed (T i))
    (hq : 2 ≤ q) (hseed : 1 ≤ seed) (length start : ℕ) :
    ∃ N, start ≤ N ∧ ∀ i, ∀ j, j < length →
      PowerSeries.coeff (N + j) (T i) = 0 := by
  obtain ⟨h, depth, hblocks⟩ := exists_common_seedBlock_data T hT
  let E := length + start + h + depth + 1
  have hpow : E < q ^ E := exponent_lt_base_pow q E hq
  have hmul : q ^ E ≤ seed * q ^ E := Nat.le_mul_of_pos_left _ hseed
  refine ⟨seed * q ^ E + h, by omega, ?_⟩
  intro i j hj
  rw [Nat.add_assoc]
  exact hblocks i E (by omega) (h + j) (by omega) (by omega)

/-- Quantified form of `exists_simultaneous_zeroBlock`. -/
theorem has_simultaneous_zeroBlocks
    {K ι : Type*} [Semiring K] [Fintype ι] {q seed : ℕ}
    (T : ι → PowerSeries K) (hT : ∀ i, HasSeedBlocks q seed (T i))
    (hq : 2 ≤ q) (hseed : 1 ≤ seed) :
    ∀ length start, ∃ N, start ≤ N ∧ ∀ i, ∀ j, j < length →
      PowerSeries.coeff (N + j) (T i) = 0 := by
  exact fun length start =>
    exists_simultaneous_zeroBlock T hT hq hseed length start

/-- Enlarging a rational denominator by a polynomial factor, while
enlarging the numerator by the same factor, does not change the resulting
power series. -/
theorem rationalMultiple_eq_of_mul_denominator
    {K : Type*} [Field K]
    (P D E : Polynomial K) (T : PowerSeries K)
    (hD0 : D.coeff 0 ≠ 0) (hDE0 : (D * E).coeff 0 ≠ 0) :
    rationalMultiple P D T = rationalMultiple (P * E) (D * E) T := by
  apply eq_rationalMultiple_of_denominator (P * E) (D * E) T
    (rationalMultiple P D T) hDE0
  have hden := rationalMultiple_denominator P D T hD0
  rw [Polynomial.coe_mul, Polynomial.coe_mul]
  calc
    (D : PowerSeries K) * (E : PowerSeries K) * rationalMultiple P D T =
        (E : PowerSeries K) *
          ((D : PowerSeries K) * rationalMultiple P D T) := by ring
    _ = (E : PowerSeries K) * ((P : PowerSeries K) * T) := by rw [hden]
    _ = (P : PowerSeries K) * (E : PowerSeries K) * T := by ring

/-- The constant coefficient of a finite product is nonzero when every
factor has nonzero constant coefficient. -/
theorem coeff_zero_finset_prod_ne_zero
    {K ι : Type*} [Field K] (s : Finset ι) (D : ι → Polynomial K)
    (hD0 : ∀ i ∈ s, (D i).coeff 0 ≠ 0) :
    (∏ i ∈ s, D i).coeff 0 ≠ 0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]
  apply (Finset.prod_ne_zero_iff.mpr ?_)
  intro i hi
  simpa [← Polynomial.coeff_zero_eq_eval_zero] using hD0 i hi

/-- Product denominator attached to a finite family. -/
noncomputable def commonDenominator
    {K ι : Type*} [Field K] [Fintype ι]
    (D : ι → Polynomial K) : Polynomial K :=
  ∏ i : ι, D i

/-- Numerator obtained by clearing every denominator except the indexed one. -/
noncomputable def commonNumerator
    {K ι : Type*} [Field K] [Fintype ι]
    (P D : ι → Polynomial K) (i : ι) : Polynomial K := by
  classical
  exact P i * ∏ j ∈ Finset.univ.erase i, D j

theorem commonDenominator_coeff_zero_ne_zero
    {K ι : Type*} [Field K] [Fintype ι]
    (D : ι → Polynomial K) (hD0 : ∀ i, (D i).coeff 0 ≠ 0) :
    (commonDenominator D).coeff 0 ≠ 0 := by
  classical
  exact coeff_zero_finset_prod_ne_zero Finset.univ D
    (fun i _ => hD0 i)

/-- Pointwise common-denominator identity with explicit numerator and
denominator definitions. -/
theorem rationalMultiple_eq_commonDenominator
    {K ι : Type*} [Field K] [Fintype ι]
    (P D : ι → Polynomial K) (T : ι → PowerSeries K)
    (hD0 : ∀ i, (D i).coeff 0 ≠ 0) (i : ι) :
    rationalMultiple (P i) (D i) (T i) =
      rationalMultiple (commonNumerator P D i) (commonDenominator D) (T i) := by
  classical
  let E : Polynomial K := ∏ j ∈ Finset.univ.erase i, D j
  have hfactor : D i * E = commonDenominator D := by
    dsimp [E, commonDenominator]
    exact Finset.mul_prod_erase Finset.univ D (Finset.mem_univ i)
  have hfactor0 : (D i * E).coeff 0 ≠ 0 := by
    rw [hfactor]
    exact commonDenominator_coeff_zero_ne_zero D hD0
  have hsame := rationalMultiple_eq_of_mul_denominator
    (P i) (D i) E (T i) (hD0 i) hfactor0
  simpa only [commonNumerator, E, hfactor] using hsame

/-- A finite family of rational multiples can be rewritten over the single
common denominator `∏ i, D i`.  The returned numerator is
`P i * ∏ j ≠ i, D j`. -/
theorem exists_common_denominator_numerators
    {K ι : Type*} [Field K] [Fintype ι]
    (P D : ι → Polynomial K) (T : ι → PowerSeries K)
    (hD0 : ∀ i, (D i).coeff 0 ≠ 0) :
    let Dall : Polynomial K := ∏ i : ι, D i
    ∃ N : ι → Polynomial K,
      Dall.coeff 0 ≠ 0 ∧
      ∀ i, rationalMultiple (P i) (D i) (T i) =
        rationalMultiple (N i) Dall (T i) := by
  classical
  let Dall : Polynomial K := ∏ i : ι, D i
  let E : ι → Polynomial K := fun i => ∏ j ∈ Finset.univ.erase i, D j
  let N : ι → Polynomial K := fun i => P i * E i
  have hDall0 : Dall.coeff 0 ≠ 0 := by
    dsimp [Dall]
    exact coeff_zero_finset_prod_ne_zero Finset.univ D
      (fun i _ => hD0 i)
  refine ⟨N, hDall0, ?_⟩
  intro i
  have hfactor : D i * E i = Dall := by
    dsimp [E, Dall]
    exact Finset.mul_prod_erase Finset.univ D (Finset.mem_univ i)
  have hfactor0 : (D i * E i).coeff 0 ≠ 0 := by
    rwa [hfactor]
  have hsame := rationalMultiple_eq_of_mul_denominator
    (P i) (D i) (E i) (T i) (hD0 i) hfactor0
  simpa only [N, hfactor] using hsame

end IndependentZeroBlocks

#print axioms IndependentZeroBlocks.exists_common_seedBlock_data
#print axioms IndependentZeroBlocks.has_simultaneous_zeroBlocks
#print axioms IndependentZeroBlocks.rationalMultiple_eq_commonDenominator
#print axioms IndependentZeroBlocks.exists_common_denominator_numerators
