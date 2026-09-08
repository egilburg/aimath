import SierpinskiFormal.CanonicalSeries
import SierpinskiFormal.ZeroBlocks
import Mathlib.RingTheory.PowerSeries.Inverse

set_option autoImplicit false

namespace IndependentZeroBlocks
open scoped BigOperators
open SierpinskiFormal

/-- All sufficiently deep descendant intervals vanish after a fixed left trim. -/
def HasSeedBlocks {K : Type*} [Semiring K] (q seed : ℕ) (T : PowerSeries K) : Prop :=
  ∃ h depth : ℕ, ∀ E, depth ≤ E → ∀ j, h ≤ j → j < q ^ E →
    PowerSeries.coeff (seed * q ^ E + j) T = 0

theorem HasSeedBlocks.zero {K : Type*} [Semiring K] (q seed : ℕ) :
    HasSeedBlocks q seed (0 : PowerSeries K) := by
  refine ⟨0, 0, ?_⟩
  simp

theorem HasSeedBlocks.add {K : Type*} [Semiring K] {q seed : ℕ}
    {T U : PowerSeries K} (hT : HasSeedBlocks q seed T)
    (hU : HasSeedBlocks q seed U) : HasSeedBlocks q seed (T + U) := by
  obtain ⟨h, d, hT⟩ := hT
  obtain ⟨k, e, hU⟩ := hU
  refine ⟨max h k, max d e, ?_⟩
  intro E hE j hj hjq
  rw [map_add, hT E (by omega) j (by omega) hjq,
    hU E (by omega) j (by omega) hjq, zero_add]

theorem HasSeedBlocks.polynomial_mul {K : Type*} [CommRing K] {q seed : ℕ}
    {T : PowerSeries K} (hT : HasSeedBlocks q seed T) (P : Polynomial K) :
    HasSeedBlocks q seed ((P : PowerSeries K) * T) := by
  obtain ⟨h, d, hT⟩ := hT
  refine ⟨h + P.natDegree, d, ?_⟩
  intro E hE j hj hjq
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_eq_zero
  intro r hr
  by_cases hrP : r ≤ P.natDegree
  · have hsub : seed * q ^ E + j - r = seed * q ^ E + (j - r) := by omega
    rw [hsub, hT E hE (j-r) (by omega) (by omega), mul_zero]
  · have hcoef : PowerSeries.coeff r (P : PowerSeries K) = 0 := by
      simpa using Polynomial.coeff_eq_zero_of_natDegree_lt (show P.natDegree < r by omega)
    rw [hcoef, zero_mul]

theorem HasSeedBlocks.sum {K ι : Type*} [CommRing K] {q seed : ℕ}
    (s : Finset ι) (T : ι → PowerSeries K)
    (hT : ∀ i ∈ s, HasSeedBlocks q seed (T i)) :
    HasSeedBlocks q seed (∑ i ∈ s, T i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasSeedBlocks.zero (K := K) q seed
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hT a (Finset.mem_insert_self _ _)).add
        (ih (fun i hi => hT i (Finset.mem_insert_of_mem hi)))

theorem HasSeedBlocks.zeroBlocks {K : Type*} [Semiring K] {q seed : ℕ}
    {T : PowerSeries K} (hT : HasSeedBlocks q seed T)
    (hq : 2 ≤ q) (hseed : 1 ≤ seed) :
    HasArbitrarilyLongZeroBlocks (fun n => PowerSeries.coeff n T) := by
  obtain ⟨h, depth, hT⟩ := hT
  intro length start
  let E := length + start + h + depth + 1
  have hpow : E < q ^ E := exponent_lt_base_pow q E hq
  have hE : E = length + start + h + depth + 1 := rfl
  have hmul : q ^ E ≤ seed * q ^ E := Nat.le_mul_of_pos_left _ hseed
  refine ⟨seed * q ^ E + h, by omega, ?_⟩
  intro j hj
  rw [Nat.add_assoc]
  exact hT E (by omega) (h+j) (by omega) (by omega)

/-- The power-series expansion of the rational multiplier `P/D` applied to `T`. -/
noncomputable def rationalMultiple {K : Type*} [Field K]
    (P D : Polynomial K) (T : PowerSeries K) : PowerSeries K :=
  (P : PowerSeries K) * (D : PowerSeries K)⁻¹ * T

theorem rationalMultiple_denominator {K : Type*} [Field K]
    (P D : Polynomial K) (T : PowerSeries K) (hD : D.coeff 0 ≠ 0) :
    (D : PowerSeries K) * rationalMultiple P D T = (P : PowerSeries K) * T := by
  have hinv := PowerSeries.mul_inv_cancel (D : PowerSeries K) (by simpa using hD)
  unfold rationalMultiple
  calc
    (D : PowerSeries K) * ((P : PowerSeries K) * (D : PowerSeries K)⁻¹ * T) =
      (P : PowerSeries K) * ((D : PowerSeries K) * (D : PowerSeries K)⁻¹) * T := by ring
    _ = (P : PowerSeries K) * T := by rw [hinv, mul_one]

theorem eq_rationalMultiple_of_denominator {K : Type*} [Field K]
    (P D : Polynomial K) (T U : PowerSeries K) (hD : D.coeff 0 ≠ 0)
    (hU : (D : PowerSeries K) * U = (P : PowerSeries K) * T) :
    U = rationalMultiple P D T := by
  have hne : (D : PowerSeries K) ≠ 0 := by
    intro hz
    apply hD
    have := congrArg (PowerSeries.coeff 0) hz
    simpa using this
  apply mul_left_cancel₀ hne
  rw [hU, rationalMultiple_denominator P D T hD]

theorem HasSeedBlocks.of_map {K L : Type*} [CommRing K] [CommRing L]
    (f : K →+* L) (hf : Function.Injective f) {q seed : ℕ}
    {T : PowerSeries K} (hT : HasSeedBlocks q seed (PowerSeries.map f T)) :
    HasSeedBlocks q seed T := by
  obtain ⟨h, d, hT⟩ := hT
  refine ⟨h, d, ?_⟩
  intro E hE j hj hjq
  apply hf
  simpa using hT E hE j hj hjq

theorem map_rationalMultiple {K L : Type*} [Field K] [Field L]
    (f : K →+* L) (P D : Polynomial K) (T : PowerSeries K)
    (hD : D.coeff 0 ≠ 0) :
    PowerSeries.map f (rationalMultiple P D T) =
      rationalMultiple (P.map f) (D.map f) (PowerSeries.map f T) := by
  apply eq_rationalMultiple_of_denominator
  · simpa using (map_ne_zero f).mpr hD
  · have h := congrArg (PowerSeries.map f) (rationalMultiple_denominator P D T hD)
    simpa using h

end IndependentZeroBlocks
