import SierpinskiFormal.DilationWindowThreshold

set_option autoImplicit false

/-!
# Initial zero windows for polynomial dilation systems

A homogeneous polynomial dilation system whose componentwise constant term is
zero has only the zero solution.  This removes the positive-start restriction
from the finite-window versions of the dilation gap criteria.
-/

namespace IndependentZeroBlocks

open scoped BigOperators
open SierpinskiFormal

/-- In a homogeneous polynomial matrix dilation system of radix at least two,
zero constant coefficients force every component series to vanish. -/
theorem polynomial_dilation_matrix_eq_zero_of_constant_coeff_eq_zero
    {K ι : Type*} [CommRing K] [Fintype ι]
    (B : ι → ι → Polynomial K) (U : ι → PowerSeries K)
    (b : ℕ) (hb : 2 ≤ b)
    (hEq : ∀ i, U i = ∑ j,
      (B i j : PowerSeries K) * dilate b (U j))
    (hconstant : ∀ i, PowerSeries.coeff 0 (U i) = 0) :
    ∀ i, U i = 0 := by
  classical
  have hcoeff : ∀ n i, PowerSeries.coeff n (U i) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro i
        rw [hEq i, map_sum]
        apply Finset.sum_eq_zero
        intro j hj
        rw [PowerSeries.coeff_mul,
          Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
        apply Finset.sum_eq_zero
        intro a ha
        simp only [Prod.fst, Prod.snd]
        rw [Polynomial.coeff_coe, coeff_dilate]
        by_cases hdvd : b ∣ n - a
        · rw [if_pos hdvd]
          have hparent : PowerSeries.coeff ((n - a) / b) (U j) = 0 := by
            by_cases hn : n = 0
            · subst n
              simpa using hconstant j
            · apply ih ((n - a) / b)
                (lt_of_le_of_lt (Nat.div_le_div_right (Nat.sub_le n a))
                  (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by omega)))
          rw [hparent, mul_zero]
        · rw [if_neg hdvd, mul_zero]
  intro i
  apply PowerSeries.ext
  intro n
  simpa using hcoeff n i

/-- The diagonal-family specialization of constant-term rigidity, valid for
an arbitrary index type. -/
theorem polynomial_dilation_family_eq_zero_of_constant_coeff_eq_zero
    {K ι : Type*} [CommRing K]
    (B : ι → Polynomial K) (U : ι → PowerSeries K)
    (b : ℕ) (hb : 2 ≤ b)
    (hEq : ∀ i, U i = (B i : PowerSeries K) * dilate b (U i))
    (hconstant : ∀ i, PowerSeries.coeff 0 (U i) = 0) :
    ∀ i, U i = 0 := by
  intro i
  let B' : Unit → Unit → Polynomial K := fun _ _ => B i
  let U' : Unit → PowerSeries K := fun _ => U i
  have hEq' : ∀ x, U' x = ∑ y,
      (B' x y : PowerSeries K) * dilate b (U' y) := by
    intro x
    simpa [B', U'] using hEq i
  have hconstant' : ∀ x, PowerSeries.coeff 0 (U' x) = 0 := by
    intro x
    exact hconstant i
  exact polynomial_dilation_matrix_eq_zero_of_constant_coeff_eq_zero
    B' U' b hb hEq' hconstant' ()

/-- Automatic-threshold matrix criterion allowing the witnessing window to
start at zero.  A zero-start window kills every solution component. -/
theorem polynomial_dilation_matrix_zeroBlocks_iff_any_window
    {K ι : Type*} [CommRing K] [Fintype ι]
    (B : ι → ι → Polynomial K) (U : ι → PowerSeries K)
    (b : ℕ) (hb : 2 ≤ b)
    (hEq : ∀ i, U i = ∑ j,
      (B i j : PowerSeries K) * dilate b (U j)) :
    HasArbitrarilyLongZeroBlocks
        (fun n i => PowerSeries.coeff n (U i)) ↔
      ∃ s, ∀ i t,
        t < polynomialDilationWindowThreshold B b →
          PowerSeries.coeff (s + t) (U i) = 0 := by
  constructor
  · intro hblocks
    obtain ⟨s, _, hzero⟩ :=
      hblocks (polynomialDilationWindowThreshold B b) 0
    refine ⟨s, ?_⟩
    intro i t ht
    exact congrFun (hzero t ht) i
  · rintro ⟨s, hzero⟩
    by_cases hs : s = 0
    · subst s
      have hconstant : ∀ i, PowerSeries.coeff 0 (U i) = 0 := by
        intro i
        simpa using hzero i 0 (polynomialDilationWindowThreshold_pos B b)
      have hU := polynomial_dilation_matrix_eq_zero_of_constant_coeff_eq_zero
        B U b hb hEq hconstant
      intro length start
      refine ⟨start, le_rfl, ?_⟩
      intro t ht
      funext i
      change PowerSeries.coeff (start + t) (U i) = 0
      rw [hU i]
      simp
    · apply (polynomial_dilation_matrix_zeroBlocks_iff_threshold
        B U b hb hEq).2
      exact ⟨s, Nat.one_le_iff_ne_zero.2 hs, hzero⟩

/-- Diagonal-family criterion allowing the common witnessing window to start
at zero. -/
theorem polynomial_dilation_family_zeroBlocks_iff_any_window
    {K ι : Type*} [CommRing K]
    (B : ι → Polynomial K) (U : ι → PowerSeries K)
    (b m : ℕ) (hb : 2 ≤ b) (hm : 1 ≤ m)
    (hdegree : ∀ i, (B i).natDegree ≤ (b - 1) * m)
    (hEq : ∀ i, U i = (B i : PowerSeries K) * dilate b (U i)) :
    HasArbitrarilyLongZeroBlocks
        (fun n i => PowerSeries.coeff n (U i)) ↔
      ∃ s, ∀ i t, t < m →
        PowerSeries.coeff (s + t) (U i) = 0 := by
  constructor
  · intro hblocks
    obtain ⟨s, _, hzero⟩ := hblocks m 0
    refine ⟨s, ?_⟩
    intro i t ht
    exact congrFun (hzero t ht) i
  · rintro ⟨s, hzero⟩
    by_cases hs : s = 0
    · subst s
      have hconstant : ∀ i, PowerSeries.coeff 0 (U i) = 0 := by
        intro i
        simpa using hzero i 0 hm
      have hU := polynomial_dilation_family_eq_zero_of_constant_coeff_eq_zero
        B U b hb hEq hconstant
      intro length start
      refine ⟨start, le_rfl, ?_⟩
      intro t ht
      funext i
      change PowerSeries.coeff (start + t) (U i) = 0
      rw [hU i]
      simp
    · apply (polynomial_dilation_family_zeroBlocks_iff
        B U b m hb hm hdegree hEq).2
      exact ⟨s, Nat.one_le_iff_ne_zero.2 hs, hzero⟩

end IndependentZeroBlocks

#print axioms IndependentZeroBlocks.polynomial_dilation_matrix_eq_zero_of_constant_coeff_eq_zero
#print axioms IndependentZeroBlocks.polynomial_dilation_family_eq_zero_of_constant_coeff_eq_zero
#print axioms IndependentZeroBlocks.polynomial_dilation_matrix_zeroBlocks_iff_any_window
#print axioms IndependentZeroBlocks.polynomial_dilation_family_zeroBlocks_iff_any_window
