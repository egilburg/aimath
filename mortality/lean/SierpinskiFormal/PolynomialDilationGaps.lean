import SierpinskiFormal.Lucas
import SierpinskiFormal.ZeroBlocks
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

/-!
# Zero blocks for polynomial dilation systems

This file treats a finite system of formal power series satisfying a polynomial
matrix dilation equation.  No characteristic assumption is used.  The degree
bound says exactly that a common block of `m` zero coefficients is inherited by
every base-`b` descendant of its ending index.
-/

namespace IndependentZeroBlocks

open scoped BigOperators
open SierpinskiFormal

/-- Appending one base-`b` digit preserves a common trailing block of `m`
zero coefficients for a polynomial matrix dilation system. -/
theorem polynomial_dilation_matrix_append
    {K ι : Type*} [CommRing K] [Fintype ι]
    (B : ι → ι → Polynomial K) (U : ι → PowerSeries K)
    (b m n r : ℕ) (hb : 2 ≤ b) (_hm : 1 ≤ m) (hn : m ≤ n)
    (hdegree : ∀ i j, (B i j).natDegree ≤ (b - 1) * m)
    (hEq : ∀ i, U i = ∑ j, (B i j : PowerSeries K) * dilate b (U j))
    (hzero : ∀ i t, t < m → PowerSeries.coeff (n - t) (U i) = 0)
    (hr : r < b) :
    m ≤ b * n + r ∧
      ∀ i t, t < m → PowerSeries.coeff (b * n + r - t) (U i) = 0 := by
  classical
  constructor
  · exact le_trans hn (le_trans (Nat.le_mul_of_pos_left n (by omega))
      (Nat.le_add_right _ _))
  · intro i t ht
    rw [hEq i, map_sum]
    apply Finset.sum_eq_zero
    intro j hj
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    apply Finset.sum_eq_zero
    intro a ha
    simp only [Prod.fst, Prod.snd]
    rw [Polynomial.coeff_coe, coeff_dilate]
    by_cases hab : b ∣ (b * n + r - t - a)
    · rw [if_pos hab]
      by_cases haB : a ≤ (B i j).natDegree
      · have habEq : b * ((b * n + r - t - a) / b) =
            b * n + r - t - a := Nat.mul_div_cancel' hab
        have hadeg : a ≤ (b - 1) * m := le_trans haB (hdegree i j)
        have hbm : (b - 1) * m + m = b * m := by
          calc
            (b - 1) * m + m = ((b - 1) + 1) * m := by
              rw [Nat.add_mul, one_mul]
            _ = b * m := by rw [Nat.sub_add_cancel (by omega)]
        have htm : t + a < b * m := by omega
        have hbmn : b * m ≤ b * n := Nat.mul_le_mul_left b hn
        have hta : t + a ≤ b * n + r := by omega
        have hsubEq : (b * n + r - t - a) + (t + a) = b * n + r := by
          rw [Nat.sub_sub, Nat.sub_add_cancel hta]
        have hquotle : (b * n + r - t - a) / b ≤ n := by
          by_contra hnot
          have hmul := Nat.mul_le_mul_left b (show n + 1 ≤
              (b * n + r - t - a) / b by omega)
          rw [habEq] at hmul
          have hlt : b * n + r - t - a < b * (n + 1) := by
            have hle : b * n + r - t - a ≤ b * n + r := by omega
            calc
              b * n + r - t - a ≤ b * n + r := hle
              _ < b * (n + 1) := by simp [Nat.mul_add]; omega
          omega
        have hquotlow : n < (b * n + r - t - a) / b + m := by
          by_contra hnot
          have hmul := Nat.mul_le_mul_left b (show
              (b * n + r - t - a) / b + m ≤ n by omega)
          rw [Nat.mul_add, habEq] at hmul
          have hlt : (b * n + r - t - a) + (t + a) <
              (b * n + r - t - a) + b * m :=
            Nat.add_lt_add_left htm _
          have hchildlt : b * n + r < b * n := by
            rw [← hsubEq]
            exact lt_of_lt_of_le hlt hmul
          omega
        have hshift : n - (n - ((b * n + r - t - a) / b)) =
            (b * n + r - t - a) / b := by omega
        have hz := hzero j (n - ((b * n + r - t - a) / b)) (by omega)
        rw [hshift] at hz
        rw [hz, mul_zero]
      · have hBa : (B i j).coeff a = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        rw [hBa, zero_mul]
    · rw [if_neg hab, mul_zero]

/-- A common trailing block for a polynomial matrix dilation system vanishes
on every explicit descendant interval of its ending index. -/
theorem polynomial_dilation_matrix_descendants
    {K ι : Type*} [CommRing K] [Fintype ι]
    (B : ι → ι → Polynomial K) (U : ι → PowerSeries K)
    (b m n : ℕ) (hb : 2 ≤ b) (hm : 1 ≤ m) (hn : m ≤ n)
    (hdegree : ∀ i j, (B i j).natDegree ≤ (b - 1) * m)
    (hEq : ∀ i, U i = ∑ j, (B i j : PowerSeries K) * dilate b (U j))
    (hzero : ∀ i t, t < m → PowerSeries.coeff (n - t) (U i) = 0) :
    ∀ E j, j < b ^ E → ∀ i,
      PowerSeries.coeff (n * b ^ E + j) (U i) = 0 := by
  let Z : ℕ → Prop := fun N =>
    m ≤ N ∧ ∀ i t, t < m → PowerSeries.coeff (N - t) (U i) = 0
  have hseed : Z n := ⟨hn, hzero⟩
  have happend : ∀ N r, r < b → Z N → Z (b * N + r) := by
    intro N r hr hN
    exact polynomial_dilation_matrix_append B U b m N r hb hm hN.1
      hdegree hEq hN.2 hr
  intro E j hj i
  have hdesc := descendants_of_append (q := b) (seed := n) (Z := Z)
    hb hseed happend E j hj
  exact hdesc.2 i 0 hm

/-- For a finite polynomial matrix dilation system, simultaneous zero blocks
of every length arbitrarily far out are equivalent to one simultaneous block
of the threshold length `m` beginning at a positive index. -/
theorem polynomial_dilation_matrix_zeroBlocks_iff
    {K ι : Type*} [CommRing K] [Fintype ι]
    (B : ι → ι → Polynomial K) (U : ι → PowerSeries K)
    (b m : ℕ) (hb : 2 ≤ b) (hm : 1 ≤ m)
    (hdegree : ∀ i j, (B i j).natDegree ≤ (b - 1) * m)
    (hEq : ∀ i, U i = ∑ j, (B i j : PowerSeries K) * dilate b (U j)) :
    HasArbitrarilyLongZeroBlocks
        (fun n i => PowerSeries.coeff n (U i)) ↔
      ∃ s, 1 ≤ s ∧ ∀ i t, t < m →
        PowerSeries.coeff (s + t) (U i) = 0 := by
  constructor
  · intro hblocks
    obtain ⟨s, hs, hzero⟩ := hblocks m 1
    refine ⟨s, hs, ?_⟩
    intro i t ht
    exact congrFun (hzero t ht) i
  · rintro ⟨s, hs, hzero⟩
    let n := s + m - 1
    have hn : m ≤ n := by dsimp [n]; omega
    have htrail : ∀ i t, t < m →
        PowerSeries.coeff (n - t) (U i) = 0 := by
      intro i t ht
      have hindex : n - t = s + (m - 1 - t) := by
        dsimp [n]
        omega
      rw [hindex]
      exact hzero i (m - 1 - t) (by omega)
    have hdesc := polynomial_dilation_matrix_descendants B U b m n hb hm hn
      hdegree hEq htrail
    apply hasArbitrarilyLongZeroBlocks_of_descendants (q := b) (seed := n) hb
      (by omega)
    intro E j hj
    funext i
    exact hdesc E j hj i

/-- Diagonal-family version of the explicit descendant theorem. -/
theorem polynomial_dilation_family_descendants
    {K ι : Type*} [CommRing K]
    (B : ι → Polynomial K) (U : ι → PowerSeries K)
    (b m n : ℕ) (hb : 2 ≤ b) (hm : 1 ≤ m) (hn : m ≤ n)
    (hdegree : ∀ i, (B i).natDegree ≤ (b - 1) * m)
    (hEq : ∀ i, U i = (B i : PowerSeries K) * dilate b (U i))
    (hzero : ∀ i t, t < m → PowerSeries.coeff (n - t) (U i) = 0) :
    ∀ E j, j < b ^ E → ∀ i,
      PowerSeries.coeff (n * b ^ E + j) (U i) = 0 := by
  intro E j hj i
  let B' : Unit → Unit → Polynomial K := fun _ _ => B i
  let U' : Unit → PowerSeries K := fun _ => U i
  have hdegree' : ∀ x y, (B' x y).natDegree ≤ (b - 1) * m := by
    intro x y
    exact hdegree i
  have hEq' : ∀ x, U' x = ∑ y, (B' x y : PowerSeries K) * dilate b (U' y) := by
    intro x
    simpa [B', U'] using hEq i
  have hzero' : ∀ x t, t < m → PowerSeries.coeff (n - t) (U' x) = 0 := by
    intro x t ht
    exact hzero i t ht
  exact polynomial_dilation_matrix_descendants B' U' b m n hb hm hn
    hdegree' hEq' hzero' E j hj ()

/-- Diagonal-family version of the one-block criterion. -/
theorem polynomial_dilation_family_zeroBlocks_iff
    {K ι : Type*} [CommRing K]
    (B : ι → Polynomial K) (U : ι → PowerSeries K)
    (b m : ℕ) (hb : 2 ≤ b) (hm : 1 ≤ m)
    (hdegree : ∀ i, (B i).natDegree ≤ (b - 1) * m)
    (hEq : ∀ i, U i = (B i : PowerSeries K) * dilate b (U i)) :
    HasArbitrarilyLongZeroBlocks
        (fun n i => PowerSeries.coeff n (U i)) ↔
      ∃ s, 1 ≤ s ∧ ∀ i t, t < m →
        PowerSeries.coeff (s + t) (U i) = 0 := by
  constructor
  · intro hblocks
    obtain ⟨s, hs, hzero⟩ := hblocks m 1
    refine ⟨s, hs, ?_⟩
    intro i t ht
    exact congrFun (hzero t ht) i
  · rintro ⟨s, hs, hzero⟩
    let n := s + m - 1
    have hn : m ≤ n := by dsimp [n]; omega
    have htrail : ∀ i t, t < m →
        PowerSeries.coeff (n - t) (U i) = 0 := by
      intro i t ht
      have hindex : n - t = s + (m - 1 - t) := by
        dsimp [n]
        omega
      rw [hindex]
      exact hzero i (m - 1 - t) (by omega)
    have hdesc := polynomial_dilation_family_descendants B U b m n hb hm hn
      hdegree hEq htrail
    apply hasArbitrarilyLongZeroBlocks_of_descendants (q := b) (seed := n) hb
      (by omega)
    intro E j hj
    funext i
    exact hdesc E j hj i

end IndependentZeroBlocks

#print axioms IndependentZeroBlocks.polynomial_dilation_matrix_descendants
#print axioms IndependentZeroBlocks.polynomial_dilation_matrix_zeroBlocks_iff
#print axioms IndependentZeroBlocks.polynomial_dilation_family_descendants
#print axioms IndependentZeroBlocks.polynomial_dilation_family_zeroBlocks_iff
