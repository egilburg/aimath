import SierpinskiFormal.SupportDensityDefs
import Mathlib.RingTheory.PowerSeries.Trunc

set_option autoImplicit false

namespace IndependentZeroBlocks

open scoped BigOperators

/-! # A density obstruction for a proper rational power series

If `D * V = P` and `D` does not divide `P`, the tail of `V` cannot contain
`natDegree D` consecutive zero coefficients.  Splitting the tail into blocks
of that length gives the quantitative support bound at the end of the file.
-/

/-- A power series which is eventually zero is the coercion of its truncation. -/
private theorem eq_coe_trunc_of_coeff_eq_zero_ge {K : Type*} [Field K]
    (V : PowerSeries K) (s : ℕ)
    (hV : ∀ n, s ≤ n → PowerSeries.coeff n V = 0) :
    V = (PowerSeries.trunc s V : PowerSeries K) := by
  ext n
  rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
  by_cases hn : n < s
  · rw [if_pos hn]
  · rw [if_neg hn, hV n (Nat.le_of_not_gt hn)]

/-- In a proper rational power series, every sufficiently late interval of
length `D.natDegree` contains a nonzero coefficient. -/
theorem rational_tail_window_nonzero {K : Type*} [Field K]
    (P D : Polynomial K) (V : PowerSeries K)
    (hD0 : D.coeff 0 ≠ 0)
    (hDV : (D : PowerSeries K) * V = (P : PowerSeries K))
    (hproper : ¬ D ∣ P) :
    0 < D.natDegree ∧
      ∀ s : ℕ, P.natDegree < s →
        ∃ i : ℕ, i < D.natDegree ∧
          PowerSeries.coeff (s + i) V ≠ 0 := by
  have hm : 0 < D.natDegree := by
    by_contra hm
    have hdeg : D.natDegree = 0 := Nat.eq_zero_of_not_pos hm
    have hDC : D = Polynomial.C (D.coeff 0) :=
      Polynomial.eq_C_of_natDegree_eq_zero hdeg
    apply hproper
    refine ⟨Polynomial.C (D.coeff 0)⁻¹ * P, ?_⟩
    rw [hDC, ← mul_assoc, ← Polynomial.C_mul]
    simp [hD0]
  refine ⟨hm, ?_⟩
  intro s hs
  by_contra hblock
  push_neg at hblock
  have htail : ∀ j : ℕ, PowerSeries.coeff (s + j) V = 0 := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
        by_cases hj : j < D.natDegree
        · exact hblock j hj
        · have hmj : D.natDegree ≤ j := Nat.le_of_not_gt hj
          have hnP : P.natDegree < s + j := lt_of_lt_of_le hs (Nat.le_add_right s j)
          have hcoeff := congrArg (PowerSeries.coeff (s + j)) hDV
          rw [PowerSeries.coeff_mul,
            Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at hcoeff
          simp only [Polynomial.coeff_coe] at hcoeff
          have hsum :
              ∑ r ∈ Finset.range (s + j + 1),
                  D.coeff r * PowerSeries.coeff (s + j - r) V =
                D.coeff 0 * PowerSeries.coeff (s + j) V := by
            rw [Finset.sum_eq_single 0]
            · simp
            · intro r hr hr0
              by_cases hrm : r ≤ D.natDegree
              · have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
                have hrj : r ≤ j := le_trans hrm hmj
                have hindex : s + j - r = s + (j - r) := by omega
                rw [hindex, ih (j - r) (Nat.sub_lt (by omega) hrpos), mul_zero]
              · have hDr : D.coeff r = 0 :=
                  Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_not_ge hrm)
                rw [hDr, zero_mul]
            · simp
          rw [hsum] at hcoeff
          have hPzero : P.coeff (s + j) = 0 :=
            Polynomial.coeff_eq_zero_of_natDegree_lt hnP
          rw [hPzero] at hcoeff
          exact (mul_eq_zero.mp hcoeff).resolve_left hD0
  let Q : Polynomial K := PowerSeries.trunc s V
  have hVQ : V = (Q : PowerSeries K) := by
    apply eq_coe_trunc_of_coeff_eq_zero_ge V s
    intro n hn
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
    exact htail j
  apply hproper
  have hpolyPS : ((D * Q : Polynomial K) : PowerSeries K) =
      (P : PowerSeries K) := by
    rw [Polynomial.coe_mul, ← hVQ]
    exact hDV
  exact ⟨Q, Polynomial.coe_injective K hpolyPS.symm⟩

/-- Quantitative tail obstruction: apart from an initial segment depending on
the numerator, each block of `D.natDegree` indices contributes to the support. -/
theorem rational_tail_supportCount_bound {K : Type*} [Field K]
    (P D : Polynomial K) (V : PowerSeries K)
    (hD0 : D.coeff 0 ≠ 0)
    (hDV : (D : PowerSeries K) * V = (P : PowerSeries K))
    (hproper : ¬ D ∣ P) (N : ℕ) :
    N ≤ D.natDegree * supportCount V N + P.natDegree + D.natDegree + 1 := by
  classical
  obtain ⟨hm, hwindow⟩ := rational_tail_window_nonzero P D V hD0 hDV hproper
  let A := P.natDegree + 1
  let m := D.natDegree
  let q := (N - A) / m
  have hm' : 0 < m := hm
  have hchoose : ∀ k : Fin q, ∃ i : ℕ, i < m ∧
      PowerSeries.coeff (A + (k : ℕ) * m + i) V ≠ 0 := by
    intro k
    exact hwindow (A + (k : ℕ) * m) (by dsimp [A]; omega)
  choose i hi hcoeff using hchoose
  let f : Fin q → {n // n ∈ (Finset.range N).filter
      (fun n ↦ PowerSeries.coeff n V ≠ 0)} := fun k ↦
    ⟨A + (k : ℕ) * m + i k, by
      rw [Finset.mem_filter, Finset.mem_range]
      constructor
      · have hk : (k : ℕ) < q := k.isLt
        have hqmul : q * m ≤ N - A := by
          dsimp [q]
          exact Nat.div_mul_le_self (N - A) m
        have hkm : (k : ℕ) * m + i k < q * m := by
          have : ((k : ℕ) + 1) * m ≤ q * m :=
            Nat.mul_le_mul_right m (Nat.succ_le_iff.mpr hk)
          calc
            (k : ℕ) * m + i k < (k : ℕ) * m + m := Nat.add_lt_add_left (hi k) _
            _ = ((k : ℕ) + 1) * m := by rw [Nat.add_mul, one_mul]
            _ ≤ q * m := this
        have hAN : A + q * m ≤ N := by omega
        omega
      · exact hcoeff k⟩
  have hf : Function.Injective f := by
    intro k l hkl
    have heq : A + (k : ℕ) * m + i k = A + (l : ℕ) * m + i l :=
      congrArg Subtype.val hkl
    apply Fin.ext
    apply le_antisymm
    · by_contra hnot
      have hlk : (l : ℕ) < (k : ℕ) := Nat.lt_of_not_ge hnot
      have hsep : (l : ℕ) * m + i l < (k : ℕ) * m := by
        calc
          (l : ℕ) * m + i l < ((l : ℕ) + 1) * m := by
            rw [Nat.add_mul, one_mul]; exact Nat.add_lt_add_left (hi l) _
          _ ≤ (k : ℕ) * m := Nat.mul_le_mul_right m hlk
      omega
    · by_contra hnot
      have hkl' : (k : ℕ) < (l : ℕ) := Nat.lt_of_not_ge hnot
      have hsep : (k : ℕ) * m + i k < (l : ℕ) * m := by
        calc
          (k : ℕ) * m + i k < ((k : ℕ) + 1) * m := by
            rw [Nat.add_mul, one_mul]; exact Nat.add_lt_add_left (hi k) _
          _ ≤ (l : ℕ) * m := Nat.mul_le_mul_right m hkl'
      omega
  have hqcount : q ≤ supportCount V N := by
    simpa [q, supportCount] using Fintype.card_le_of_injective f hf
  have hdiv : N - A < (q + 1) * m := by
    exact (Nat.div_lt_iff_lt_mul hm').mp (Nat.lt_succ_self q)
  by_cases hNA : N ≤ A
  · dsimp [A, m] at hNA
    omega
  · have hA : A ≤ N := Nat.le_of_not_ge hNA
    have hN : N ≤ A + (q + 1) * m := by omega
    have hmul : m * q ≤ m * supportCount V N := Nat.mul_le_mul_left m hqcount
    calc
      N ≤ A + (q + 1) * m := hN
      _ = m * q + A + m := by rw [Nat.add_mul, one_mul, Nat.mul_comm q m]; omega
      _ ≤ m * supportCount V N + A + m := by
        simpa [Nat.add_assoc] using Nat.add_le_add_right hmul (A + m)
      _ = D.natDegree * supportCount V N + P.natDegree + D.natDegree + 1 := by
        dsimp [A, m]
        omega

/-- The support bound specialized to the rational multiplier `P / D`. -/
theorem rationalMultiple_one_supportCount_bound {K : Type*} [Field K]
    (P D : Polynomial K) (hD0 : D.coeff 0 ≠ 0)
    (hproper : ¬ D ∣ P) (N : ℕ) :
    N ≤ D.natDegree * supportCount (rationalMultiple P D 1) N +
      P.natDegree + D.natDegree + 1 := by
  apply rational_tail_supportCount_bound P D (rationalMultiple P D 1)
      hD0 _ hproper N
  simpa using rationalMultiple_denominator P D 1 hD0

end IndependentZeroBlocks
