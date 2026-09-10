import SierpinskiFormal.CanonicalSeries
import SierpinskiFormal.SeedBlocks
import SierpinskiFormal.RootSupportedDenominator
import Mathlib.Algebra.Polynomial.BigOperators

open scoped BigOperators
open SierpinskiFormal

set_option autoImplicit false

/-! Finite polynomial prefixes of the canonical digit-product series. -/
namespace IndependentZeroBlocks
variable {R : Type*} [CommRing R]

theorem dilate_add (q : ℕ) (S T : PowerSeries R) :
    dilate q (S + T) = dilate q S + dilate q T := by
  ext n
  simp only [coeff_dilate, map_add]
  split_ifs <;> simp

theorem dilate_C_mul (q : ℕ) (a : R) (T : PowerSeries R) :
    dilate q (PowerSeries.C a * T) =
      PowerSeries.C a * dilate q T := by
  ext n
  simp [coeff_dilate, PowerSeries.coeff_C_mul]

theorem dilate_X_pow_mul (q : ℕ) (hq : 0 < q) (n : ℕ) (T : PowerSeries R) :
    dilate q (PowerSeries.X ^ n * T) =
      PowerSeries.X ^ (q * n) * dilate q T := by
  ext k
  simp only [coeff_dilate, PowerSeries.coeff_X_pow_mul']
  by_cases hqk : q ∣ k
  · obtain ⟨l, rfl⟩ := hqk
    simp only [dvd_mul_right, if_true]
    rw [Nat.mul_div_cancel_left l hq]
    by_cases hnl : n ≤ l
    · have hqn : q * n ≤ q * l := Nat.mul_le_mul_left q hnl
      rw [if_pos hnl, if_pos hqn]
      have hsub : q * l - q * n = q * (l - n) := (Nat.mul_sub_left_distrib q l n).symm
      rw [hsub, if_pos (dvd_mul_right q (l - n)), Nat.mul_div_cancel_left _ hq]
    · have hqn : ¬ q * n ≤ q * l := by
        intro h
        exact hnl (Nat.le_of_mul_le_mul_left h hq)
      rw [if_neg hnl, if_neg hqn]
  · rw [if_neg hqk]
    by_cases hqnk : q * n ≤ k
    · rw [if_pos hqnk]
      have hnot : ¬ q ∣ k - q * n := by
        intro h
        have hqn' : q ∣ q * n := dvd_mul_right q n
        have : q ∣ k := by
          rw [← Nat.sub_add_cancel hqnk]
          exact dvd_add h hqn'
        exact hqk this
      rw [if_neg hnot]
    · rw [if_neg hqnk]

theorem coe_monomial_mul (n : ℕ) (a : R) (T : PowerSeries R) :
    (↑(Polynomial.monomial n a) : PowerSeries R) * T =
      PowerSeries.C a * (PowerSeries.X ^ n * T) := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coe_mul,
    Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X, mul_assoc]

theorem dilate_polynomial_mul (q : ℕ) (hq : 0 < q)
    (P : Polynomial R) (T : PowerSeries R) :
    dilate q ((P : PowerSeries R) * T) =
      (Polynomial.expand R q P : PowerSeries R) * dilate q T := by
  induction P using Polynomial.induction_on' with
  | add P Q ihP ihQ =>
      rw [Polynomial.coe_add, add_mul, dilate_add, ihP, ihQ, map_add,
        Polynomial.coe_add, add_mul]
  | monomial n a =>
      rw [coe_monomial_mul, dilate_C_mul, dilate_X_pow_mul q hq,
        Polynomial.expand_monomial, coe_monomial_mul]
      rw [Nat.mul_comm n q]



theorem dilate_one (T : PowerSeries R) : dilate 1 T = T := by
  ext n
  simp [coeff_dilate]

theorem dilate_dilate (q r : ℕ) (T : PowerSeries R) :
    dilate q (dilate r T) = dilate (q * r) T := by
  ext n
  simp only [coeff_dilate]
  by_cases hqn : q ∣ n
  · rw [if_pos hqn]
    have hiff : r ∣ n / q ↔ q * r ∣ n := Nat.dvd_div_iff_mul_dvd hqn
    by_cases hrn : r ∣ n / q
    · rw [if_pos hrn, if_pos (hiff.mp hrn), Nat.div_div_eq_div_mul]
    · rw [if_neg hrn, if_neg (mt hiff.mpr hrn)]
  · rw [if_neg hqn]
    have hnot : ¬ q * r ∣ n := by
      intro h
      exact hqn ((dvd_mul_right q r).trans h)
    rw [if_neg hnot]

noncomputable def kernelPrefix (b : ℕ) (A : Polynomial R) (e : ℕ) : Polynomial R :=
  ∏ j ∈ Finset.range e, Polynomial.expand R (b ^ j) A

theorem canonicalSeries_eq_kernelPrefix_mul_dilate
    (b : ℕ) (hb : 2 ≤ b) (A : Polynomial R) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b) (e : ℕ) :
    IndependentZeroBlocks.canonicalSeries b A =
      (kernelPrefix b A e : PowerSeries R) *
        dilate (b ^ e) (IndependentZeroBlocks.canonicalSeries b A) := by
  let T := IndependentZeroBlocks.canonicalSeries b A
  have hT : T = (A : PowerSeries R) * dilate b T :=
    IndependentZeroBlocks.canonicalSeries_dilation_equation b hb A hA0 hdegree
  induction e with
  | zero => simp [kernelPrefix, T, dilate_one]
  | succ e ih =>
      calc
        T = (kernelPrefix b A e : PowerSeries R) * dilate (b ^ e) T := ih
        _ = (kernelPrefix b A e : PowerSeries R) *
            dilate (b ^ e) ((A : PowerSeries R) * dilate b T) := by rw [← hT]
        _ = (kernelPrefix b A e : PowerSeries R) *
            ((Polynomial.expand R (b ^ e) A : PowerSeries R) *
              dilate (b ^ e) (dilate b T)) := by
                rw [dilate_polynomial_mul (b ^ e) (pow_pos (by omega) e)]
        _ = (kernelPrefix b A (e + 1) : PowerSeries R) *
            dilate (b ^ (e + 1)) T := by
              rw [dilate_dilate (b ^ e) b]
              simp only [kernelPrefix, Finset.prod_range_succ, Polynomial.coe_mul,
                pow_succ]
              ring


theorem kernelPrefix_natDegree_bound
    (b : ℕ) (hb : 2 ≤ b) (A : Polynomial R) (e : ℕ) :
    (b - 1) * (kernelPrefix b A e).natDegree ≤
      A.natDegree * (b ^ e - 1) := by
  have hdeg : (kernelPrefix b A e).natDegree ≤
      ∑ j ∈ Finset.range e, A.natDegree * b ^ j := by
    exact (Polynomial.natDegree_prod_le (Finset.range e)
      (fun j => Polynomial.expand R (b ^ j) A)).trans_eq (by
        simp only [Polynomial.natDegree_expand])
  have hgeom : (∑ j ∈ Finset.range e, b ^ j) * (b - 1) = b ^ e - 1 := by
    have h := geom_sum_mul_add (b - 1) e
    rw [show b - 1 + 1 = b by omega] at h
    omega
  calc
    (b - 1) * (kernelPrefix b A e).natDegree ≤
        (b - 1) * (∑ j ∈ Finset.range e, A.natDegree * b ^ j) :=
      Nat.mul_le_mul_left (b - 1) hdeg
    _ = A.natDegree * (b ^ e - 1) := by
      rw [← Finset.mul_sum]
      rw [← hgeom]
      ring

theorem kernelPrefix_natDegree_le_mul_pow
    (b : ℕ) (hb : 2 ≤ b) (A : Polynomial R) (e : ℕ) :
    (b - 1) * (kernelPrefix b A e).natDegree ≤ A.natDegree * b ^ e :=
  (kernelPrefix_natDegree_bound b hb A e).trans
    (Nat.mul_le_mul_left A.natDegree (Nat.sub_le _ _))

theorem kernelPrefix_natDegree_lt_pow
    (b : ℕ) (hb : 2 ≤ b) (A : Polynomial R)
    (hdegree : A.natDegree < b - 1) (e : ℕ) :
    (kernelPrefix b A e).natDegree < b ^ e := by
  have h := kernelPrefix_natDegree_le_mul_pow b hb A e
  have hstrict : A.natDegree * b ^ e < (b - 1) * b ^ e :=
    Nat.mul_lt_mul_of_pos_right hdegree (pow_pos (by omega) e)
  exact Nat.lt_of_mul_lt_mul_left (h.trans_lt hstrict)


theorem coeff_mul_dilate_of_lt (q : ℕ)
    (U T : PowerSeries R) (hT0 : PowerSeries.coeff 0 T = 1)
    (n : ℕ) (hn : n < q) :
    PowerSeries.coeff n (U * dilate q T) = PowerSeries.coeff n U := by
  rw [PowerSeries.coeff_mul]
  rw [Finset.sum_eq_single (n, 0)]
  · simp [coeff_dilate, hT0]
  · intro ij hij hne
    have hsum : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
    by_cases hdiv : q ∣ ij.2
    · have hjzero : ij.2 = 0 := by
        obtain ⟨k, hk⟩ := hdiv
        by_cases hkzero : k = 0
        · simp [hk, hkzero]
        · have : q ≤ ij.2 := by
            rw [hk]
            exact Nat.le_mul_of_pos_right q (Nat.pos_of_ne_zero hkzero)
          omega
      have hizero : ij.1 = n := by omega
      exact False.elim (hne (Prod.ext hizero hjzero))
    · simp [coeff_dilate, hdiv]
  · intro hnot
    exact False.elim (hnot (Finset.mem_antidiagonal.mpr (Nat.add_zero n)))


theorem rationalMultiple_kernelPrefix_factorization
    {K : Type*} [Field K]
    (b : ℕ) (hb : 2 ≤ b) (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b) (e : ℕ) (P D : Polynomial K) :
    IndependentZeroBlocks.rationalMultiple P D
        (IndependentZeroBlocks.canonicalSeries b A) =
      IndependentZeroBlocks.rationalMultiple (P * kernelPrefix b A e) D 1 *
        dilate (b ^ e) (IndependentZeroBlocks.canonicalSeries b A) := by
  nth_rw 1 [canonicalSeries_eq_kernelPrefix_mul_dilate b hb A hA0 hdegree e]
  unfold IndependentZeroBlocks.rationalMultiple
  simp only [Polynomial.coe_mul]
  ring

theorem coeff_rationalMultiple_eq_prefix
    {K : Type*} [Field K]
    (b : ℕ) (hb : 2 ≤ b) (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b) (e : ℕ) (P D : Polynomial K)
    (_hD0 : D.coeff 0 ≠ 0) (n : ℕ) (hn : n < b ^ e) :
    PowerSeries.coeff n
        (IndependentZeroBlocks.rationalMultiple P D
          (IndependentZeroBlocks.canonicalSeries b A)) =
      PowerSeries.coeff n
        (IndependentZeroBlocks.rationalMultiple (P * kernelPrefix b A e) D 1) := by
  rw [rationalMultiple_kernelPrefix_factorization b hb A hA0 hdegree e P D]
  exact coeff_mul_dilate_of_lt (b ^ e) _ _ (by simp) n hn

theorem rationalMultiple_eq_polynomial_mul_dilate_of_dvd
    {K : Type*} [Field K]
    (b : ℕ) (hb : 2 ≤ b) (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b) (e : ℕ) (P D : Polynomial K)
    (hD0 : D.coeff 0 ≠ 0) (hdiv : D ∣ P * kernelPrefix b A e) :
    ∃ H : Polynomial K,
      IndependentZeroBlocks.rationalMultiple P D
          (IndependentZeroBlocks.canonicalSeries b A) =
        (H : PowerSeries K) *
          dilate (b ^ e) (IndependentZeroBlocks.canonicalSeries b A) := by
  obtain ⟨H, hH⟩ := hdiv
  refine ⟨H, ?_⟩
  apply Eq.symm
  apply IndependentZeroBlocks.eq_rationalMultiple_of_denominator P D
    (IndependentZeroBlocks.canonicalSeries b A)
    ((H : PowerSeries K) *
      dilate (b ^ e) (IndependentZeroBlocks.canonicalSeries b A)) hD0
  nth_rw 2 [canonicalSeries_eq_kernelPrefix_mul_dilate b hb A hA0 hdegree e]
  have hHps := congrArg (fun Q : Polynomial K => (Q : PowerSeries K)) hH
  simp only [Polynomial.coe_mul] at hHps ⊢
  calc
    (D : PowerSeries K) * ((H : PowerSeries K) *
        dilate (b ^ e) (IndependentZeroBlocks.canonicalSeries b A)) =
      ((D : PowerSeries K) * (H : PowerSeries K)) *
        dilate (b ^ e) (IndependentZeroBlocks.canonicalSeries b A) := by ring
    _ = ((P : PowerSeries K) * (kernelPrefix b A e : PowerSeries K)) *
        dilate (b ^ e) (IndependentZeroBlocks.canonicalSeries b A) := by rw [hHps]
    _ = (P : PowerSeries K) * ((kernelPrefix b A e : PowerSeries K) *
        dilate (b ^ e) (IndependentZeroBlocks.canonicalSeries b A)) := by ring


theorem expand_card_pow_eq_pow
    {K : Type*} [Field K] [Fintype K]
    (A : Polynomial K) (e : ℕ) :
    Polynomial.expand K ((Fintype.card K) ^ e) A =
      A ^ ((Fintype.card K) ^ e) := by
  induction e generalizing A with
  | zero => simp
  | succ e ih =>
      rw [pow_succ, Polynomial.expand_mul, ih, FiniteField.expand_card, ← pow_mul]
      congr 1
      exact Nat.mul_comm _ _

theorem kernelPrefix_card_eq_pow_geomSum
    {K : Type*} [Field K] [Fintype K]
    (A : Polynomial K) (e : ℕ) :
    kernelPrefix (Fintype.card K) A e =
      A ^ (∑ j ∈ Finset.range e, (Fintype.card K) ^ j) := by
  unfold kernelPrefix
  simp_rw [expand_card_pow_eq_pow]
  exact Finset.prod_pow_eq_pow_sum (Finset.range e) _ A

end IndependentZeroBlocks
