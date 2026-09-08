import SierpinskiFormal.RationalDensityCriterion

set_option autoImplicit false

namespace IndependentZeroBlocks

/-- Multiplication preserves agreement of all coefficients below a cutoff. -/
theorem coeff_mul_congr_below
    {K : Type*} [CommRing K] (T F G : PowerSeries K) (N : ℕ)
    (h : ∀ n, n < N → PowerSeries.coeff n F = PowerSeries.coeff n G) :
    ∀ n, n < N → PowerSeries.coeff n (T * F) = PowerSeries.coeff n (T * G) := by
  intro n hn
  simp only [PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro ij hij
  have hs : ij.1 + ij.2 = n := Finset.mem_antidiagonal.mp hij
  rw [h ij.2 (by omega)]

/-- Regular rational division preserves a numerator's coefficient agreement
with a polynomial below a cutoff. -/
theorem coeff_rationalMultiple_eq_of_numerator_below
    {K : Type*} [Field K] (P D Q : Polynomial K) (F : PowerSeries K) (N : ℕ)
    (h : ∀ n, n < N → PowerSeries.coeff n ((P : PowerSeries K) * F) = Q.coeff n) :
    ∀ n, n < N →
      PowerSeries.coeff n (rationalMultiple P D F) =
        PowerSeries.coeff n (rationalMultiple Q D 1) := by
  have hnum : ∀ n, n < N →
      PowerSeries.coeff n ((P : PowerSeries K) * F) =
        PowerSeries.coeff n (Q : PowerSeries K) := by
    simpa only [Polynomial.coeff_coe] using h
  have hm := coeff_mul_congr_below ((D : PowerSeries K)⁻¹)
    ((P : PowerSeries K) * F) (Q : PowerSeries K) N hnum
  intro n hn
  convert hm n hn using 1 <;> congr 1 <;> unfold rationalMultiple <;> ring

/-- A nonabsorbed polynomial prefix with a forcing-free interval gives a
support lower bound for the full rationally filtered series. -/
theorem rational_prefix_gap_support_bound
    {K : Type*} [Field K] (P D Q : Polynomial K) (F : PowerSeries K)
    (hD0 : D.coeff 0 ≠ 0) (hproper : ¬D ∣ Q)
    (g L M : ℕ) (hdegree : Q.natDegree < g + P.natDegree)
    (hM : g + L ≤ M)
    (hcoeff : ∀ n, n < g + L →
      PowerSeries.coeff n ((P : PowerSeries K) * F) = Q.coeff n) :
    L ≤ D.natDegree * supportCount (rationalMultiple P D F) M +
      P.natDegree + D.natDegree := by
  have hcount := supportCount_congr_below (g + L)
    (coeff_rationalMultiple_eq_of_numerator_below P D Q F (g + L) hcoeff)
  have hr := rationalMultiple_one_supportCount_bound Q D hD0 hproper (g + L)
  rw [← hcount] at hr
  have hmono := Nat.mul_le_mul_left D.natDegree
    (supportCount_mono (rationalMultiple P D F) hM)
  omega

/-- Shifting the radix cutoffs only changes the constants in a positive
lower-density estimate. -/
theorem positiveLowerSupportDensity_of_shifted_radix_bound
    {K : Type*} [Semiring K] (F : PowerSeries K) (b E d B : ℕ)
    (hb : 2 ≤ b) (hd : 0 < d)
    (hbound : ∀ e, b ^ e ≤ d * supportCount F (b ^ (e + E)) + B) :
    HasPositiveLowerSupportDensity F := by
  have hpow (e : ℕ) :
      b ^ e ≤ (b ^ E * d) * supportCount F (b ^ e) + b ^ E * (B + 1) := by
    by_cases he : E ≤ e
    · have h := Nat.mul_le_mul_left (b ^ E) (hbound (e - E))
      have heq : e - E + E = e := Nat.sub_add_cancel he
      have heq' : E + (e - E) = e := Nat.add_sub_of_le he
      rw [← pow_add, heq', heq, Nat.mul_add] at h
      calc
        b ^ e ≤ b ^ E * (d * supportCount F (b ^ e)) + b ^ E * B := h
        _ ≤ b ^ E * (d * supportCount F (b ^ e)) + b ^ E * (B + 1) := by gcongr; omega
        _ = _ := by ring
    · have hp : b ^ e ≤ b ^ E := Nat.pow_le_pow_right (by omega) (by omega)
      have hbB : b ^ E ≤ b ^ E * (B + 1) := Nat.le_mul_of_pos_right _ (by omega)
      omega
  apply hasPositiveLowerSupportDensity_of_powers F b hb 1
    (b ^ E * d : ℕ) (b ^ E * (B + 1) : ℕ)
  · norm_num
  · exact_mod_cast Nat.mul_pos (pow_pos (by omega) E) hd
  · intro e
    simpa using (show ((b ^ e : ℕ) : ℝ) ≤
      ((b ^ E * d : ℕ) : ℝ) * (supportCount F (b ^ e) : ℝ) +
      ((b ^ E * (B + 1) : ℕ) : ℝ) by exact_mod_cast hpow e)

end IndependentZeroBlocks
