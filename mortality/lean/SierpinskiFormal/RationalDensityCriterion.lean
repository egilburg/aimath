import SierpinskiFormal.SupportCounting
import SierpinskiFormal.ProductPrefixes
import SierpinskiFormal.RationalTailDensity
import SierpinskiFormal.SupportDensityBounds

set_option autoImplicit false

/-!
# Exact support-density classification for rationally filtered digit products

The field and the radix are independent. The canonical series is constructed,
not supplied as an existence assumption. All cancellation is retained in P.
-/
namespace IndependentZeroBlocks

/-- If no finite prefix absorbs the denominator, the rational-tail obstruction
forces a uniform lower count at every power of the radix. -/
theorem digitProduct_rational_supportCount_pow_lower
    {K : Type*} [Field K]
    (b : ℕ) (hb : 2 ≤ b) (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b - 1) (P D : Polynomial K)
    (hD0 : D.coeff 0 ≠ 0)
    (hnot : ∀ e : ℕ, ¬ D ∣ P * kernelPrefix b A e) (e : ℕ) :
    (b - 1 - A.natDegree) * b ^ e ≤
      ((b - 1) * D.natDegree) *
        supportCount (rationalMultiple P D (canonicalSeries b A)) (b ^ e) +
      (b - 1) * (P.natDegree + D.natDegree + 1) := by
  have hc := supportCount_congr_below (b ^ e)
    (coeff_rationalMultiple_eq_prefix b hb A hA0 (by omega) e P D hD0)
  have ht := rationalMultiple_one_supportCount_bound
    (P * kernelPrefix b A e) D hD0 (hnot e) (b ^ e)
  rw [← hc] at ht
  have hd := kernelPrefix_natDegree_le_mul_pow b hb A e
  have hp : (P * kernelPrefix b A e).natDegree ≤
      P.natDegree + (kernelPrefix b A e).natDegree := Polynomial.natDegree_mul_le
  have hs : (b - 1 - A.natDegree) + A.natDegree = b - 1 :=
    Nat.sub_add_cancel hdegree.le
  nlinarith [congrArg (fun n : ℕ => n * b ^ e) hs,
    Nat.mul_le_mul_left (b - 1) ht,
    Nat.mul_le_mul_left (b - 1) hp]

private theorem denominator_degree_pos_of_no_prefix
    {K : Type*} [Field K] (b : ℕ) (A P D : Polynomial K)
    (hD0 : D.coeff 0 ≠ 0)
    (hnot : ∀ e : ℕ, ¬ D ∣ P * kernelPrefix b A e) : 0 < D.natDegree := by
  have hproper : ¬ D ∣ P := by simpa [kernelPrefix] using hnot 0
  exact (rational_tail_window_nonzero P D (rationalMultiple P D 1) hD0
    (by simpa using rationalMultiple_denominator P D 1 hD0) hproper).1

/-- Outside the absorption locus the lower density is strictly positive.
This does not assume that an ordinary density exists. -/
theorem digitProduct_rational_positive_lower_density
    {K : Type*} [Field K]
    (b : ℕ) (hb : 2 ≤ b) (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b - 1) (P D : Polynomial K)
    (hD0 : D.coeff 0 ≠ 0)
    (hnot : ∀ e : ℕ, ¬ D ∣ P * kernelPrefix b A e) :
    HasPositiveLowerSupportDensity (rationalMultiple P D (canonicalSeries b A)) := by
  have hm := denominator_degree_pos_of_no_prefix b A P D hD0 hnot
  apply hasPositiveLowerSupportDensity_of_powers _ b hb
    (b - 1 - A.natDegree : ℕ) ((b - 1) * D.natDegree : ℕ)
    ((b - 1) * (P.natDegree + D.natDegree + 1) : ℕ)
  · exact_mod_cast (show 0 < b - 1 - A.natDegree by omega)
  · exact_mod_cast Nat.mul_pos (show 0 < b - 1 by omega) hm
  · intro e
    exact_mod_cast digitProduct_rational_supportCount_pow_lower b hb A hA0 hdegree
      P D hD0 hnot e

/-- Explicit lower-limit bound outside the absorption locus. The constant is
equivalently `(1 - deg A / (b-1)) / (b * deg D)`. -/
theorem digitProduct_rational_density_lower_bound
    {K : Type*} [Field K]
    (b : ℕ) (hb : 2 ≤ b) (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b - 1) (P D : Polynomial K)
    (hD0 : D.coeff 0 ≠ 0)
    (hnot : ∀ e : ℕ, ¬ D ∣ P * kernelPrefix b A e) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (b - 1 - A.natDegree : ℕ) / ((b : ℝ) * ((b - 1) * D.natDegree : ℕ)) - ε ≤
        (supportCount (rationalMultiple P D (canonicalSeries b A)) N : ℝ) / (N : ℝ) := by
  have hm := denominator_degree_pos_of_no_prefix b A P D hD0 hnot
  apply supportDensity_eventually_lower_of_powers _ b hb
    (b - 1 - A.natDegree : ℕ) ((b - 1) * D.natDegree : ℕ)
    ((b - 1) * (P.natDegree + D.natDegree + 1) : ℕ)
  · positivity
  · exact_mod_cast Nat.mul_pos (show 0 < b - 1 by omega) hm
  · intro e
    exact_mod_cast digitProduct_rational_supportCount_pow_lower b hb A hA0 hdegree
      P D hD0 hnot e

/-- Exact classification over every field and every independent radix:
density zero is precisely finite polynomial-prefix absorption. -/
theorem digitProduct_rational_density_zero_iff
    {K : Type*} [Field K]
    (b : ℕ) (hb : 2 ≤ b) (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b - 1) (P D : Polynomial K)
    (hD0 : D.coeff 0 ≠ 0) :
    HasZeroSupportDensity (rationalMultiple P D (canonicalSeries b A)) ↔
      ∃ e : ℕ, D ∣ P * kernelPrefix b A e := by
  constructor
  · intro hz
    by_contra h
    push_neg at h
    exact (digitProduct_rational_positive_lower_density b hb A hA0 hdegree P D hD0 h).not_zero hz
  · rintro ⟨e, hdiv⟩
    obtain ⟨H, hH⟩ := rationalMultiple_eq_polynomial_mul_dilate_of_dvd
      b hb A hA0 (by omega) e P D hD0 hdiv
    rw [hH]
    exact hasZeroSupportDensity_polynomial_mul_dilate_canonicalSeries b hb A H hA0 hdegree e

theorem digitProduct_rational_positive_lower_density_iff
    {K : Type*} [Field K]
    (b : ℕ) (hb : 2 ≤ b) (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b - 1) (P D : Polynomial K)
    (hD0 : D.coeff 0 ≠ 0) :
    HasPositiveLowerSupportDensity (rationalMultiple P D (canonicalSeries b A)) ↔
      ∀ e : ℕ, ¬ D ∣ P * kernelPrefix b A e := by
  constructor
  · intro hp e he
    exact hp.not_zero ((digitProduct_rational_density_zero_iff b hb A hA0 hdegree P D hD0).2 ⟨e, he⟩)
  · exact digitProduct_rational_positive_lower_density b hb A hA0 hdegree P D hD0

/-- The same criterion for any normalized solution of the dilation equation. -/
theorem dilation_rational_density_zero_iff
    {K : Type*} [Field K]
    (b : ℕ) (hb : 2 ≤ b) (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < b - 1) (F : PowerSeries K)
    (hF0 : PowerSeries.coeff 0 F = 1)
    (hF : F = (A : PowerSeries K) * SierpinskiFormal.dilate b F)
    (P D : Polynomial K) (hD0 : D.coeff 0 ≠ 0) :
    HasZeroSupportDensity (rationalMultiple P D F) ↔
      ∃ e : ℕ, D ∣ P * kernelPrefix b A e := by
  rw [eq_canonicalSeries_of_dilation_equation b hb A hA0 (by omega) F hF0 hF]
  exact digitProduct_rational_density_zero_iff b hb A hA0 hdegree P D hD0

end IndependentZeroBlocks
