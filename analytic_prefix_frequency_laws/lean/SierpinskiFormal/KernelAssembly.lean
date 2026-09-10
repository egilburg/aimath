import SierpinskiFormal.Lucas
import SierpinskiFormal.Assembly

/-!
# Modular weighted-kernel zero blocks

This theorem connects a whole-power-series dilation equation to arbitrarily
long zero blocks of every polynomially weighted convolution. The finite-field
pole-evaluation condition is explicit. It makes no claim about reduction from
characteristic zero or about existence of an appropriate splitting field.
-/

namespace SierpinskiFormal

open scoped BigOperators

/-- A normalized nonconstant kernel with a genuine high-digit gap kills every
polynomially weighted convolution at a pole whose normalized kernel evaluation
is zero or one. All scalar digit hypotheses are derived internally. -/
theorem weighted_zeroBlocks_of_kernel
    {K : Type*} [Field K] [Fintype K]
    (p : ℕ) [CharP K p] (hp : 0 < p)
    (A : Polynomial K) (T : PowerSeries K)
    (hApos : 0 < A.natDegree)
    (hAdegree : A.natDegree < Fintype.card K - 1)
    (hA0 : A.coeff 0 = 1)
    (hT0 : PowerSeries.coeff 0 T = 1)
    (hT : T = (A : PowerSeries K) * dilate (Fintype.card K) T)
    (gamma : K) (hgamma : gamma ≠ 0)
    (heval : A.eval gamma = 0 ∨ A.eval gamma = 1)
    (P : Polynomial K) :
    HasArbitrarilyLongZeroBlocks
      (Convolution.weighted P (fun n => PowerSeries.coeff n T * gamma ^ n)) := by
  let q := Fintype.card K
  let v := fun n => PowerSeries.coeff n T * gamma ^ n
  have hq : 2 ≤ q := Fintype.one_lt_card
  have hqpos : 0 < q := by omega
  have hAdegreeq : A.natDegree < q := by dsimp [q]; omega
  have hcoeff (i : ℕ) (hi : i < q) : PowerSeries.coeff i T = A.coeff i :=
    low_coeff_of_dilation_equation q hqpos A hAdegreeq T hT hT0 i hi
  obtain ⟨d, hdpos, hdq, hdne, hdprior⟩ :=
    exists_first_nonzero_kernel_digit A q hApos hAdegreeq
  have hv0 : v 0 = 1 := by
    dsimp [v]
    rw [hcoeff 0 hqpos, hA0, pow_zero, mul_one]
  have hvlucas : ∀ m a, a < q → v (q * m + a) = v m * v a := by
    exact Convolution.twist_lucas (fun n => PowerSeries.coeff n T) q gamma
      (FiniteField.pow_card gamma)
      (lucas_of_dilation_equation q hqpos A hAdegreeq T hT hT0)
  have hsum : (∑ j ∈ Finset.range q, v j) = A.eval gamma := by
    rw [Polynomial.eval_eq_sum_range' hAdegreeq]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [v]
    rw [hcoeff j (Finset.mem_range.mp hj)]
  have hvd : v d ≠ 0 := by
    dsimp [v]
    rw [hcoeff d hdq]
    exact mul_ne_zero hdne (pow_ne_zero d hgamma)
  have hlow : (∑ j ∈ Finset.range (d + 1), v j) = 1 + v d := by
    apply Convolution.first_digit_prefix v d hdpos hv0
    intro j hjpos hjlt
    dsimp [v]
    rw [hcoeff j (lt_trans hjlt hdq), hdprior j hjpos hjlt, zero_mul]
  have heq : q - 1 + 1 = q := by omega
  have he : q - 1 < q := by omega
  have hepos : 0 < q - 1 := by omega
  have hve : v (q - 1) = 0 := by
    dsimp [v]
    rw [high_digit_zero_of_dilation_equation q hqpos A hAdegreeq T hT hT0
      (q - 1) he hAdegree, zero_mul]
  apply weighted_zeroBlocks_of_lucas p q d (q - 1) hp hq
    (FiniteField.cast_card_eq_zero K) v P hv0 hvlucas hdq he hepos
  · simpa only [hsum] using heval
  · intro _
    exact FiniteField.pow_card_sub_one_eq_one (v d) hvd
  · exact hlow
  · rw [heq]
  · exact hve

/-- One seed, selected from the kernel alone, works simultaneously for every
admissible pole parameter and every polynomial weight. Its scalar-kernel
descendants vanish too, so the same intervals can accommodate polynomial parts
and finite sums of pole contributions. -/
theorem exists_common_kernel_seed
    {K : Type*} [Field K] [Fintype K]
    (p : ℕ) [CharP K p] (hp : 0 < p)
    (A : Polynomial K) (T : PowerSeries K)
    (hApos : 0 < A.natDegree)
    (hAdegree : A.natDegree < Fintype.card K - 1)
    (hA0 : A.coeff 0 = 1)
    (hT0 : PowerSeries.coeff 0 T = 1)
    (hT : T = (A : PowerSeries K) * dilate (Fintype.card K) T) :
    ∃ seed, 1 ≤ seed ∧
      (∀ E j, j < Fintype.card K ^ E →
        PowerSeries.coeff (seed * Fintype.card K ^ E + j) T = 0) ∧
      ∀ gamma : K, gamma ≠ 0 → (A.eval gamma = 0 ∨ A.eval gamma = 1) →
        ∀ P : Polynomial K, ∀ E, 1 ≤ E → ∀ j, j < Fintype.card K ^ E →
          Convolution.weighted P (fun n => PowerSeries.coeff n T * gamma ^ n)
            (seed * Fintype.card K ^ E + j) = 0 := by
  let q := Fintype.card K
  have hq : 2 ≤ q := Fintype.one_lt_card
  have hqpos : 0 < q := by omega
  have hqzero : (q : K) = 0 := FiniteField.cast_card_eq_zero K
  have hAdegreeq : A.natDegree < q := by dsimp [q]; omega
  have hcoeff (i : ℕ) (hi : i < q) : PowerSeries.coeff i T = A.coeff i :=
    low_coeff_of_dilation_equation q hqpos A hAdegreeq T hT hT0 i hi
  have hlucas : ∀ m a, a < q →
      PowerSeries.coeff (q * m + a) T =
        PowerSeries.coeff m T * PowerSeries.coeff a T :=
    lucas_of_dilation_equation q hqpos A hAdegreeq T hT hT0
  obtain ⟨d, hdpos, hdq, hdne, hdprior⟩ :=
    exists_first_nonzero_kernel_digit A q hApos hAdegreeq
  let seed := q * DigitState.lowIndex q d (DigitState.extensionLength p q) + (q - 1)
  have he : q - 1 < q := by omega
  have heq : q - 1 + 1 = q := by omega
  have hte : PowerSeries.coeff (q - 1) T = 0 :=
    high_digit_zero_of_dilation_equation q hqpos A hAdegreeq T hT hT0
      (q - 1) he hAdegree
  have hseedt : PowerSeries.coeff seed T = 0 := by
    dsimp [seed]
    rw [hlucas _ _ he, hte, mul_zero]
  refine ⟨seed, by dsimp [seed]; omega, ?_, ?_⟩
  · apply zero_on_descendants_of_append
      (f := fun n => PowerSeries.coeff n T) (seed := seed) hq hseedt
    intro n a ha hn
    rw [hlucas n a ha, hn, zero_mul]
  · intro gamma hgamma heval P
    let v := fun n => PowerSeries.coeff n T * gamma ^ n
    have hv0 : v 0 = 1 := by
      dsimp [v]
      rw [hcoeff 0 hqpos, hA0, pow_zero, mul_one]
    have hvlucas : ∀ m a, a < q → v (q * m + a) = v m * v a :=
      Convolution.twist_lucas (fun n => PowerSeries.coeff n T) q gamma
        (FiniteField.pow_card gamma) hlucas
    have hsum : (∑ j ∈ Finset.range q, v j) = A.eval gamma := by
      rw [Polynomial.eval_eq_sum_range' hAdegreeq]
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [v]
      rw [hcoeff j (Finset.mem_range.mp hj)]
    have hvd : v d ≠ 0 := by
      dsimp [v]
      rw [hcoeff d hdq]
      exact mul_ne_zero hdne (pow_ne_zero d hgamma)
    have hlow : (∑ j ∈ Finset.range (d + 1), v j) = 1 + v d := by
      apply Convolution.first_digit_prefix v d hdpos hv0
      intro j hjpos hjlt
      dsimp [v]
      rw [hcoeff j (lt_trans hjlt hdq), hdprior j hjpos hjlt, zero_mul]
    have hve : v (q - 1) = 0 := by dsimp [v]; rw [hte, zero_mul]
    have hs0 : prefixState v 0 = (1, 1) := by simp [prefixState, hv0]
    have hseedv : prefixState v seed = (0, 0) := by
      apply DigitState.sequence_extension_seed p q d (q - 1) hp (by omega)
        (∑ j ∈ Finset.range q, v j) (v d)
        (fun a => ∑ j ∈ Finset.range (a + 1), v j) v (prefixState v)
        hdq he hs0 (prefixState_transition v q hqzero hvlucas)
      · simpa only [hsum] using heval
      · intro _
        exact FiniteField.pow_card_sub_one_eq_one (v d) hvd
      · exact hlow
      · rfl
      · rw [heq]
      · exact hve
    exact weighted_zero_on_seed_descendants q seed hq hqzero v P hvlucas hseedv

/-- Direct fractional-power version of the simultaneous modular theorem.
Frobenius, the kernel degree bound, Lucas identities, and all digit-state
conditions are proved from the displayed branch hypotheses. -/
theorem exists_common_seed_of_branch
    {K : Type*} [Field K] [Fintype K]
    (p : ℕ) [CharP K p] (hp : 0 < p)
    (D : Polynomial K) (T : PowerSeries K) (a b s : ℕ)
    (ha : 0 < a) (hs : 0 < s)
    (hq : Fintype.card K = b * s + 1)
    (hDpos : 0 < D.natDegree) (hgap : a * D.natDegree < b)
    (hD0 : D.coeff 0 = 1)
    (hT0 : PowerSeries.coeff 0 T = 1)
    (hbranch : (D : PowerSeries K) ^ a * T ^ b = 1) :
    ∃ seed, 1 ≤ seed ∧
      (∀ E j, j < Fintype.card K ^ E →
        PowerSeries.coeff (seed * Fintype.card K ^ E + j) T = 0) ∧
      ∀ gamma : K, gamma ≠ 0 →
        ((D ^ (a * s)).eval gamma = 0 ∨ (D ^ (a * s)).eval gamma = 1) →
        ∀ P : Polynomial K, ∀ E, 1 ≤ E → ∀ j, j < Fintype.card K ^ E →
          Convolution.weighted P (fun n => PowerSeries.coeff n T * gamma ^ n)
            (seed * Fintype.card K ^ E + j) = 0 := by
  have hApos : 0 < (D ^ (a * s)).natDegree := by
    rw [Polynomial.natDegree_pow]
    exact Nat.mul_pos (Nat.mul_pos ha hs) hDpos
  have hAdegree : (D ^ (a * s)).natDegree < Fintype.card K - 1 :=
    kernel_degree_lt_pred_base D a b s (Fintype.card K) hs hq hgap
  have hA0 : (D ^ (a * s)).coeff 0 = 1 := by
    rw [← Polynomial.constantCoeff_coe, Polynomial.coe_pow, map_pow,
      Polynomial.constantCoeff_coe, hD0, one_pow]
  exact exists_common_kernel_seed p hp (D ^ (a * s)) T hApos hAdegree hA0 hT0
    (finiteField_dilation_equation D T a b s hq hbranch)

end SierpinskiFormal

#print axioms SierpinskiFormal.weighted_zeroBlocks_of_kernel
#print axioms SierpinskiFormal.exists_common_kernel_seed
#print axioms SierpinskiFormal.exists_common_seed_of_branch
