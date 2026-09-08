import SierpinskiFormal.KernelAssembly

set_option autoImplicit false

/-!
# Explicit common seeds for kernels with a shared first digit

The seed in this file is determined only by the characteristic, the cardinality
of the finite field, and a supplied first positive kernel digit.  In particular,
the same seed applies pointwise to an arbitrarily indexed family of kernels with
that shared digit; no finiteness assumption on the index type is needed.
-/

namespace SierpinskiFormal

open scoped BigOperators

/-- The index whose base-`q` digits are
`DigitState.extensionLength p q` copies of `d`, followed by `q - 1`. -/
def commonSeed (p q d : ℕ) : ℕ :=
  q * DigitState.lowIndex q d (DigitState.extensionLength p q) + (q - 1)

/-- A supplied first positive kernel digit gives an explicit seed which kills
all bare coefficient descendants and all positive-depth descendants of every
admissible polynomially weighted twist.  A separate positive-degree hypothesis
is unnecessary, since `A.coeff d ≠ 0` and `0 < d` already witness it. -/
theorem commonSeed_descendants_of_kernel
    {K : Type*} [Field K] [Fintype K]
    (p : ℕ) [CharP K p] (hp : 0 < p)
    (A : Polynomial K) (T : PowerSeries K) (d : ℕ)
    (hdpos : 0 < d)
    (hdq : d < Fintype.card K)
    (hdne : A.coeff d ≠ 0)
    (hdprior : ∀ j, 0 < j → j < d → A.coeff j = 0)
    (hAdegree : A.natDegree < Fintype.card K - 1)
    (hA0 : A.coeff 0 = 1)
    (hT0 : PowerSeries.coeff 0 T = 1)
    (hT : T = (A : PowerSeries K) * dilate (Fintype.card K) T) :
    1 ≤ commonSeed p (Fintype.card K) d ∧
      (∀ E j, j < Fintype.card K ^ E →
        PowerSeries.coeff (commonSeed p (Fintype.card K) d * Fintype.card K ^ E + j) T = 0) ∧
      ∀ gamma : K, gamma ≠ 0 → (A.eval gamma = 0 ∨ A.eval gamma = 1) →
        ∀ P : Polynomial K, ∀ E, 1 ≤ E → ∀ j, j < Fintype.card K ^ E →
          Convolution.weighted P
              (fun n => PowerSeries.coeff n T * gamma ^ n)
              (commonSeed p (Fintype.card K) d * Fintype.card K ^ E + j) = 0 := by
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
  let seed := commonSeed p q d
  have he : q - 1 < q := by omega
  have heq : q - 1 + 1 = q := by omega
  have hte : PowerSeries.coeff (q - 1) T = 0 :=
    high_digit_zero_of_dilation_equation q hqpos A hAdegreeq T hT hT0
      (q - 1) he hAdegree
  have hseedt : PowerSeries.coeff seed T = 0 := by
    dsimp [seed, commonSeed]
    rw [hlucas _ _ he, hte, mul_zero]
  have hseedpos : 1 ≤ seed := by
    dsimp [seed, commonSeed]
    omega
  have hbare : ∀ E j, j < q ^ E →
      PowerSeries.coeff (seed * q ^ E + j) T = 0 := by
    apply zero_on_descendants_of_append
        (f := fun n => PowerSeries.coeff n T) (seed := seed) hq hseedt
    intro n a ha hn
    rw [hlucas n a ha, hn, zero_mul]
  refine ⟨hseedpos, hbare, ?_⟩
  intro gamma hgamma heval P
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
  have hve : v (q - 1) = 0 := by
    dsimp [v]
    rw [hte, zero_mul]
  have hs0 : prefixState v 0 = (1, 1) := by simp [prefixState, hv0]
  have hseedv : prefixState v seed = (0, 0) := by
    dsimp [seed, commonSeed]
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

/-- An arbitrary family of normalized kernels with the same supplied first
positive digit has one common seed.  The witness is outside the quantifiers over
the family index, pole parameter, and polynomial weight. -/
theorem exists_commonSeed_for_indexed_kernels
    {ι K : Type*} [Field K] [Fintype K]
    (p : ℕ) [CharP K p] (hp : 0 < p)
    (A : ι → Polynomial K) (T : ι → PowerSeries K) (d : ℕ)
    (hdpos : 0 < d)
    (hdq : d < Fintype.card K)
    (hdne : ∀ i, (A i).coeff d ≠ 0)
    (hdprior : ∀ i j, 0 < j → j < d → (A i).coeff j = 0)
    (hAdegree : ∀ i, (A i).natDegree < Fintype.card K - 1)
    (hA0 : ∀ i, (A i).coeff 0 = 1)
    (hT0 : ∀ i, PowerSeries.coeff 0 (T i) = 1)
    (hT : ∀ i, T i = (A i : PowerSeries K) * dilate (Fintype.card K) (T i)) :
    ∃ seed, seed = commonSeed p (Fintype.card K) d ∧ 1 ≤ seed ∧
      (∀ i E j, j < Fintype.card K ^ E →
        PowerSeries.coeff (seed * Fintype.card K ^ E + j) (T i) = 0) ∧
      ∀ i, ∀ gamma : K,
        gamma ≠ 0 → ((A i).eval gamma = 0 ∨ (A i).eval gamma = 1) →
        ∀ P : Polynomial K, ∀ E, 1 ≤ E → ∀ j, j < Fintype.card K ^ E →
          Convolution.weighted P
              (fun n => PowerSeries.coeff n (T i) * gamma ^ n)
              (seed * Fintype.card K ^ E + j) = 0 := by
  let seed := commonSeed p (Fintype.card K) d
  have hi (i : ι) := commonSeed_descendants_of_kernel p hp (A i) (T i) d
    hdpos hdq (hdne i) (hdprior i) (hAdegree i) (hA0 i) (hT0 i) (hT i)
  refine ⟨seed, rfl, ?_, ?_, ?_⟩
  · have hq : 2 ≤ Fintype.card K := Fintype.one_lt_card
    dsimp [seed, commonSeed]
    omega
  · intro i E j hj
    exact (hi i).2.1 E j hj
  · intro i gamma hgamma heval P E hE j hj
    exact (hi i).2.2 gamma hgamma heval P E hE j hj

end SierpinskiFormal

#print axioms SierpinskiFormal.commonSeed_descendants_of_kernel
#print axioms SierpinskiFormal.exists_commonSeed_for_indexed_kernels
