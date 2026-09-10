import SierpinskiFormal.KernelPrefix
import SierpinskiFormal.PeriodicConvolution

set_option autoImplicit false

namespace IndependentZeroBlocks
open SierpinskiFormal

/-- One kernel seed handles every admissible geometric twist and every
weight whose period divides a power of the field cardinality. -/
theorem exists_common_seed_periodic_filters
    {K : Type*} [Field K] [Fintype K]
    (p : ℕ) [CharP K p] (hp : 0 < p)
    (A : Polynomial K) (T : PowerSeries K)
    (hApos : 0 < A.natDegree)
    (hAdegree : A.natDegree < Fintype.card K - 1)
    (hA0 : A.coeff 0 = 1)
    (hT0 : PowerSeries.coeff 0 T = 1)
    (hT : T = (A : PowerSeries K) * dilate (Fintype.card K) T) :
    ∃ seed : ℕ, 1 ≤ seed ∧ HasSeedBlocks (Fintype.card K) seed T ∧
      ∀ beta : K, beta ≠ 0 → (A.eval beta⁻¹ = 0 ∨ A.eval beta⁻¹ = 1) →
        ∀ (r : ℕ) (w : ℕ → K), Function.Periodic w (Fintype.card K ^ r) →
          HasSeedBlocks (Fintype.card K) seed
            (PeriodicConvolution.weightedSeries w beta * T) := by
  have hq : 2 ≤ Fintype.card K := Fintype.one_lt_card
  have hdeg : A.natDegree < Fintype.card K := by omega
  obtain ⟨d, hdpos, hdq, hdne, hdprior⟩ :=
    exists_first_nonzero_kernel_digit A (Fintype.card K) hApos hdeg
  obtain ⟨hseedpos, hbare, hprefix⟩ := commonSeed_prefix_of_kernel p hp A T d
    hdpos hdq hdne hdprior hAdegree hA0 hT0 hT
  refine ⟨commonSeed p (Fintype.card K) d, hseedpos, ⟨0, 0, ?_⟩, ?_⟩
  · intro E _ j _ hj
    exact hbare E j hj
  · intro beta hbeta heval r w hw
    apply PeriodicConvolution.weightedSeries_mul_hasSeedBlocks_of_prefix
      (Fintype.card K) (commonSeed p (Fintype.card K) d) r hq
      (FiniteField.cast_card_eq_zero K) w hw beta hbeta T
    · simp [hT0]
    · exact Convolution.twist_lucas (fun n => PowerSeries.coeff n T)
        (Fintype.card K) beta⁻¹ (FiniteField.pow_card beta⁻¹)
        (lucas_of_dilation_equation (Fintype.card K) Fintype.card_pos A hdeg T hT hT0)
    · exact hprefix beta⁻¹ (inv_ne_zero hbeta) heval

end IndependentZeroBlocks
