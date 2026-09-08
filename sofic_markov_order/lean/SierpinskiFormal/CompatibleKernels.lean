import SierpinskiFormal.KernelPeriodic
import SierpinskiFormal.RadixExtension

set_option autoImplicit false

namespace IndependentZeroBlocks
open SierpinskiFormal

/-- A specified first positive degree gives the same periodic-filter seed
for every compatible polynomial kernel over the field. -/
theorem commonSeed_periodic_filters_of_first_degree
    {K : Type*} [Field K] [Fintype K]
    (p : ℕ) [CharP K p] (hp : 0 < p)
    (A : Polynomial K) (T : PowerSeries K) (d : ℕ)
    (hdpos : 0 < d) (hdne : A.coeff d ≠ 0)
    (hdprior : ∀ j, 0 < j → j < d → A.coeff j = 0)
    (hAdegree : A.natDegree < Fintype.card K - 1)
    (hA0 : A.coeff 0 = 1)
    (hT0 : PowerSeries.coeff 0 T = 1)
    (hT : T = (A : PowerSeries K) * dilate (Fintype.card K) T) :
    1 ≤ commonSeed p (Fintype.card K) d ∧
      HasSeedBlocks (Fintype.card K) (commonSeed p (Fintype.card K) d) T ∧
      ∀ beta : K, beta ≠ 0 → (A.eval beta⁻¹ = 0 ∨ A.eval beta⁻¹ = 1) →
        ∀ (r : ℕ) (w : ℕ → K), Function.Periodic w (Fintype.card K ^ r) →
          HasSeedBlocks (Fintype.card K) (commonSeed p (Fintype.card K) d)
            (PeriodicConvolution.weightedSeries w beta * T) := by
  have hdq : d < Fintype.card K := by
    have := Polynomial.le_natDegree_of_ne_zero hdne
    omega
  have hq : 2 ≤ Fintype.card K := Fintype.one_lt_card
  obtain ⟨hseed, hbare, hprefix⟩ := commonSeed_prefix_of_kernel p hp A T d
    hdpos hdq hdne hdprior hAdegree hA0 hT0 hT
  refine ⟨hseed, ⟨0, 0, ?_⟩, ?_⟩
  · intro E _ j _ hj
    exact hbare E j hj
  · intro beta hbeta heval r w hw
    apply PeriodicConvolution.weightedSeries_mul_hasSeedBlocks_of_prefix
      (Fintype.card K) (commonSeed p (Fintype.card K) d) r hq
      (FiniteField.cast_card_eq_zero K) w hw beta hbeta T
    · simp [hT0]
    · exact Convolution.twist_lucas (fun n => PowerSeries.coeff n T)
        (Fintype.card K) beta⁻¹ (FiniteField.pow_card beta⁻¹)
        (lucas_of_dilation_equation (Fintype.card K) Fintype.card_pos A
          (by omega) T hT hT0)
    · exact hprefix beta⁻¹ (inv_ne_zero hbeta) heval

/-- Enlargement of the coefficient field preserves a specified first
positive degree, so common seeds remain common across different kernels. -/
theorem radixExtensionKernel_first_degree
    {K L : Type*} [Field K] [Field L] [Fintype K] [Fintype L] [Algebra K L]
    (A : Polynomial K) (hA0 : A.coeff 0 = 1)
    (hdegree : A.natDegree < Fintype.card K - 1)
    (d : ℕ) (hdne : A.coeff d ≠ 0)
    (hdprior : ∀ j, 0 < j → j < d → A.coeff j = 0) :
    ((A.map (algebraMap K L)) ^ radixExtensionExponent K L).coeff d ≠ 0 ∧
      ∀ j, 0 < j → j < d →
        ((A.map (algebraMap K L)) ^ radixExtensionExponent K L).coeff j = 0 := by
  have hdq : d < Fintype.card K := by
    have := Polynomial.le_natDegree_of_ne_zero hdne
    omega
  constructor
  · rw [coeff_radixExtensionKernel_of_lt_card A hA0 hdegree d hdq]
    exact (map_ne_zero (algebraMap K L)).mpr hdne
  · intro j hjpos hjd
    rw [coeff_radixExtensionKernel_of_lt_card A hA0 hdegree j (lt_trans hjd hdq),
      hdprior j hjpos hjd, map_zero]

end IndependentZeroBlocks
