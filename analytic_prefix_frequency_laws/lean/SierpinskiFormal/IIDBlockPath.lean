import SierpinskiFormal.InitialMarkerGap
import SierpinskiFormal.WeightedBlockCoding

/-! # The actual regrouped IID block path -/

noncomputable section
open MeasureTheory Function
open scoped BigOperators
namespace IndependentZeroBlocks

variable {A : Type*} [MeasurableSpace A] [Fintype A] [MeasurableSingletonClass A]
  [DecidableEq A]

def iidBlockPath (ell : ℕ) (ω : ℕ → A) : ℕ → (Fin ell → A) :=
  fun n i ↦ ω (n * ell + i.val)

theorem measurable_iidBlockPath (ell : ℕ) : Measurable (iidBlockPath (A := A) ell) := by
  apply measurable_pi_lambda
  intro n
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply _

def FiniteProbabilityWeights.blockLaw (P : FiniteProbabilityWeights A) (ell : ℕ) :
    FiniteProbabilityWeights (Fin ell → A) where
  weight := blockWeight P.weight ell
  nonneg := blockWeight_nonneg P.weight P.nonneg ell
  sum_eq_one := sum_blockWeight_eq_one P.weight P.sum_eq_one ell

theorem blockLaw_letterMeasure (P : FiniteProbabilityWeights A) (ell : ℕ) :
    (P.blockLaw ell).letterMeasure = Measure.infinitePi (fun _ : Fin ell ↦ P.letterMeasure) := by
  apply Measure.ext_of_singleton
  intro a
  simp only [FiniteProbabilityWeights.letterMeasure_singleton,
    Measure.infinitePi_singleton_of_fintype]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ P.nonneg (a i))]
  simp [FiniteProbabilityWeights.blockLaw, blockWeight, wordWeight, List.prod_ofFn]

theorem measurePreserving_iidBlockPath (P : FiniteProbabilityWeights A)
    (ell : ℕ) (hell : 0 < ell) :
    MeasurePreserving (iidBlockPath ell) P.iidMeasure (P.blockLaw ell).iidMeasure := by
  letI : NeZero ell := ⟨hell.ne'⟩
  let f : ℕ × Fin ell → ℕ := fun k ↦ k.1 * ell + k.2.val
  have hf : Injective f := by
    convert (Nat.divModEquiv ell).symm.injective using 1
    simp [f, Nat.divModEquiv, Nat.mul_comm]
  have hmap := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : ℕ ↦ P.letterMeasure) hf
  refine ⟨measurable_iidBlockPath ell, ?_⟩
  have hc := Measure.infinitePi_map_curry (fun (_ : ℕ) (_ : Fin ell) ↦ P.letterMeasure)
  rw [← hmap, Measure.map_map] at hc
  · have hfun : (MeasurableEquiv.curry ℕ (Fin ell) A) ∘
        (fun ω : ℕ → A ↦ fun k : ℕ × Fin ell ↦ ω (f k)) = iidBlockPath ell := by
      rfl
    rw [hfun] at hc
    simpa only [FiniteProbabilityWeights.iidMeasure, ← blockLaw_letterMeasure] using hc
  · exact (MeasurableEquiv.curry ℕ (Fin ell) A).measurable
  · fun_prop

theorem flatten_iidBlockPath_prefix (ell n : ℕ) (ω : ℕ → A) :
    flattenBlocks ell (stationaryPrefix digitHead digitShift n (iidBlockPath ell ω)) =
      stationaryPrefix digitHead digitShift (n * ell) ω := by
  simp only [FiniteProbabilityWeights.stationaryPrefix_digit_eq_ofFn]
  rw [List.ofFn_mul]
  simp [flattenBlocks, List.map_ofFn, Function.comp_def, iidBlockPath]
  rfl

theorem blockLaw_weight_pos (P : FiniteProbabilityWeights A)
    (hp : ∀ a, 0 < P.weight a) (ell : ℕ) (a : Fin ell → A) :
    0 < (P.blockLaw ell).weight a := by
  simp only [FiniteProbabilityWeights.blockLaw, blockWeight, wordWeight, List.map_ofFn, List.prod_ofFn]
  exact Finset.prod_pos fun i _ ↦ hp (a i)

end IndependentZeroBlocks
