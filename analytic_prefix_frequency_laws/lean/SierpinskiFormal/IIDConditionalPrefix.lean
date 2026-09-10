import SierpinskiFormal.FiniteIIDWordLaw
import SierpinskiFormal.PrefixFiltration
import Mathlib.Probability.ConditionalExpectation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

/-! # Conditional expectations of fresh IID finite words -/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace IndependentZeroBlocks

variable {A : Type*} [MeasurableSpace A]

abbrev tailCoordinateSigma (n : ℕ) : MeasurableSpace (ℕ → A) :=
  ⨆ k, ⨆ (_ : n < k), MeasurableSpace.comap (fun ω : ℕ → A ↦ ω k) inferInstance

theorem tailCoordinateSigma_le (n : ℕ) :
    tailCoordinateSigma (A := A) n ≤ (inferInstance : MeasurableSpace (ℕ → A)) :=
  iSup₂_le fun k _ ↦ (measurable_pi_apply k).comap_le

variable [Fintype A]

theorem iid_indep_tail_prefix (L : FiniteProbabilityWeights A) (n : ℕ) :
    Indep (tailCoordinateSigma (A := A) n) (prefixFiltration n) L.iidMeasure := by
  have hi : iIndepFun (fun k (ω : ℕ → A) ↦ ω k) L.iidMeasure :=
    iIndepFun_infinitePi (P := fun _ : ℕ ↦ L.letterMeasure)
      (X := fun _ x ↦ x) (fun _ ↦ measurable_id)
  exact indep_iSup_of_disjoint (fun k ↦ (measurable_pi_apply k).comap_le) hi
    (S := {k : ℕ | n < k}) (T := {k : ℕ | k ≤ n}) (by
      apply Set.disjoint_left.mpr
      intro k hk hk'
      change n < k at hk
      change k ≤ n at hk'
      omega)

variable [MeasurableSingletonClass A]

/-- A finite observation strictly after coordinate `n` is measurable in the
tail sigma algebra, with no reference to the first `n+1` coordinates. -/
theorem measurable_tail_observation (n N : ℕ) (F : (Fin N → A) → ℝ) :
    @Measurable (ℕ → A) ℝ (tailCoordinateSigma n) inferInstance
      (fun ω ↦ F (fun i ↦ ω (n + 1 + i.val))) := by
  letI : MeasurableSpace (ℕ → A) := tailCoordinateSigma n
  apply (measurable_of_countable F).comp
  apply measurable_pi_lambda
  intro i
  apply Measurable.of_comap_le
  exact le_iSup_of_le (n + 1 + i.val) (le_iSup_of_le (by omega) le_rfl)

/-- Fresh finite-word observations have their ordinary expectation after
conditioning on the observed finite prefix. -/
theorem condExp_tail_observation (L : FiniteProbabilityWeights A)
    (n N : ℕ) (F : (Fin N → A) → ℝ) :
    L.iidMeasure[fun ω ↦ F (fun i ↦ ω (n + 1 + i.val)) | prefixFiltration n] =ᵐ[L.iidMeasure]
      fun _ ↦ ∫ ω, F (fun i ↦ ω (n + 1 + i.val)) ∂L.iidMeasure := by
  exact condExp_indep_eq (tailCoordinateSigma_le n) (prefixFiltration.le n)
    (measurable_tail_observation n N F).stronglyMeasurable
    (iid_indep_tail_prefix L n)

variable [DecidableEq A]

/-- The actual fresh coordinates have the pinned finite product law. -/
theorem iid_tail_observation_law (L : FiniteProbabilityWeights A)
    (n N : ℕ) (F : (Fin N → A) → ℝ) :
    Integrable (fun ω ↦ F (fun i ↦ ω (n + 1 + i.val))) L.iidMeasure ∧
    (∫ ω, F (fun i ↦ ω (n + 1 + i.val)) ∂L.iidMeasure) =
      ∑ w : Fin N → A, wordWeight L.weight (List.ofFn w) * F w := by
  let φ : (ℕ → A) → (Fin N → A) := fun ω i ↦ ω (n + 1 + i.val)
  have hφ : Measurable φ := measurable_pi_lambda _ fun i ↦ measurable_pi_apply _
  have hmap : L.iidMeasure.map φ =
      Measure.infinitePi (fun _ : Fin N ↦ L.letterMeasure) := by
    simpa only [FiniteProbabilityWeights.iidMeasure, φ] using
      (Measure.map_infinitePi_infinitePi_of_inj
        (P := fun _ : ℕ ↦ L.letterMeasure)
        (f := fun i : Fin N ↦ n + 1 + i.val)
        (fun i j hij ↦ Fin.ext (Nat.add_left_cancel hij)))
  have hF : Integrable F (Measure.infinitePi (fun _ : Fin N ↦ L.letterMeasure)) := .of_finite
  have hFm : Integrable F (L.iidMeasure.map φ) := by rwa [hmap]
  refine ⟨hFm.comp_aemeasurable hφ.aemeasurable, ?_⟩
  change (∫ ω, F (φ ω) ∂L.iidMeasure) = _
  rw [← integral_map hφ.aemeasurable hFm.aestronglyMeasurable, hmap]
  rw [integral_fintype hF]
  apply Finset.sum_congr rfl
  intro w _
  simp only [Measure.real, Measure.infinitePi_singleton_of_fintype,
    FiniteProbabilityWeights.letterMeasure_singleton, wordWeight, smul_eq_mul]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ L.nonneg (w i)),
    ENNReal.toReal_ofReal (Finset.prod_nonneg fun i _ ↦ L.nonneg (w i))]
  simp [List.prod_ofFn]

end IndependentZeroBlocks
