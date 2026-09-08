import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Countable fiber measures and Radon--Nikodym weights

A finite measure on `X × K`, with countable measurable fibers in `K`, splits
as the sum of its singleton-fiber measures.  When its first marginal is `μ`,
these fibers are dominated by `μ`; their Radon--Nikodym derivatives form a
probability vector almost everywhere.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal BigOperators

namespace IndependentZeroBlocks
section AtomicFibers

variable {X K : Type*} [MeasurableSpace X] [MeasurableSpace K]

/-- The source measure carried by the fiber over `k`. -/
noncomputable def countableFiberMeasure (ν : Measure (X × K)) (k : K) :
    Measure X :=
  (ν.restrict ((Prod.snd : X × K → K) ⁻¹' ({k} : Set K))).fst

/-- A fiber measure is dominated by the first marginal. -/
theorem countableFiberMeasure_le_fst (ν : Measure (X × K)) (k : K) :
    countableFiberMeasure ν k ≤ ν.fst := by
  exact Measure.fst_mono Measure.restrict_le_self

/-- If the first marginal is `μ`, every fiber measure is absolutely
continuous with respect to `μ`. -/
theorem countableFiberMeasure_absolutelyContinuous_of_fst_eq
    {ν : Measure (X × K)} {μ : Measure X} (hν : ν.fst = μ) (k : K) :
    countableFiberMeasure ν k ≪ μ := by
  apply Measure.absolutelyContinuous_of_le
  rw [← hν]
  exact countableFiberMeasure_le_fst ν k

/-- Radon--Nikodym reconstruction of one fiber measure. -/
theorem withDensity_rnDeriv_countableFiberMeasure
    {ν : Measure (X × K)} [IsFiniteMeasure ν]
    {μ : Measure X} [SigmaFinite μ]
    (hν : ν.fst = μ) (k : K) :
    μ.withDensity ((countableFiberMeasure ν k).rnDeriv μ) =
      countableFiberMeasure ν k := by
  letI : IsFiniteMeasure (countableFiberMeasure ν k) := by
    dsimp [countableFiberMeasure]
    infer_instance
  exact Measure.withDensity_rnDeriv_eq _ _
    (countableFiberMeasure_absolutelyContinuous_of_fst_eq hν k)

/-- A measure on a product with countable second coordinate is the sum of
its restrictions to singleton fibers. -/
theorem restrict_sum_countable_fibers [MeasurableSingletonClass K]
    [Countable K] (ν : Measure (X × K)) :
    ν = Measure.sum (fun k : K =>
      ν.restrict ((Prod.snd : X × K → K) ⁻¹' ({k} : Set K))) := by
  have hunion : (⋃ k : K,
      (Prod.snd : X × K → K) ⁻¹' ({k} : Set K)) = Set.univ := by
    ext z
    simp
  have hdisjoint : Pairwise (Function.onFun Disjoint
      (fun k : K => (Prod.snd : X × K → K) ⁻¹' ({k} : Set K))) := by
    intro i j hij
    change Disjoint ((Prod.snd : X × K → K) ⁻¹' ({i} : Set K))
      ((Prod.snd : X × K → K) ⁻¹' ({j} : Set K))
    rw [Set.disjoint_left]
    intro z hzi hzj
    apply hij
    simpa only [Set.mem_preimage, Set.mem_singleton_iff] using
      hzi.symm.trans hzj
  calc
    ν = ν.restrict Set.univ := (Measure.restrict_univ).symm
    _ = ν.restrict (⋃ k : K,
        (Prod.snd : X × K → K) ⁻¹' ({k} : Set K)) := by rw [hunion]
    _ = Measure.sum (fun k : K =>
        ν.restrict ((Prod.snd : X × K → K) ⁻¹' ({k} : Set K))) :=
      Measure.restrict_iUnion hdisjoint
        (fun k => (measurableSet_singleton k).preimage measurable_snd)

/-- The first marginal is the sum of the countable fiber measures. -/
theorem fst_eq_sum_countableFiberMeasure [MeasurableSingletonClass K]
    [Countable K] (ν : Measure (X × K)) :
    ν.fst = Measure.sum (fun k : K => countableFiberMeasure ν k) := by
  calc
    ν.fst = (Measure.sum (fun k : K =>
        ν.restrict ((Prod.snd : X × K → K) ⁻¹' ({k} : Set K)))).fst := by
      rw [← restrict_sum_countable_fibers ν]
    _ = Measure.sum (fun k : K => countableFiberMeasure ν k) := by
      rw [Measure.fst_sum]
      rfl

/-- With prescribed first marginal `μ`, the countable fiber measures sum
to `μ`. -/
theorem sum_countableFiberMeasure_eq_of_fst_eq
    [MeasurableSingletonClass K] [Countable K]
    {ν : Measure (X × K)} {μ : Measure X} (hν : ν.fst = μ) :
    Measure.sum (fun k : K => countableFiberMeasure ν k) = μ := by
  rw [← hν]
  exact (fst_eq_sum_countableFiberMeasure ν).symm

/-- The nonnegative Radon--Nikodym density of the fiber over `k`. -/
noncomputable def countableFiberDensity
    (ν : Measure (X × K)) (μ : Measure X) (k : K) : X → ℝ≥0∞ :=
  (countableFiberMeasure ν k).rnDeriv μ

theorem measurable_countableFiberDensity
    (ν : Measure (X × K)) (μ : Measure X) (k : K) :
    Measurable (countableFiberDensity ν μ k) :=
  Measure.measurable_rnDeriv _ _

/-- When the first marginal is `μ`, the countable fiber densities form a
probability vector at `μ`-almost every source point. -/
theorem tsum_countableFiberDensity_eq_one_ae
    [MeasurableSingletonClass K] [Countable K]
    (ν : Measure (X × K)) [IsFiniteMeasure ν]
    (μ : Measure X) [SigmaFinite μ] (hν : ν.fst = μ) :
    (fun x => ∑' k : K, countableFiberDensity ν μ k x) =ᵐ[μ] 1 := by
  have hdensity : ∀ k : K,
      μ.withDensity (countableFiberDensity ν μ k) =
        countableFiberMeasure ν k :=
    fun k => withDensity_rnDeriv_countableFiberMeasure hν k
  have hsum : μ = Measure.sum (fun k : K => countableFiberMeasure ν k) := by
    rw [← hν]
    exact fst_eq_sum_countableFiberMeasure ν
  have hmeas : ∀ k : K, Measurable (countableFiberDensity ν μ k) :=
    measurable_countableFiberDensity ν μ
  have hdecomp : μ = 0 + μ.withDensity
      (fun x => ∑' k : K, countableFiberDensity ν μ k x) := by
    have hfun : (fun x => ∑' k : K, countableFiberDensity ν μ k x) =
        ∑' k : K, countableFiberDensity ν μ k := by
      funext x
      exact (tsum_apply (Pi.summable.2 fun _ => ENNReal.summable)).symm
    rw [hfun]
    rw [zero_add, MeasureTheory.withDensity_tsum hmeas]
    simpa only [hdensity] using hsum
  have hrn := Measure.eq_rnDeriv
    (μ := μ) (ν := μ) (s := 0)
    (Measurable.ennreal_tsum hmeas) Measure.MutuallySingular.zero_left hdecomp
  exact hrn.trans (Measure.rnDeriv_self μ)

end AtomicFibers
section RealFiberDensities

variable {X K : Type*} [MeasurableSpace X] [MeasurableSpace K]

/-- The real-valued version of a countable fiber density. -/
noncomputable def countableFiberDensityReal
    (ν : Measure (X × K)) (μ : Measure X) (k : K) : X → ℝ :=
  fun x => (countableFiberDensity ν μ k x).toReal

theorem measurable_countableFiberDensityReal
    (ν : Measure (X × K)) (μ : Measure X) (k : K) :
    Measurable (countableFiberDensityReal ν μ k) :=
  (measurable_countableFiberDensity ν μ k).ennreal_toReal

theorem countableFiberDensityReal_nonneg
    (ν : Measure (X × K)) (μ : Measure X) (k : K) (x : X) :
    0 ≤ countableFiberDensityReal ν μ k x :=
  ENNReal.toReal_nonneg

/-- The real Radon--Nikodym weights sum to one almost everywhere.  This is
convenient for pointwise convex combinations in Bochner spaces. -/
theorem tsum_countableFiberDensityReal_eq_one_ae
    [MeasurableSingletonClass K] [Countable K]
    (ν : Measure (X × K)) [IsFiniteMeasure ν]
    (μ : Measure X) [SigmaFinite μ] (hν : ν.fst = μ) :
    (fun x => ∑' k : K, countableFiberDensityReal ν μ k x) =ᵐ[μ] 1 := by
  filter_upwards [tsum_countableFiberDensity_eq_one_ae ν μ hν] with x hx
  have hfinite : ∀ k : K, countableFiberDensity ν μ k x ≠ ⊤ := by
    intro k hk
    have hle : countableFiberDensity ν μ k x ≤
        ∑' j : K, countableFiberDensity ν μ j x :=
      ENNReal.le_tsum k
    rw [hx, hk] at hle
    exact (not_le_of_gt ENNReal.one_lt_top) hle
  change ∑' k : K, (countableFiberDensity ν μ k x).toReal = 1
  rw [← ENNReal.tsum_toReal_eq hfinite, hx]
  simp

/-- Bundled interface for the graph-state route: measurable nonnegative real
fiber weights, reconstruction of each fiber measure, and a.e. normalization. -/
theorem exists_countableFiberDensityReal_partition
    [MeasurableSingletonClass K] [Countable K]
    (ν : Measure (X × K)) [IsFiniteMeasure ν]
    (μ : Measure X) [SigmaFinite μ] (hν : ν.fst = μ) :
    ∃ ρ : K → X → ℝ,
      (∀ k, Measurable (ρ k)) ∧
      (∀ k x, 0 ≤ ρ k x) ∧
      (∀ k, μ.withDensity (fun x => ENNReal.ofReal (ρ k x)) =
        countableFiberMeasure ν k) ∧
      (fun x => ∑' k : K, ρ k x) =ᵐ[μ] 1 := by
  refine ⟨fun k => countableFiberDensityReal ν μ k,
    measurable_countableFiberDensityReal ν μ,
    countableFiberDensityReal_nonneg ν μ, ?_,
    tsum_countableFiberDensityReal_eq_one_ae ν μ hν⟩
  intro k
  have hfinite : ∀ᵐ x ∂μ, countableFiberDensity ν μ k x ≠ ⊤ := by
    filter_upwards [tsum_countableFiberDensity_eq_one_ae ν μ hν] with x hx
    intro hk
    have hle : countableFiberDensity ν μ k x ≤
        ∑' j : K, countableFiberDensity ν μ j x :=
      ENNReal.le_tsum k
    rw [hx, hk] at hle
    exact (not_le_of_gt ENNReal.one_lt_top) hle
  rw [← withDensity_rnDeriv_countableFiberMeasure hν k]
  apply withDensity_congr_ae
  filter_upwards [hfinite] with x hx
  exact ENNReal.ofReal_toReal hx

end RealFiberDensities

end IndependentZeroBlocks
