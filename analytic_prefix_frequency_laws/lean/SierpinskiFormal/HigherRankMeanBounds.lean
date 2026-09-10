import SierpinskiFormal.HigherRankCentralReturnMean
import SierpinskiFormal.CommonContextLogDensity

/-! # The internal rational means are probability values -/

noncomputable section
open Filter Set Topology
namespace IndependentZeroBlocks

theorem realCesaroLimit_mem_Icc {c : ℕ → ℝ} {L : ℝ}
    (hc : ∀ n, c n ∈ Set.Icc (0 : ℝ) 1)
    (hL : Tendsto (realCesaroMean c) atTop (𝓝 L)) :
    L ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · apply ge_of_tendsto hL
    exact Eventually.of_forall fun N ↦ realCesaroMean_nonneg (fun n ↦ (hc n).1) N
  · apply le_of_tendsto hL
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact realCesaroMean_le_one (fun n ↦ (hc n).2) hN

theorem centralReturnCesaroLimit_mem_Icc
    {F C ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
    [TopologicalSpace C] [DiscreteTopology C] [Fintype C] [Nonempty C]
    [DecidableEq C] {r : ℕ}
    (M : C → Matrix ι ι F) (U : Matrix ι (Fin r) F)
    (V : Matrix (Fin r) ι F)
    (left : Module.Dual F (Fin r → F)) (seed : Fin r → F)
    (p : C → ℝ) (hp : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1)
    (L : ℝ)
    (hL : Tendsto
      (realCesaroMean (centralReturnExactAverage M U V left seed p))
      atTop (𝓝 L)) : L ∈ Set.Icc (0 : ℝ) 1 :=
  realCesaroLimit_mem_Icc
    (centralReturnExactAverage_mem_Icc M U V left seed p hp hp1) hL

end IndependentZeroBlocks
