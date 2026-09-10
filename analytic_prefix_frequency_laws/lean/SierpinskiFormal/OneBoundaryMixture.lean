import SierpinskiFormal.ModuleDensityAssembly

/-! # Collapsing a source-independent initial boundary in a reset mixture -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped BigOperators
namespace IndependentZeroBlocks

variable {A : Type*} [Fintype A] [Nonempty A] [DecidableEq A]
  [TopologicalSpace A] [DiscreteTopology A]

theorem hasSum_markerGapWeight_one
    (p : A → ℝ) (e : A) (hp : ∀ a, 0 ≤ p a)
    (hp1 : ∑ a, p a = 1) (he : 0 < p e) :
    HasSum (fun g : GapWords e ↦ p e * wordWeight p g.1) 1 := by
  have hlt : realNonMarkerMass p e < 1 := by
    rw [realNonMarkerMass_eq_one_sub p e hp1]
    linarith
  have h := (hasSum_gapWordWeight_geometric p e hp hlt).mul_left (p e)
  have hz : 1 - realNonMarkerMass p e = p e := by
    rw [realNonMarkerMass_eq_one_sub p e hp1]
    ring
  rw [hz, mul_inv_cancel₀ he.ne'] at h
  exact h

theorem summable_oneBoundaryMean
    (p : A → ℝ) (e : A) (hp : ∀ a, 0 ≤ p a)
    (hp1 : ∑ a, p a = 1) (he : 0 < p e)
    (m : GapWords e → ℝ) (hm : ∀ g, m g ∈ Icc (0 : ℝ) 1) :
    Summable (fun g ↦ p e * wordWeight p g.1 * m g) := by
  apply Summable.of_nonneg_of_le
    (fun g ↦ mul_nonneg (mul_nonneg he.le (wordWeight_nonneg p hp g.1)) (hm g).1)
    (fun g ↦ mul_le_of_le_one_right
      (mul_nonneg he.le (wordWeight_nonneg p hp g.1)) (hm g).2)
  exact (hasSum_markerGapWeight_one p e hp hp1 he).summable

theorem oneBoundaryMean_mem_Icc
    (p : A → ℝ) (e : A) (hp : ∀ a, 0 ≤ p a)
    (hp1 : ∑ a, p a = 1) (he : 0 < p e)
    (m : GapWords e → ℝ) (hm : ∀ g, m g ∈ Icc (0 : ℝ) 1) :
    (∑' g, p e * wordWeight p g.1 * m g) ∈ Icc (0 : ℝ) 1 := by
  refine ⟨tsum_nonneg (fun g ↦
    mul_nonneg (mul_nonneg he.le (wordWeight_nonneg p hp g.1)) (hm g).1), ?_⟩
  rw [← (hasSum_markerGapWeight_one p e hp hp1 he).tsum_eq]
  exact Summable.tsum_le_tsum (fun g ↦ mul_le_of_le_one_right
    (mul_nonneg he.le (wordWeight_nonneg p hp g.1)) (hm g).2)
    (summable_oneBoundaryMean p e hp hp1 he m hm)
    (hasSum_markerGapWeight_one p e hp hp1 he).summable

theorem twoBoundaryMean_eq_oneBoundaryMean
    (p : A → ℝ) (e : A) (hp : ∀ a, 0 ≤ p a)
    (hp1 : ∑ a, p a = 1) (he : 0 < p e)
    (m : GapWords e → ℝ) (hm : ∀ g, m g ∈ Icc (0 : ℝ) 1) :
    (∑' i : GapWords e × GapWords e, moduleBoundaryWeight p e i * m i.2) =
      p e * ∑' v, wordWeight p v.1 * m v := by
  let a : GapWords e → ℝ := fun g ↦ p e * wordWeight p g.1
  let b : GapWords e → ℝ := fun g ↦ p e * wordWeight p g.1 * m g
  have ha := hasSum_markerGapWeight_one p e hp hp1 he
  have hb := summable_oneBoundaryMean p e hp hp1 he m hm
  have hap : ∀ g, 0 ≤ a g := fun g ↦ mul_nonneg he.le (wordWeight_nonneg p hp g.1)
  have hbp : ∀ g, 0 ≤ b g := fun g ↦ mul_nonneg (hap g) (hm g).1
  have hab : Summable (fun i : GapWords e × GapWords e ↦ a i.1 * b i.2) :=
    ha.summable.mul_of_nonneg hb hap hbp
  have hterm : (fun i : GapWords e × GapWords e ↦ moduleBoundaryWeight p e i * m i.2) =
      fun i ↦ a i.1 * b i.2 := by
    funext i
    dsimp [a, b, moduleBoundaryWeight]
    ring
  rw [hterm, ← ha.summable.tsum_mul_tsum hb hab, ha.tsum_eq, one_mul]
  simp only [b, mul_assoc, tsum_mul_left]

end IndependentZeroBlocks
