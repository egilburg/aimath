import SierpinskiFormal.UniformAtomicTransforms
import SierpinskiFormal.ModuleBlockAtomicLaw
import SierpinskiFormal.RationalBoundaryDensityAnalytic

/-! # A uniform holomorphic extension of every branch of one block law -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Set Topology
open scoped BigOperators BoundedContinuousFunction
namespace IndependentZeroBlocks

variable {A : Type*} [Fintype A] [DecidableEq A]
  [TopologicalSpace A] [DiscreteTopology A]

abbrev BlockBranchCoefficients (h : List A) :=
  (s : Fin h.length) → (Fin (s : ℕ) → A) →
    List (Fin h.length → A) → List (Fin h.length → A) → ℚ

def blockBranchComplexCoefficient (h : List A) (m : BlockBranchCoefficients h)
    (s : Fin h.length) (ξ : Fin (s : ℕ) → A)
    (u v : List (NonMarkerBlock h)) : ℂ :=
  (m s ξ (gapOfSubtypeList h u).1 (gapOfSubtypeList h v).1 : ℂ)

theorem norm_blockBranchComplexCoefficient (h : List A) (m : BlockBranchCoefficients h)
    (hm : ∀ s ξ u v, (m s ξ u v : ℝ) ∈ Icc (0 : ℝ) 1)
    (s : Fin h.length) (ξ : Fin (s : ℕ) → A) (u v : List (NonMarkerBlock h)) :
    ‖blockBranchComplexCoefficient h m s ξ u v‖ ≤ 1 := by
  have hb := hm s ξ (gapOfSubtypeList h u).1 (gapOfSubtypeList h v).1
  change ‖((m s ξ (gapOfSubtypeList h u).1 (gapOfSubtypeList h v).1 : ℝ) : ℂ)‖ ≤ 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb.1]
  exact hb.2

def uniformBlockBranch (h : List A) (m : BlockBranchCoefficients h)
    (hm : ∀ s ξ u v, (m s ξ u v : ℝ) ∈ Icc (0 : ℝ) 1)
    (z : A → ℂ) : List (NonMarkerBlock h) →ᵇ ℂ :=
  (h.length : ℂ)⁻¹ • ∑ s : Fin h.length, ∑ ξ : Fin (s : ℕ) → A,
    Sierpinski.finWordMonomial z ξ •
      Sierpinski.uniformWordBranch (blockBranchComplexCoefficient h m s ξ)
        (norm_blockBranchComplexCoefficient h m hm s ξ)
        (complexBlockWeight z h (endoMarkerBlock h))
        (fun b : NonMarkerBlock h ↦ complexBlockWeight z h b.1)

theorem analyticAt_uniformBlockBranch (h : List A) (m : BlockBranchCoefficients h)
    (hm : ∀ s ξ u v, (m s ξ u v : ℝ) ∈ Icc (0 : ℝ) 1)
    (z : A → ℂ)
    (hz : Sierpinski.finiteL1Norm
      (fun c : NonMarkerBlock h ↦ complexBlockWeight z h c.1) < 1) :
    AnalyticAt ℂ (uniformBlockBranch h m hm) z := by
  classical
  apply AnalyticAt.fun_const_smul
  apply Finset.analyticAt_fun_sum
  intro s _
  apply Finset.analyticAt_fun_sum
  intro ξ _
  have hξ : AnalyticAt ℂ (fun u : A → ℂ ↦ Sierpinski.finWordMonomial u ξ) z := by
    apply Finset.analyticAt_fun_prod
    intro i _
    exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : A ↦ ℂ) (ξ i)).analyticAt z
  apply hξ.fun_smul
  exact Sierpinski.analyticAt_uniformWordBranch _ _
    (fun u ↦ complexBlockWeight u h (endoMarkerBlock h))
    (fun u ↦ fun b : NonMarkerBlock h ↦ complexBlockWeight u h b.1) z
    (analyticAt_complexBlockWeight h (endoMarkerBlock h) z)
    (AnalyticAt.pi fun b ↦ analyticAt_complexBlockWeight h b.1 z) hz

variable [Nonempty A]

theorem uniformWordBranch_block_ofReal (h : List A) (m : BlockBranchCoefficients h)
    (hm : ∀ s ξ u v, (m s ξ u v : ℝ) ∈ Icc (0 : ℝ) 1)
    (p : A → ℝ) (hp : ∀ a, 0 < p a) (hp1 : ∑ a, p a = 1)
    (s : Fin h.length) (ξ : Fin (s : ℕ) → A) (u : List (NonMarkerBlock h)) :
    Sierpinski.uniformWordBranch (blockBranchComplexCoefficient h m s ξ)
      (norm_blockBranchComplexCoefficient h m hm s ξ)
      (complexBlockWeight (fun a ↦ (p a : ℂ)) h (endoMarkerBlock h))
      (fun b : NonMarkerBlock h ↦ complexBlockWeight (fun a ↦ (p a : ℂ)) h b.1) u =
    (oneMarkerBranch (endoMarkerBlock h) (m s ξ) (blockWeight p h.length)
      (gapOfSubtypeList h u) : ℂ) := by
  rw [Sierpinski.uniformWordBranch_apply _ _ _ _
    (finiteL1Norm_nonMarkerBlock_ofReal_lt_one p hp hp1 h)]
  rw [complexBlockWeight_ofReal]
  unfold oneMarkerBranch
  rw [Complex.ofReal_mul, Complex.ofReal_tsum]
  congr 1
  rw [← (nonMarkerListEquivGap h).tsum_eq
    (fun v : GapWords (endoMarkerBlock h) ↦
      ((wordWeight (blockWeight p h.length) v.1 *
        (m s ξ (gapOfSubtypeList h u).1 v.1 : ℝ) : ℝ) : ℂ))]
  apply tsum_congr
  intro v
  rw [← complexWordWeight_gapOfSubtypeList]
  have hweight : complexBlockWeight (fun a ↦ (p a : ℂ)) h =
      (fun c ↦ (blockWeight p h.length c : ℂ)) := funext (complexBlockWeight_ofReal p h)
  rw [hweight, complexWordWeight_ofReal]
  simp only [complexBlockWeight_ofReal, complexWordWeight_ofReal, Complex.ofReal_mul,
    blockBranchComplexCoefficient, Complex.ofReal_ratCast]
  rfl

theorem uniformBlockBranch_ofReal (h : List A) (m : BlockBranchCoefficients h)
    (hm : ∀ s ξ u v, (m s ξ u v : ℝ) ∈ Icc (0 : ℝ) 1)
    (p : A → ℝ) (hp : ∀ a, 0 < p a) (hp1 : ∑ a, p a = 1)
    (u : List (NonMarkerBlock h)) :
    uniformBlockBranch h m hm (fun a ↦ (p a : ℂ)) u =
      (blockMarkerBranch h.length (endoMarkerBlock h) m p (gapOfSubtypeList h u) : ℂ) := by
  simp only [uniformBlockBranch, BoundedContinuousFunction.smul_apply,
    BoundedContinuousFunction.sum_apply, smul_eq_mul,
    uniformWordBranch_block_ofReal h m hm p hp hp1, finWordMonomial_ofReal,
    blockMarkerBranch, Complex.ofReal_div, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_natCast, div_eq_mul_inv, mul_comm]
  norm_cast
  simp only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast]

end IndependentZeroBlocks
