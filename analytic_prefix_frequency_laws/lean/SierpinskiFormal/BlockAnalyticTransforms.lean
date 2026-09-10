import SierpinskiFormal.UniformBlockBranchAnalytic

/-! # Analytic mixed moments and joint exponential transforms of block branches -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter Set Topology
open scoped BigOperators BoundedContinuousFunction
namespace IndependentZeroBlocks

variable {A J : Type*} [Fintype A] [DecidableEq A]
  [TopologicalSpace A] [DiscreteTopology A] [Fintype J]

def blockMixtureFunctional (h : List A) (z : A → ℂ) :
    (List (NonMarkerBlock h) →ᵇ ℂ) →L[ℂ] ℂ :=
  Sierpinski.wordMixtureFunctional (complexBlockWeight z h (endoMarkerBlock h))
    (fun b : NonMarkerBlock h ↦ complexBlockWeight z h b.1)

theorem analyticAt_blockMixture_test (h : List A)
    (f : (A → ℂ) → (List (NonMarkerBlock h) →ᵇ ℂ)) (z : A → ℂ)
    (hz : Sierpinski.finiteL1Norm (fun b : NonMarkerBlock h ↦ complexBlockWeight z h b.1) < 1)
    (hf : AnalyticAt ℂ f z) :
    AnalyticAt ℂ (fun u ↦ blockMixtureFunctional h u (f u)) z :=
  Sierpinski.analyticAt_wordMixture_test _ _ f z
    (analyticAt_complexBlockWeight h (endoMarkerBlock h) z)
    (AnalyticAt.pi fun b ↦ analyticAt_complexBlockWeight h b.1 z) hz hf

def blockComplexMixedMoment (h : List A) (m : J → BlockBranchCoefficients h)
    (hm : ∀ j s ξ u v, (m j s ξ u v : ℝ) ∈ Icc (0 : ℝ) 1)
    (k : J → ℕ) (z : A → ℂ) : ℂ :=
  blockMixtureFunctional h z (∏ j, uniformBlockBranch h (m j) (hm j) z ^ k j)

theorem analyticAt_blockComplexMixedMoment (h : List A) (m : J → BlockBranchCoefficients h)
    (hm : ∀ j s ξ u v, (m j s ξ u v : ℝ) ∈ Icc (0 : ℝ) 1)
    (k : J → ℕ) (z : A → ℂ)
    (hz : Sierpinski.finiteL1Norm (fun b : NonMarkerBlock h ↦ complexBlockWeight z h b.1) < 1) :
    AnalyticAt ℂ (blockComplexMixedMoment h m hm k) z := by
  apply analyticAt_blockMixture_test
  · exact hz
  · apply Finset.analyticAt_fun_prod
    intro j _
    exact (analyticAt_uniformBlockBranch h (m j) (hm j) z hz).fun_pow (k j)

def blockComplexExpTransform (h : List A) (m : J → BlockBranchCoefficients h)
    (hm : ∀ j s ξ u v, (m j s ξ u v : ℝ) ∈ Icc (0 : ℝ) 1)
    (z : A → ℂ) (t : J → ℂ) : ℂ :=
  blockMixtureFunctional h z
    (NormedSpace.exp (∑ j, t j • uniformBlockBranch h (m j) (hm j) z))

/-- Joint local holomorphy in the complex weight parameters and every complex
transform parameter; the restriction is solely on the nonmarker weight mass. -/
theorem analyticAt_blockComplexExpTransform (h : List A) (m : J → BlockBranchCoefficients h)
    (hm : ∀ j s ξ u v, (m j s ξ u v : ℝ) ∈ Icc (0 : ℝ) 1)
    (z : A → ℂ) (t : J → ℂ)
    (hz : Sierpinski.finiteL1Norm (fun b : NonMarkerBlock h ↦ complexBlockWeight z h b.1) < 1) :
    AnalyticAt ℂ (fun zt : (A → ℂ) × (J → ℂ) ↦ blockComplexExpTransform h m hm zt.1 zt.2)
      (z, t) := by
  have hfst : AnalyticAt ℂ (Prod.fst : (A → ℂ) × (J → ℂ) → (A → ℂ)) (z, t) := analyticAt_fst
  have hsnd : AnalyticAt ℂ (Prod.snd : (A → ℂ) × (J → ℂ) → (J → ℂ)) (z, t) := analyticAt_snd
  apply Sierpinski.analyticAt_wordMixture_test
    (fun zt : (A → ℂ) × (J → ℂ) ↦ complexBlockWeight zt.1 h (endoMarkerBlock h))
    (fun zt ↦ fun b : NonMarkerBlock h ↦ complexBlockWeight zt.1 h b.1)
  · simpa only [Function.comp_def] using
      (analyticAt_complexBlockWeight h (endoMarkerBlock h) z).comp hfst
  · simpa only [Function.comp_def] using
      (AnalyticAt.pi fun b : NonMarkerBlock h ↦ analyticAt_complexBlockWeight h b.1 z).comp hfst
  · exact hz
  · apply (NormedSpace.exp_analytic (𝕂 := ℂ) _).comp
    apply Finset.analyticAt_fun_sum
    intro j _
    have ht : AnalyticAt ℂ (fun zt : (A → ℂ) × (J → ℂ) ↦ zt.2 j) (z, t) := by
      simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : J ↦ ℂ) j).analyticAt t).comp hsnd
    have hBj : AnalyticAt ℂ (fun zt : (A → ℂ) × (J → ℂ) ↦
        uniformBlockBranch h (m j) (hm j) zt.1) (z, t) := by
      simpa only [Function.comp_def] using
        (analyticAt_uniformBlockBranch h (m j) (hm j) z hz).comp
          (f := Prod.fst) (x := (z, t)) hfst
    exact ht.fun_smul hBj

def normalizedBlockBranch (h : List A) (m : BlockBranchCoefficients h)
    (hm : ∀ s ξ u v, (m s ξ u v : ℝ) ∈ Icc (0 : ℝ) 1)
    (p : A → ℝ) (u : GapWords (endoMarkerBlock h)) : ℝ :=
  (uniformBlockBranch h m hm (normalizedComplexWeights (complexifyWeightVector p))
    (subtypeListOfGap h u)).re

def normalizedBlockMixedMoment (h : List A) (m : J → BlockBranchCoefficients h)
    (hm : ∀ j s ξ u v, (m j s ξ u v : ℝ) ∈ Icc (0 : ℝ) 1)
    (k : J → ℕ) (p : A → ℝ) : ℝ :=
  (blockComplexMixedMoment h m hm k (normalizedComplexWeights (complexifyWeightVector p))).re

variable [Nonempty A]

theorem analyticAt_normalizedBlockBranch (h : List A) (m : BlockBranchCoefficients h)
    (hm : ∀ s ξ u v, (m s ξ u v : ℝ) ∈ Icc (0 : ℝ) 1)
    (p : A → ℝ) (hp : ∀ a, 0 < p a) (u : GapWords (endoMarkerBlock h)) :
    AnalyticAt ℝ (fun r ↦ normalizedBlockBranch h m hm r u) p := by
  have hz := finiteL1Norm_nonMarkerBlock_ofReal_lt_one (normalizedRealWeights p)
    (normalizedRealWeights_pos p hp) (sum_normalizedRealWeights p hp) h
  have hB := analyticAt_uniformBlockBranch h m hm
    (complexifyWeightVector (normalizedRealWeights p)) hz
  rw [← normalizedComplexWeights_complexify] at hB
  have he := ((BoundedContinuousFunction.evalCLM ℂ (subtypeListOfGap h u)).analyticAt _).comp
    (hB.comp (analyticAt_normalizedComplexWeights _ (complex_totalWeight_ne_zero p hp)))
  exact analyticAt_realPart_complexify _ p he

theorem normalizedBlockBranch_eq (h : List A) (m : BlockBranchCoefficients h)
    (hm : ∀ s ξ u v, (m s ξ u v : ℝ) ∈ Icc (0 : ℝ) 1)
    (p : A → ℝ) (hp : ∀ a, 0 < p a) (u : GapWords (endoMarkerBlock h)) :
    normalizedBlockBranch h m hm p u =
      blockMarkerBranch h.length (endoMarkerBlock h) m (normalizedRealWeights p) u := by
  unfold normalizedBlockBranch
  rw [normalizedComplexWeights_complexify]
  change (uniformBlockBranch h m hm (fun a ↦ (normalizedRealWeights p a : ℂ))
    (subtypeListOfGap h u)).re = _
  rw [uniformBlockBranch_ofReal h m hm _
    (normalizedRealWeights_pos p hp) (sum_normalizedRealWeights p hp)]
  have hu : gapOfSubtypeList h (subtypeListOfGap h u) = u := (nonMarkerListEquivGap h).apply_symm_apply u
  simp only [hu, Complex.ofReal_re]

theorem analyticAt_normalizedBlockMixedMoment (h : List A) (m : J → BlockBranchCoefficients h)
    (hm : ∀ j s ξ u v, (m j s ξ u v : ℝ) ∈ Icc (0 : ℝ) 1)
    (k : J → ℕ) (p : A → ℝ) (hp : ∀ a, 0 < p a) :
    AnalyticAt ℝ (normalizedBlockMixedMoment h m hm k) p := by
  have hz := finiteL1Norm_nonMarkerBlock_ofReal_lt_one (normalizedRealWeights p)
    (normalizedRealWeights_pos p hp) (sum_normalizedRealWeights p hp) h
  have he := analyticAt_blockComplexMixedMoment h m hm k
    (complexifyWeightVector (normalizedRealWeights p)) hz
  rw [← normalizedComplexWeights_complexify] at he
  exact analyticAt_realPart_complexify _ p
    (he.comp (analyticAt_normalizedComplexWeights _ (complex_totalWeight_ne_zero p hp)))

end IndependentZeroBlocks
