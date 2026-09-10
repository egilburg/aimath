import SierpinskiFormal.RationalBoundaryDensityAnalytic

/-! # Linear closure of actual analytic Bernoulli word means

The analytic function is always tied to the actual normalized word-length
Cesaro mean. This file supplies only finite linear closure, not any closure
of recognizable scalar series under zero/nonzero Booleanization.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
namespace IndependentZeroBlocks

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
variable [TopologicalSpace A] [DiscreteTopology A]

def HasAnalyticWordMean (f : BoundedWordFunction A) : Prop :=
  ∃ d : (A → ℝ) → ℝ,
    (∀ p : A → ℝ, (∀ a, 0 < p a) → AnalyticAt ℝ d p) ∧
    ∀ p : A → ℝ, (∀ a, 0 < p a) →
      Tendsto (realCesaroMean (fun n ↦ weightedWordExtensionAverage
        (normalizedRealWeights p) f n [])) atTop (𝓝 (d p))

theorem weightedWordExtensionAverage_add_linear (p : A → ℝ)
    (f g : BoundedWordFunction A) (n : ℕ) (z : List A) :
    weightedWordExtensionAverage p (f + g) n z =
      weightedWordExtensionAverage p f n z + weightedWordExtensionAverage p g n z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => simp only [weightedWordExtensionAverage, ih, mul_add, Finset.sum_add_distrib]

theorem weightedWordExtensionAverage_smul_linear (p : A → ℝ)
    (c : ℝ) (f : BoundedWordFunction A) (n : ℕ) (z : List A) :
    weightedWordExtensionAverage p (c • f) n z =
      c * weightedWordExtensionAverage p f n z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
      simp only [weightedWordExtensionAverage, ih, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring

theorem weightedWordExtensionAverage_const_linear (p : A → ℝ)
    (hp : ∑ a, p a = 1) (c : ℝ) (n : ℕ) (z : List A) :
    weightedWordExtensionAverage p (BoundedContinuousFunction.const (List A) c) n z = c := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => simp only [weightedWordExtensionAverage, ih, ← Finset.sum_mul, hp, one_mul]

theorem realCesaroMean_add_linear (f g : ℕ → ℝ) (N : ℕ) :
    realCesaroMean (fun n ↦ f n + g n) N = realCesaroMean f N + realCesaroMean g N := by
  simp [realCesaroMean, Finset.sum_add_distrib, add_div]

theorem realCesaroMean_mul_linear (c : ℝ) (f : ℕ → ℝ) (N : ℕ) :
    realCesaroMean (fun n ↦ c * f n) N = c * realCesaroMean f N := by
  simp [realCesaroMean, ← Finset.mul_sum, mul_div_assoc]

theorem hasAnalyticWordMean_const (c : ℝ) :
    HasAnalyticWordMean (BoundedContinuousFunction.const (List A) c) := by
  refine ⟨fun _ ↦ c, fun _ _ ↦ analyticAt_const, ?_⟩
  intro p hp
  simp_rw [weightedWordExtensionAverage_const_linear _ (sum_normalizedRealWeights p hp)]
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  simp [realCesaroMean, ne_of_gt hN, mul_div_cancel_left₀]

theorem HasAnalyticWordMean.add {f g : BoundedWordFunction A}
    (hf : HasAnalyticWordMean f) (hg : HasAnalyticWordMean g) :
    HasAnalyticWordMean (f + g) := by
  obtain ⟨d, hd, hdl⟩ := hf
  obtain ⟨e, he, hel⟩ := hg
  refine ⟨fun p ↦ d p + e p, fun p hp ↦ (hd p hp).fun_add (he p hp), ?_⟩
  intro p hp
  change Tendsto (fun N ↦ realCesaroMean (fun n ↦
    weightedWordExtensionAverage (normalizedRealWeights p) (f + g) n []) N)
    atTop (𝓝 (d p + e p))
  simpa only [weightedWordExtensionAverage_add_linear, realCesaroMean_add_linear] using
    (hdl p hp).add (hel p hp)

theorem HasAnalyticWordMean.smul {f : BoundedWordFunction A}
    (hf : HasAnalyticWordMean f) (c : ℝ) : HasAnalyticWordMean (c • f) := by
  obtain ⟨d, hd, hdl⟩ := hf
  refine ⟨fun p ↦ c * d p, fun p hp ↦ analyticAt_const.fun_mul (hd p hp), ?_⟩
  intro p hp
  change Tendsto (fun N ↦ realCesaroMean (fun n ↦
    weightedWordExtensionAverage (normalizedRealWeights p) (c • f) n []) N)
    atTop (𝓝 (c * d p))
  simpa only [weightedWordExtensionAverage_smul_linear, realCesaroMean_mul_linear] using
    (hdl p hp).const_mul c

theorem hasAnalyticWordMean_finset_sum {J : Type*} (s : Finset J)
    (f : J → BoundedWordFunction A) (hf : ∀ j ∈ s, HasAnalyticWordMean (f j)) :
    HasAnalyticWordMean (∑ j ∈ s, f j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty]
      change HasAnalyticWordMean (BoundedContinuousFunction.const (List A) 0)
      exact hasAnalyticWordMean_const 0
  | @insert j s hj ih =>
      rw [Finset.sum_insert hj]
      exact (hf j (Finset.mem_insert_self j s)).add
        (ih fun k hk ↦ hf k (Finset.mem_insert_of_mem hk))

/-- The finite linear-combination closure used after a pointwise Boolean
expansion. Its hypotheses are actual analytic means of the component words. -/
theorem hasAnalyticWordMean_of_finite_linear_combination
    {J : Type*} [Fintype J] (f : BoundedWordFunction A)
    (g : J → BoundedWordFunction A) (hg : ∀ j, HasAnalyticWordMean (g j))
    (c : ℝ) (a : J → ℝ)
    (h : ∀ w, f w = c + ∑ j, a j * g j w) : HasAnalyticWordMean f := by
  have he : f = BoundedContinuousFunction.const (List A) c + ∑ j, a j • g j := by
    ext w
    simpa only [BoundedContinuousFunction.add_apply,
      BoundedContinuousFunction.const_apply, BoundedContinuousFunction.sum_apply,
      BoundedContinuousFunction.smul_apply, smul_eq_mul] using h w
  rw [he]
  exact (hasAnalyticWordMean_const c).add
    (hasAnalyticWordMean_finset_sum Finset.univ (fun j ↦ a j • g j)
      (fun j _ ↦ (hg j).smul (a j)))

end IndependentZeroBlocks
