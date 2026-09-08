import SierpinskiFormal.WeakContinuousMapConvergence
import Mathlib.Analysis.Normed.Module.HahnBanach

set_option autoImplicit false

namespace IndependentZeroBlocks

open Filter Set Topology

private theorem max_abs_add_abs_sub (a c : ℝ) :
    max |a + c| |a - c| = |a| + |c| := by
  apply le_antisymm
  · exact max_le (abs_add_le a c) (abs_sub a c)
  · by_cases ha : 0 ≤ a
    · by_cases hc : 0 ≤ c
      · rw [(abs_add_eq_add_abs_iff a c).2 (Or.inl ⟨ha, hc⟩)]
        exact le_max_left _ _
      · have hc' : c ≤ 0 := le_of_not_ge hc
        have heq : |a - c| = |a| + |c| := by
          rw [sub_eq_add_neg,
            (abs_add_eq_add_abs_iff a (-c)).2 (Or.inl ⟨ha, neg_nonneg.mpr hc'⟩),
            abs_neg]
        rw [← heq]
        exact le_max_right _ _
    · have ha' : a ≤ 0 := le_of_not_ge ha
      by_cases hc : 0 ≤ c
      · have heq : |a - c| = |a| + |c| := by
          rw [sub_eq_add_neg,
            (abs_add_eq_add_abs_iff a (-c)).2
              (Or.inr ⟨ha', neg_nonpos.mpr hc⟩), abs_neg]
        rw [← heq]
        exact le_max_right _ _
      · have hc' : c ≤ 0 := le_of_not_ge hc
        rw [(abs_add_eq_add_abs_iff a c).2 (Or.inr ⟨ha', hc'⟩)]
        exact le_max_left _ _

section Nonempty

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]

private theorem norm_continuousMap_const (c : ℝ) :
    ‖ContinuousMap.const X c‖ = |c| := by
  apply le_antisymm
  · apply (ContinuousMap.norm_le_of_nonempty
      (f := ContinuousMap.const X c)).2
    intro x
    simp
  · obtain ⟨x⟩ := ‹Nonempty X›
    simpa using ContinuousMap.norm_coe_le_norm (ContinuousMap.const X c) x

private def orderUnitEmbedding :
    (C(X, ℝ) × ℝ) →ₗ[ℝ] (C(X, ℝ) × C(X, ℝ)) :=
  { toFun := fun z ↦
      (z.1 + ContinuousMap.const X z.2,
        -z.1 + ContinuousMap.const X z.2)
    map_add' := by
      intro z w
      ext x <;> simp <;> ring
    map_smul' := by
      intro r z
      ext x <;> simp }

omit [CompactSpace X] in
private theorem orderUnitEmbedding_injective :
    Function.Injective (orderUnitEmbedding (X := X)) := by
  intro z w h
  obtain ⟨x₀⟩ := ‹Nonempty X›
  apply Prod.ext
  · apply ContinuousMap.ext
    intro x
    have h₁ := congrArg (fun q ↦ q.1 x) h
    have h₂ := congrArg (fun q ↦ q.2 x) h
    simp [orderUnitEmbedding] at h₁ h₂
    linarith
  · have h₁ := congrArg (fun q ↦ q.1 x₀) h
    have h₂ := congrArg (fun q ↦ q.2 x₀) h
    simp [orderUnitEmbedding] at h₁ h₂
    linarith

private theorem norm_orderUnitEmbedding (z : C(X, ℝ) × ℝ) :
    ‖orderUnitEmbedding (X := X) z‖ = ‖z.1‖ + |z.2| := by
  apply le_antisymm
  · rw [Prod.norm_def]
    apply max_le
    · simpa [orderUnitEmbedding, norm_continuousMap_const (X := X)] using
        norm_add_le z.1 (ContinuousMap.const X z.2)
    · simpa [orderUnitEmbedding, norm_continuousMap_const (X := X)] using
        norm_add_le (-z.1) (ContinuousMap.const X z.2)
  · have hz : ‖z.1‖ ≤ ‖orderUnitEmbedding (X := X) z‖ - |z.2| := by
      apply (ContinuousMap.norm_le_of_nonempty (f := z.1)).2
      intro x
      have hpoint : ‖z.1 x‖ + |z.2| ≤ ‖orderUnitEmbedding (X := X) z‖ := by
        rw [Prod.norm_def]
        calc
          ‖z.1 x‖ + |z.2| = max |z.1 x + z.2| |z.1 x - z.2| :=
            (max_abs_add_abs_sub (z.1 x) z.2).symm
          _ ≤ max
              ‖z.1 + ContinuousMap.const X z.2‖
              ‖-z.1 + ContinuousMap.const X z.2‖ := by
            apply max_le_max
            · simpa using ContinuousMap.norm_coe_le_norm
                (z.1 + ContinuousMap.const X z.2) x
            · have heq : |-z.1 x + z.2| = |z.1 x - z.2| := by
                rw [show -z.1 x + z.2 = -(z.1 x - z.2) by ring, abs_neg]
              rw [← heq]
              simpa using ContinuousMap.norm_coe_le_norm
                (-z.1 + ContinuousMap.const X z.2) x
      linarith
    linarith

/-- On a nonempty compact space, every continuous functional on the real
continuous functions is a difference of two positive continuous
functionals. -/
theorem exists_sub_positive_continuousLinearMap_of_nonempty
    (phi : C(X, ℝ) →L[ℝ] ℝ) :
    ∃ phiPos phiNeg : C(X, ℝ) →L[ℝ] ℝ,
      (∀ f : C(X, ℝ), 0 ≤ f → 0 ≤ phiPos f) ∧
      (∀ f : C(X, ℝ), 0 ≤ f → 0 ≤ phiNeg f) ∧
      phi = phiPos - phiNeg := by
  letI : NormedAddCommGroup (C(X, ℝ) × C(X, ℝ)) := inferInstance
  letI : NormedSpace ℝ (C(X, ℝ) × C(X, ℝ)) := inferInstance
  let T := orderUnitEmbedding (X := X)
  have hT : Function.Injective T := orderUnitEmbedding_injective (X := X)
  let P : Subspace ℝ (C(X, ℝ) × C(X, ℝ)) := LinearMap.range T
  let equiv : (C(X, ℝ) × ℝ) ≃ₗ[ℝ] P :=
    LinearEquiv.ofInjective T hT
  let M : ℝ := ‖phi‖
  let base : (C(X, ℝ) × ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun z ↦ phi z.1 + M * z.2
      map_add' := by intro z w; simp; ring
      map_smul' := by intro r z; simp; ring }
  let onRangeLinear : P →ₗ[ℝ] ℝ :=
    base.comp equiv.symm.toLinearMap
  have honRangeBound (z : P) :
      ‖onRangeLinear z‖ ≤ M * ‖z‖ := by
    let w : C(X, ℝ) × ℝ := equiv.symm z
    have hphi : ‖phi w.1‖ ≤ M * ‖w.1‖ := phi.le_opNorm w.1
    have hM : 0 ≤ M := norm_nonneg phi
    calc
      ‖onRangeLinear z‖ = |phi w.1 + M * w.2| := by
        simp [onRangeLinear, base, w, Real.norm_eq_abs]
      _ ≤ |phi w.1| + |M * w.2| := abs_add_le _ _
      _ = ‖phi w.1‖ + M * |w.2| := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hM]
      _ ≤ M * ‖w.1‖ + M * |w.2| := add_le_add hphi le_rfl
      _ = M * (‖w.1‖ + |w.2|) := by ring
      _ = M * ‖T w‖ := by rw [norm_orderUnitEmbedding]
      _ = M * ‖z‖ := by
        have he : equiv w = z := equiv.apply_symm_apply z
        change M * ‖(T w : C(X, ℝ) × C(X, ℝ))‖ = M * ‖(z :
          C(X, ℝ) × C(X, ℝ))‖
        rw [show T w = (z : C(X, ℝ) × C(X, ℝ)) from congrArg Subtype.val he]
  let onRange : StrongDual ℝ P :=
    onRangeLinear.mkContinuous M honRangeBound
  have honRangeNorm : ‖onRange‖ ≤ M := by
    exact onRangeLinear.mkContinuous_norm_le (norm_nonneg phi) honRangeBound
  obtain ⟨Psi, hPsiExt, hPsiNorm⟩ := exists_extension_norm_eq P onRange
  have hPsiNormLe : ‖Psi‖ ≤ M := hPsiNorm.le.trans honRangeNorm
  let unitPair : C(X, ℝ) × C(X, ℝ) := (1, 1)
  have hunitMem : unitPair ∈ P := by
    refine ⟨(0, 1), ?_⟩
    ext x <;> simp [T, orderUnitEmbedding, unitPair]
  let unitInRange : P := ⟨unitPair, hunitMem⟩
  have hPsiUnit : Psi unitPair = M := by
    rw [hPsiExt unitInRange]
    change onRangeLinear unitInRange = M
    let w := equiv.symm unitInRange
    have he : T w = unitPair := by
      exact congrArg Subtype.val (equiv.apply_symm_apply unitInRange)
    have hw : w = (0, 1) := hT (by simpa [T, unitPair, orderUnitEmbedding] using he)
    simp [onRangeLinear, base, w, hw, M]
  let phiPos : C(X, ℝ) →L[ℝ] ℝ :=
    Psi.comp (ContinuousLinearMap.inl ℝ C(X, ℝ) C(X, ℝ))
  let phiNeg : C(X, ℝ) →L[ℝ] ℝ :=
    Psi.comp (ContinuousLinearMap.inr ℝ C(X, ℝ) C(X, ℝ))
  have hpositive (side : Bool) (f : C(X, ℝ)) (hf : 0 ≤ f) :
      0 ≤ if side then phiNeg f else phiPos f := by
    by_cases hzero : f = 0
    · simp [hzero]
    · let r : ℝ := ‖f‖
      have hr : 0 < r := norm_pos_iff.mpr hzero
      let a : C(X, ℝ) × C(X, ℝ) :=
        if side then (1, 1 - r⁻¹ • f) else (1 - r⁻¹ • f, 1)
      have hnormFirst : ‖1 - r⁻¹ • f‖ ≤ 1 := by
        apply (ContinuousMap.norm_le_of_nonempty
          (f := 1 - r⁻¹ • f)).2
        intro x
        rw [Real.norm_eq_abs, abs_le]
        constructor
        · have hfx : 0 ≤ f x := hf x
          have hfxr : f x ≤ r := ContinuousMap.apply_le_norm f x
          simp only [ContinuousMap.sub_apply, ContinuousMap.one_apply,
            ContinuousMap.smul_apply, smul_eq_mul]
          have hdiv : r⁻¹ * f x ≤ 1 := by
            rw [inv_mul_eq_div]
            exact (div_le_one hr).2 hfxr
          linarith
        · have hfx : 0 ≤ f x := hf x
          simp only [ContinuousMap.sub_apply, ContinuousMap.one_apply,
            ContinuousMap.smul_apply, smul_eq_mul]
          have : 0 ≤ r⁻¹ * f x := mul_nonneg (le_of_lt (inv_pos.mpr hr)) hfx
          linarith
      have haNorm : ‖a‖ ≤ 1 := by
        simp only [a]
        split_ifs <;> simp [Prod.norm_def, hnormFirst]
      have hPsiA : Psi a ≤ M := by
        calc
          Psi a ≤ ‖Psi a‖ := Real.le_norm_self _
          _ ≤ ‖Psi‖ * ‖a‖ := Psi.le_opNorm a
          _ ≤ M * ‖a‖ := mul_le_mul_of_nonneg_right hPsiNormLe (norm_nonneg a)
          _ ≤ M * 1 := mul_le_mul_of_nonneg_left haNorm (norm_nonneg phi)
          _ = M := mul_one M
      have hvalue : Psi a = M - r⁻¹ * (if side then phiNeg f else phiPos f) := by
        cases side with
        | false =>
            simp only [Bool.false_eq_true, ↓reduceIte, a, phiPos]
            rw [← hPsiUnit]
            have ha : (1 - r⁻¹ • f, 1) =
                unitPair - r⁻¹ • (f, 0) := by
              ext x <;> simp [unitPair]
            rw [ha, Psi.map_sub, Psi.map_smul]
            rfl
        | true =>
            simp only [↓reduceIte, a, phiNeg]
            rw [← hPsiUnit]
            have ha : (1, 1 - r⁻¹ • f) =
                unitPair - r⁻¹ • (0, f) := by
              ext x <;> simp [unitPair]
            rw [ha, Psi.map_sub, Psi.map_smul]
            rfl
      rw [hvalue] at hPsiA
      have hmul : 0 ≤ r⁻¹ * (if side then phiNeg f else phiPos f) := by
        linarith
      exact nonneg_of_mul_nonneg_right hmul (inv_pos.mpr hr)
  refine ⟨phiPos, phiNeg, ?_, ?_, ?_⟩
  · exact hpositive false
  · exact hpositive true
  · ext f
    let rangePoint : P := equiv (f, 0)
    have hext := hPsiExt rangePoint
    have hrange : (rangePoint : C(X, ℝ) × C(X, ℝ)) = (f, -f) := by
      change T (f, 0) = (f, -f)
      ext x <;> simp [T, orderUnitEmbedding]
    have hon : onRange rangePoint = phi f := by
      change base (equiv.symm rangePoint) = phi f
      rw [show equiv.symm rangePoint = (f, 0) from equiv.symm_apply_apply (f, 0)]
      simp [base]
    rw [hrange, hon] at hext
    change phi f = Psi (f, 0) - Psi (0, f)
    calc
      phi f = Psi (f, -f) := hext.symm
      _ = Psi ((f, 0) - (0, f)) := by
        congr 1
        ext <;> simp
      _ = Psi (f, 0) - Psi (0, f) := Psi.map_sub _ _

end Nonempty

/-- Every continuous functional on real continuous functions over a compact
space is a difference of two positive continuous functionals. The empty
space is handled separately, where the function space is trivial. -/
theorem exists_sub_positive_continuousLinearMap
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (phi : C(X, ℝ) →L[ℝ] ℝ) :
    ∃ phiPos phiNeg : C(X, ℝ) →L[ℝ] ℝ,
      (∀ f : C(X, ℝ), 0 ≤ f → 0 ≤ phiPos f) ∧
      (∀ f : C(X, ℝ), 0 ≤ f → 0 ≤ phiNeg f) ∧
      phi = phiPos - phiNeg := by
  cases isEmpty_or_nonempty X with
  | inr hX =>
      letI : Nonempty X := hX
      exact exists_sub_positive_continuousLinearMap_of_nonempty phi
  | inl hX =>
      letI : IsEmpty X := hX
      refine ⟨0, 0, ?_, ?_, ?_⟩
      · intro f hf
        simp
      · intro f hf
        simp
      · ext f
        have hf : f = 0 := by
          apply ContinuousMap.ext
          intro x
          exact isEmptyElim x
        simp [hf]

/-- Uniformly norm-bounded pointwise convergence to a continuous limit on
a compact Hausdorff space is weak convergence against every real continuous
linear functional. -/
theorem tendsto_functional_continuousMap_of_pointwise
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (phi : C(X, ℝ) →L[ℝ] ℝ)
    (u : ℕ → C(X, ℝ)) (v : C(X, ℝ)) (C : ℝ)
    (hbound : ∀ n, ‖u n‖ ≤ C)
    (hpointwise : ∀ x, Tendsto (fun n ↦ u n x) atTop (nhds (v x))) :
    Tendsto (fun n ↦ phi (u n)) atTop (nhds (phi v)) := by
  obtain ⟨phiPos, phiNeg, hphiPos, hphiNeg, rfl⟩ :=
    exists_sub_positive_continuousLinearMap phi
  exact tendsto_sub_positiveFunctionals_continuousMap_of_pointwise
    phiPos phiNeg hphiPos hphiNeg u v C hbound hpointwise

end IndependentZeroBlocks
