import Mathlib.Analysis.Convex.Cone.Extension
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import SierpinskiFormal.CountableWeakKrein

/-!
# Positive state representation for Bochner `L¹` functionals

This file develops the sign-doubling Hahn--Banach route.  A norming linear
isometry `E → C(K, ℝ)` turns a Bochner `L¹` functional into a positive state
on `X × (K × Bool)`.  Positivity removes the need for signed-measure variation
estimates in the subsequent countable-fiber disintegration.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace IndependentZeroBlocks

section PositiveLinearFunctional

variable {Z : Type*} [TopologicalSpace Z] [CompactSpace Z]

/-- A positive algebraic functional on the continuous real functions over a
compact space is automatically bounded by its value at one. -/
theorem positive_linearMap_continuous_bound
    (L : C(Z, ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀ F : C(Z, ℝ), 0 ≤ F → 0 ≤ L F) (F : C(Z, ℝ)) :
    ‖L F‖ ≤ L 1 * ‖F‖ := by
  have hu : F ≤ ‖F‖ • (1 : C(Z, ℝ)) := by
    intro z
    simpa using ContinuousMap.apply_le_norm F z
  have hl : -(‖F‖ • (1 : C(Z, ℝ))) ≤ F := by
    intro z
    have hz := neg_le_of_abs_le (ContinuousMap.norm_coe_le_norm F z)
    simpa using hz
  have hupper : L F ≤ L 1 * ‖F‖ := by
    have hpos : 0 ≤ (‖F‖ • (1 : C(Z, ℝ))) - F := by
      intro z
      simpa using hu z
    have h := hL ((‖F‖ • (1 : C(Z, ℝ))) - F) hpos
    rw [L.map_sub, L.map_smul] at h
    simpa [smul_eq_mul, mul_comm] using h
  have hlower : -(L 1 * ‖F‖) ≤ L F := by
    have hpos : 0 ≤ F - (-(‖F‖ • (1 : C(Z, ℝ)))) := by
      intro z
      have hz := hl z
      simp at hz ⊢
      linarith
    have h := hL (F - (-(‖F‖ • (1 : C(Z, ℝ))))) hpos
    rw [L.map_sub, L.map_neg, L.map_smul] at h
    simp [smul_eq_mul, mul_comm] at h
    linarith
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨hlower, hupper⟩

/-- Package a positive algebraic functional as a continuous linear map. -/
noncomputable def positiveLinearMapToContinuous
    (L : C(Z, ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀ F : C(Z, ℝ), 0 ≤ F → 0 ≤ L F) :
    C(Z, ℝ) →L[ℝ] ℝ :=
  L.mkContinuous (L 1) (positive_linearMap_continuous_bound L hL)

@[simp] theorem positiveLinearMapToContinuous_apply
    (L : C(Z, ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀ F : C(Z, ℝ), 0 ≤ F → 0 ≤ L F)
    (F : C(Z, ℝ)) :
    positiveLinearMapToContinuous L hL F = L F := rfl

end PositiveLinearFunctional

section SignedPairing

variable {X K E : Type*} [TopologicalSpace X] [CompactSpace X]
  [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The two signs used to make positivity encode the norming inequality. -/
def boolSign (s : Bool) : ℝ := if s then -1 else 1

theorem continuous_boolSign : Continuous boolSign :=
  continuous_of_discreteTopology

/-- The signed evaluation of a continuous `E`-valued map through a norming
embedding into `C(K,ℝ)`. -/
noncomputable def signedPairingContinuousMap
    (J : E →ₗᵢ[ℝ] C(K, ℝ)) (g : C(X, E)) :
    C(X × (K × Bool), ℝ) := by
  refine ⟨fun z => boolSign z.2.2 * J (g z.1) z.2.1, ?_⟩
  have hfun : Continuous (fun z : X × (K × Bool) => J (g z.1)) :=
    J.continuous.comp (g.continuous.comp continuous_fst)
  have harg : Continuous (fun z : X × (K × Bool) => z.2.1) :=
    continuous_fst.comp continuous_snd
  have heval : Continuous
      (fun z : X × (K × Bool) => J (g z.1) z.2.1) :=
    ContinuousEval.continuous_eval.comp (hfun.prodMk harg)
  have hsign : Continuous
      (fun z : X × (K × Bool) => boolSign z.2.2) :=
    continuous_boolSign.comp (continuous_snd.comp continuous_snd)
  exact hsign.mul heval

omit [CompactSpace X] in
@[simp] theorem signedPairingContinuousMap_apply
    (J : E →ₗᵢ[ℝ] C(K, ℝ)) (g : C(X, E))
    (x : X) (k : K) (s : Bool) :
    signedPairingContinuousMap J g (x, k, s) =
      boolSign s * J (g x) k := rfl

/-- The map `(a,g) ↦ a(x) + sign(s) * J(g(x))(k)` whose range is the
subspace on which the normalized `L¹` functional is initially defined. -/
noncomputable def signedPairingRangeMap
    (J : E →ₗᵢ[ℝ] C(K, ℝ)) :
    (C(X, ℝ) × C(X, E)) →ₗ[ℝ] C(X × (K × Bool), ℝ) where
  toFun z :=
    z.1.comp ⟨Prod.fst, continuous_fst⟩ + signedPairingContinuousMap J z.2
  map_add' z w := by
    ext p
    by_cases hs : p.2.2 = true <;>
      simp [hs, signedPairingContinuousMap, boolSign] <;> ring
  map_smul' c z := by
    ext p
    by_cases hs : p.2.2 = true <;>
      simp [hs, signedPairingContinuousMap, boolSign]

omit [CompactSpace X] in
@[simp] theorem signedPairingRangeMap_apply
    (J : E →ₗᵢ[ℝ] C(K, ℝ)) (z : C(X, ℝ) × C(X, E))
    (x : X) (k : K) (s : Bool) :
    signedPairingRangeMap J z (x, k, s) =
      z.1 x + boolSign s * J (z.2 x) k := rfl

omit [CompactSpace X] in
/-- Sign doubling makes the range parametrization injective. -/
theorem signedPairingRangeMap_injective [Nonempty K]
    (J : E →ₗᵢ[ℝ] C(K, ℝ)) :
    Function.Injective (signedPairingRangeMap (X := X) J) := by
  intro z w h
  have ha : z.1 = w.1 := by
    apply ContinuousMap.ext
    intro x
    obtain ⟨k⟩ := ‹Nonempty K›
    have hp := congrArg
      (fun F : C(X × (K × Bool), ℝ) => F (x, k, false)) h
    have hm := congrArg
      (fun F : C(X × (K × Bool), ℝ) => F (x, k, true)) h
    simp [signedPairingRangeMap_apply, boolSign] at hp hm
    linarith
  have hg : z.2 = w.2 := by
    apply ContinuousMap.ext
    intro x
    apply J.injective
    apply ContinuousMap.ext
    intro k
    have hp := congrArg
      (fun F : C(X × (K × Bool), ℝ) => F (x, k, false)) h
    have hax := DFunLike.congr_fun ha x
    simp [signedPairingRangeMap_apply, boolSign] at hp
    linarith
  exact Prod.ext ha hg

omit [CompactSpace X] in
/-- Nonnegativity of the sign-doubled function says pointwise that its scalar
part dominates the norm of its vector part. -/
theorem norm_le_fst_of_signedPairingRangeMap_nonneg [Nonempty K]
    (J : E →ₗᵢ[ℝ] C(K, ℝ)) (z : C(X, ℝ) × C(X, E))
    (hz : 0 ≤ signedPairingRangeMap J z) (x : X) :
    ‖z.2 x‖ ≤ z.1 x := by
  rw [← J.norm_map]
  apply (ContinuousMap.norm_le_of_nonempty (f := J (z.2 x))).2
  intro k
  have hp := hz (x, k, false)
  have hm := hz (x, k, true)
  simp [signedPairingRangeMap_apply, boolSign] at hp hm
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith

end SignedPairing

section ContinuousL1

variable {X E : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [SecondCountableTopologyEither X E]
  {μ : Measure X} [IsFiniteMeasure μ]

/-- The `L¹` norm of the class of a continuous function is the integral of
its pointwise norm. -/
theorem norm_continuousMap_toLp_one (g : C(X, E)) :
    ‖ContinuousMap.toLp 1 μ ℝ g‖ = ∫ x, ‖g x‖ ∂μ := by
  rw [Lp.norm_def, eLpNorm_one_eq_lintegral_enorm]
  rw [lintegral_congr_ae]
  · exact (integral_norm_eq_lintegral_enorm
      g.continuous.aestronglyMeasurable).symm
  · filter_upwards
      [ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) μ g] with x hx
    rw [hx]

end ContinuousL1


section PositiveStateExtension

variable {X K E : Type*} [TopologicalSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [TopologicalSpace K] [CompactSpace K] [Nonempty K]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {μ : Measure X} [IsProbabilityMeasure μ]

noncomputable def continuousIntegralCLM : C(X, ℝ) →L[ℝ] ℝ :=
  L1.integralCLM.comp (ContinuousMap.toLp 1 μ ℝ)

omit [SecondCountableTopology X] in
@[simp] theorem continuousIntegralCLM_apply (a : C(X,ℝ)) :
    continuousIntegralCLM (μ:=μ) a = ∫ x, a x ∂μ := by
  rw [continuousIntegralCLM, ContinuousLinearMap.comp_apply, ← L1.integral_eq]
  change L1.integral (ContinuousMap.toLp 1 μ ℝ a) = _
  rw [L1.integral_eq_integral]
  exact integral_congr_ae
    (ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℝ) μ a)

noncomputable def normalizedSignedPairingBase
    (Λ : Lp E 1 μ →L[ℝ] ℝ) :
    (C(X, ℝ) × C(X, E)) →ₗ[ℝ] ℝ where
  toFun z := continuousIntegralCLM (μ:=μ) z.1 +
    ‖Λ‖⁻¹ * Λ (ContinuousMap.toLp 1 μ ℝ z.2)
  map_add' z w := by
    change continuousIntegralCLM (μ := μ) (z.1 + w.1) +
      ‖Λ‖⁻¹ * Λ (ContinuousMap.toLp 1 μ ℝ (z.2 + w.2)) = _
    rw [map_add, map_add, map_add]
    ring
  map_smul' c z := by
    change continuousIntegralCLM (μ := μ) (c • z.1) +
      ‖Λ‖⁻¹ * Λ (ContinuousMap.toLp 1 μ ℝ (c • z.2)) = _
    rw [map_smul, map_smul, map_smul]
    simp only [smul_eq_mul, RingHom.id_apply]
    ring

@[simp] theorem normalizedSignedPairingBase_apply
    (Λ : Lp E 1 μ →L[ℝ] ℝ) (z : C(X,ℝ) × C(X,E)) :
    normalizedSignedPairingBase (μ:=μ) Λ z =
      (∫ x, z.1 x ∂μ) + ‖Λ‖⁻¹ * Λ (ContinuousMap.toLp 1 μ ℝ z.2) := by
  simp [normalizedSignedPairingBase]

theorem normalizedSignedPairingBase_nonneg
    (J : E →ₗᵢ[ℝ] C(K, ℝ))
    (Λ : Lp E 1 μ →L[ℝ] ℝ) (hΛ : Λ ≠ 0)
    (z : C(X,ℝ) × C(X,E))
    (hz : 0 ≤ signedPairingRangeMap J z) :
    0 ≤ normalizedSignedPairingBase (μ:=μ) Λ z := by
  have hC : 0 < ‖Λ‖ := norm_pos_iff.mpr hΛ
  have hgint : Integrable (fun x => ‖z.2 x‖) μ := by
    apply (integrable_const ‖z.2‖).mono'
    · exact z.2.continuous.norm.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
          ContinuousMap.norm_coe_le_norm z.2 x
  have haint : Integrable (fun x => z.1 x) μ := by
    apply (integrable_const ‖z.1‖).mono'
    · exact z.1.continuous.aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun x => ContinuousMap.norm_coe_le_norm z.1 x
  have hint : (∫ x, ‖z.2 x‖ ∂μ) ≤ ∫ x, z.1 x ∂μ :=
    integral_mono hgint haint
      (norm_le_fst_of_signedPairingRangeMap_nonneg J z hz)
  have hΛbound :
      -(‖Λ‖ * ‖ContinuousMap.toLp 1 μ ℝ z.2‖) ≤
        Λ (ContinuousMap.toLp 1 μ ℝ z.2) := by
    apply neg_le_of_abs_le
    rw [← Real.norm_eq_abs]
    exact Λ.le_opNorm _
  rw [norm_continuousMap_toLp_one] at hΛbound
  rw [normalizedSignedPairingBase_apply]
  have hinv : 0 < ‖Λ‖⁻¹ := inv_pos.mpr hC
  have hone : ‖Λ‖⁻¹ * ‖Λ‖ = 1 := inv_mul_cancel₀ hC.ne'
  have hscaled : -(∫ x, ‖z.2 x‖ ∂μ) ≤
      ‖Λ‖⁻¹ * Λ (ContinuousMap.toLp 1 μ ℝ z.2) := by
    calc
      -(∫ x, ‖z.2 x‖ ∂μ) =
          ‖Λ‖⁻¹ * (-(‖Λ‖ * ∫ x, ‖z.2 x‖ ∂μ)) := by
        rw [mul_neg, ← mul_assoc, hone, one_mul]
      _ ≤ ‖Λ‖⁻¹ * Λ (ContinuousMap.toLp 1 μ ℝ z.2) :=
        mul_le_mul_of_nonneg_left hΛbound hinv.le
  have hfinal : -(∫ x, z.1 x ∂μ) ≤
      ‖Λ‖⁻¹ * Λ (ContinuousMap.toLp 1 μ ℝ z.2) :=
    (neg_le_neg hint).trans hscaled
  linarith


noncomputable def continuousMapPositiveCone (Z : Type*)
    [TopologicalSpace Z] : ConvexCone ℝ C(Z, ℝ) where
  carrier := {F | 0 ≤ F}
  smul_mem' c hc F hF := by
    intro z
    exact mul_nonneg hc.le (hF z)
  add_mem' F hF G hG := by
    intro z
    exact add_nonneg (hF z) (hG z)

theorem exists_positiveNormalizedState_extends_signedPairing
    (J : E →ₗᵢ[ℝ] C(K, ℝ))
    (Λ : Lp E 1 μ →L[ℝ] ℝ) (hΛ : Λ ≠ 0) :
    ∃ Ψ : PositiveNormalizedState (X × (K × Bool)),
      ∀ z : C(X, ℝ) × C(X, E),
        Ψ.1 (signedPairingRangeMap J z) =
          normalizedSignedPairingBase (μ := μ) Λ z := by
  let T := signedPairingRangeMap (X := X) J
  have hT : Function.Injective T := signedPairingRangeMap_injective J
  let P : Subspace ℝ C(X × (K × Bool), ℝ) := LinearMap.range T
  let equiv : (C(X, ℝ) × C(X, E)) ≃ₗ[ℝ] P :=
    LinearEquiv.ofInjective T hT
  let onRange : P →ₗ[ℝ] ℝ :=
    (normalizedSignedPairingBase (μ := μ) Λ).comp equiv.symm.toLinearMap
  let fP : C(X × (K × Bool), ℝ) →ₗ.[ℝ] ℝ := ⟨P, onRange⟩
  let cone := (continuousMapPositiveCone (X × (K × Bool))).toPointedCone
    (by change (0 : C(X × (K × Bool), ℝ)) ≤ 0; exact le_rfl)
  have hpositive : ∀ x : fP.domain, (x : C(X × (K × Bool), ℝ)) ∈ cone →
      0 ≤ fP x := by
    intro x hx
    let w : C(X, ℝ) × C(X, E) := equiv.symm x
    have he : T w = (x : C(X × (K × Bool), ℝ)) := by
      exact congrArg Subtype.val (equiv.apply_symm_apply x)
    apply normalizedSignedPairingBase_nonneg J Λ hΛ w
    rw [he]
    exact hx
  have hdense : ∀ y : C(X × (K × Bool), ℝ),
      ∃ x : fP.domain, (x : C(X × (K × Bool), ℝ)) + y ∈ cone := by
    intro y
    let a : C(X, ℝ) := ContinuousMap.const X ‖y‖
    let z : C(X, ℝ) × C(X, E) := (a, 0)
    let x : P := equiv z
    refine ⟨x, ?_⟩
    intro p
    have hp := neg_le_of_abs_le (ContinuousMap.norm_coe_le_norm y p)
    have hex : (x : C(X × (K × Bool), ℝ)) = T z := by
      rfl
    rw [hex]
    change 0 ≤ signedPairingRangeMap J z p + y p
    rw [signedPairingRangeMap_apply]
    change 0 ≤ ‖y‖ + boolSign p.2.2 * J (0 : E) p.2.1 + y p
    simp only [map_zero, ContinuousMap.zero_apply, mul_zero, add_zero]
    linarith
  obtain ⟨PsiLin, hPsiExt, hPsiPos⟩ :=
    riesz_extension cone fP hpositive hdense
  have hpos : ∀ F : C(X × (K × Bool), ℝ), 0 ≤ F → 0 ≤ PsiLin F := by
    intro F hF
    exact hPsiPos F hF
  let Psi : C(X × (K × Bool), ℝ) →L[ℝ] ℝ :=
    positiveLinearMapToContinuous PsiLin hpos
  have hPsiOne : Psi 1 = 1 := by
    let z : C(X, ℝ) × C(X, E) := (1, 0)
    let x : P := equiv z
    have hext := hPsiExt x
    have hx : (x : C(X × (K × Bool), ℝ)) = 1 := by
      change signedPairingRangeMap J z = 1
      ext p
      change (1 : C(X, ℝ)) p.1 +
        boolSign p.2.2 * J ((0 : C(X, E)) p.1) p.2.1 = 1
      simp [boolSign]
    rw [hx] at hext
    change PsiLin 1 = 1
    rw [hext]
    change normalizedSignedPairingBase (μ := μ) Λ (equiv.symm x) = 1
    rw [show equiv.symm x = z from equiv.symm_apply_apply z]
    simp [z, normalizedSignedPairingBase_apply]
  let state : PositiveNormalizedState (X × (K × Bool)) :=
    ⟨StrongDual.toWeakDual Psi, by
      constructor
      · intro F hF
        exact hpos F hF
      · exact hPsiOne⟩
  refine ⟨state, fun z => ?_⟩
  let x : P := equiv z
  have hext := hPsiExt x
  have hx : (x : C(X × (K × Bool), ℝ)) = T z := by
    rfl
  change PsiLin (T z) = normalizedSignedPairingBase (μ := μ) Λ z
  rw [← hx, hext]
  change normalizedSignedPairingBase (μ := μ) Λ (equiv.symm x) = _
  rw [equiv.symm_apply_apply]

end PositiveStateExtension
end IndependentZeroBlocks
