import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

set_option autoImplicit false

noncomputable section

namespace FiniteMonoidMortality

open Complex

def boundedRotation (θ : ℝ) : ℂ →L[ℝ] ℂ :=
  ContinuousLinearMap.mul ℝ ℂ (Complex.exp (θ*I))

def boundedProjection : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.reCLM

def boundedDigit (θ : ℝ) : Bool → (ℂ →L[ℝ] ℂ)
  | false => boundedRotation θ
  | true => boundedProjection

def continuousWord {A : Type*} (T : A → (ℂ →L[ℝ] ℂ)) (w : List A) : ℂ →L[ℝ] ℂ :=
  (w.map T).prod

@[simp] theorem boundedRotation_apply (θ : ℝ) (z : ℂ) :
    boundedRotation θ z=Complex.exp (θ*I)*z := rfl

@[simp] theorem boundedProjection_apply (z : ℂ) : boundedProjection z=(z.re : ℂ) := rfl

@[simp] theorem continuousWord_append {A : Type*} (T : A → (ℂ →L[ℝ] ℂ)) (w v : List A) :
    continuousWord T (w++v)=continuousWord T w*continuousWord T v := by
  simp [continuousWord,List.map_append,List.prod_append]

theorem boundedRotation_pow_apply (θ : ℝ) (k : ℕ) (z : ℂ) :
    ((boundedRotation θ)^k) z=Complex.exp (((k : ℝ)*θ)*I)*z := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ']
    change boundedRotation θ (((boundedRotation θ)^k) z)=_
    rw [boundedRotation_apply,ih,← mul_assoc,← Complex.exp_add]
    congr 2
    push_cast
    ring

theorem boundedDigit_norm_le (θ : ℝ) (a : Bool) (z : ℂ) : ‖boundedDigit θ a z‖ ≤ ‖z‖ := by
  cases a with
  | false => simp [boundedDigit,Complex.norm_exp_ofReal_mul_I]
  | true => simpa [boundedDigit] using Complex.abs_re_le_norm z

theorem boundedWord_norm_le (θ : ℝ) (w : List Bool) (z : ℂ) :
    ‖continuousWord (boundedDigit θ) w z‖ ≤ ‖z‖ := by
  induction w with
  | nil => exact le_rfl
  | cons a w ih => exact (boundedDigit_norm_le θ a _).trans ih

theorem boundedWord_range_bounded (θ : ℝ) :
    Bornology.IsBounded (Set.range (continuousWord (boundedDigit θ))) := by
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨1,?_⟩
  rintro X ⟨w,rfl⟩
  exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by simpa using boundedWord_norm_le θ w)

theorem boundedProjection_idempotent : IsIdempotentElem boundedProjection := by
  ext z
  simp

theorem boundedRotation_period (m : ℕ) (hm : 0<m) :
    (boundedRotation (Real.pi/(2*m)))^(4*m)=1 := by
  ext z
  rw [boundedRotation_pow_apply]
  have he : ((4*m : ℕ) : ℝ)*(Real.pi/(2*m))=2*Real.pi := by
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
    push_cast
    field_simp
    <;> ring
  rw [← Complex.ofReal_mul,he]
  push_cast
  rw [Complex.exp_two_pi_mul_I,one_mul]
  rfl

theorem boundedDigit_finite_powers (m : ℕ) (hm : 0<m) (a : Bool) :
    (Set.range (fun k : ℕ => (boundedDigit (Real.pi/(2*m)) a)^k)).Finite := by
  cases a with
  | false =>
    have hf := (isOfFinOrder_iff_pow_eq_one.mpr
      ⟨4*m,by omega,boundedRotation_period m hm⟩).finite_powers
    simpa [Submonoid.coe_powers,boundedDigit] using hf
  | true =>
    apply (Set.toFinite ({1,boundedProjection} : Set (ℂ →L[ℝ] ℂ))).subset
    rintro X ⟨k,rfl⟩
    cases k with
    | zero => simp
    | succ k =>
      change boundedProjection^(k+1) ∈ _
      rw [boundedProjection_idempotent.pow_succ_eq]
      simp

theorem boundedWord_positive_ray (θ : ℝ) (hθ : 0 ≤ θ) (w : List Bool)
    (hl : (w.length : ℝ)*θ < Real.pi/2) :
    ∃ q : ℝ, ∃ k : ℕ, 0<q ∧ k ≤ w.length ∧
      continuousWord (boundedDigit θ) w 1=(q : ℂ)*Complex.exp (((k : ℝ)*θ)*I) := by
  induction w with
  | nil => exact ⟨1,0,by norm_num,le_rfl,by simp [continuousWord]⟩
  | cons a w ih =>
    have hlw : (w.length : ℝ)*θ < Real.pi/2 := by
      have hh : (w.length : ℝ) ≤ ((a::w).length : ℝ) := by simp
      exact (mul_le_mul_of_nonneg_right hh hθ).trans_lt hl
    obtain ⟨q,k,hq,hk,he⟩ := ih hlw
    cases a with
    | false =>
      refine ⟨q,k+1,hq,by simpa using Nat.succ_le_succ hk,?_⟩
      change boundedRotation θ (continuousWord (boundedDigit θ) w 1)=_
      rw [boundedRotation_apply,he]
      rw [mul_left_comm,← Complex.exp_add]
      congr 2
      push_cast
      ring
    | true =>
      have hkθ : (k : ℝ)*θ < Real.pi/2 :=
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hθ).trans_lt hlw
      have hcos : 0<Real.cos ((k : ℝ)*θ) := Real.cos_pos_of_mem_Ioo
        ⟨by have := Real.pi_pos; have := mul_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ k) hθ; linarith, hkθ⟩
      refine ⟨q*Real.cos ((k : ℝ)*θ),0,mul_pos hq hcos,Nat.zero_le _,?_⟩
      change boundedProjection (continuousWord (boundedDigit θ) w 1)=_
      rw [he,boundedProjection_apply]
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
      rw [← Complex.ofReal_mul,Complex.exp_ofReal_mul_I_re]
      simp

theorem boundedWord_short_ne_zero (θ : ℝ) (hθ : 0 ≤ θ) (w : List Bool)
    (hl : (w.length : ℝ)*θ < Real.pi/2) : continuousWord (boundedDigit θ) w ≠ 0 := by
  obtain ⟨q,k,hq,_,he⟩ := boundedWord_positive_ray θ hθ w hl
  intro hz
  have hv := congrArg (fun T : ℂ →L[ℝ] ℂ => T 1) hz
  rw [he] at hv
  exact mul_ne_zero (by exact_mod_cast ne_of_gt hq) (Complex.exp_ne_zero _) hv

theorem boundedWord_zero (m : ℕ) (hm : 0<m) :
    continuousWord (boundedDigit (Real.pi/(2*m)))
      ([true]++List.replicate m false++[true])=0 := by
  have hrep : continuousWord (boundedDigit (Real.pi/(2*m))) (List.replicate m false)=
      boundedRotation (Real.pi/(2*m))^m := by simp [continuousWord,boundedDigit]
  rw [continuousWord_append,continuousWord_append,hrep]
  ext z
  change boundedProjection ((boundedRotation (Real.pi/(2*m))^m) (boundedProjection z))=0
  rw [boundedRotation_pow_apply,boundedProjection_apply,boundedProjection_apply]
  have he : (m : ℝ)*(Real.pi/(2*m))=Real.pi/2 := by
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
    field_simp
  rw [← Complex.ofReal_mul,he]
  simp [Complex.mul_re,Real.cos_pi_div_two]

theorem bounded_periodic_mortality_no_uniform_bound (N : ℕ) :
    Module.finrank ℝ ℂ=2 ∧
    ∃ T : Bool → (ℂ →L[ℝ] ℂ),
      Bornology.IsBounded (Set.range (continuousWord T)) ∧
      (∀ a, (Set.range (fun k : ℕ => (T a)^k)).Finite) ∧
      (∃ w, continuousWord T w=0) ∧
      (∀ w, w.length ≤ N → continuousWord T w ≠ 0) := by
  let m := N+1
  have hm : 0<m := by omega
  refine ⟨Complex.finrank_real_complex,boundedDigit (Real.pi/(2*m)),
    boundedWord_range_bounded _,boundedDigit_finite_powers m hm,
    ⟨_,boundedWord_zero m hm⟩,?_⟩
  intro w hw
  apply boundedWord_short_ne_zero _ (by positivity)
  have hm0 : (0 : ℝ)<m := by exact_mod_cast hm
  have hl : (w.length : ℝ)<m := by exact_mod_cast (show w.length<m by omega)
  have hp := Real.pi_pos
  apply (lt_div_iff₀ (by norm_num : (0 : ℝ)<2)).mpr
  field_simp
  nlinarith [mul_lt_mul_of_pos_right hl hp]

end FiniteMonoidMortality
