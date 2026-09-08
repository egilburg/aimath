import SoficMarkovOrder.ExteriorRank
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.LinearAlgebra.Dual.Lemmas

set_option autoImplicit false

/-!
# Reduced word representations and the finite-memory rank criterion

Markovity is expressed through contextual cylinder-weight identities, not
defined as matrix rank. Probability-measure realization is a separate bridge.
-/

namespace SoficMarkovOrder

variable {K V A : Type*} [Field K] [AddCommGroup V] [Module K V]

def representedWord (T : A → Module.End K V) (l : Module.Dual K V) (g : V)
    (w : List A) : K := l (linearWord T w g)

/-- The intrinsic column space of the word Hankel matrix. -/
def wordHankelSpan (p : List A → K) : Submodule K (List A → K) :=
  Submodule.span K (Set.range fun z : List A => fun u : List A => p (u ++ z))

/-- Observe a state in every left context. -/
def wordObservationMap (T : A → Module.End K V) (l : Module.Dual K V) :
    V →ₗ[K] (List A → K) := LinearMap.pi fun u => l.comp (linearWord T u)

theorem wordHankelSpan_eq_map_reachable
    (T : A → Module.End K V) (l : Module.Dual K V) (g : V) :
    wordHankelSpan (representedWord T l g) =
      (linearReachableSpan T g).map (wordObservationMap T l) := by
  rw [linearReachableSpan, linearOrbit, Submodule.map_span, ← Set.range_comp]
  simp only [wordHankelSpan, representedWord, wordObservationMap, linearWord_append,
    Module.End.mul_apply, Function.comp_def, LinearMap.pi_apply, LinearMap.comp_apply]
  rfl

/-- Every finite future has the same conditional law after a fixed suffix. -/
def ContextMarkov (p : List A → K) (k : ℕ) : Prop :=
  ∀ u v z : List A, v.length = k →
    p (u ++ v ++ z) * p v = p (u ++ v) * p (v ++ z)

/-- Reachable columns span and observable rows separate the state space. -/
structure WordReduced (T : A → Module.End K V) (l : Module.Dual K V) (g : V) : Prop where
  reachable : linearReachableSpan T g = ⊤
  observable : ∀ x : V, (∀ u : List A, l (linearWord T u x) = 0) → x = 0

theorem WordReduced.observation_injective
    {T : A → Module.End K V} {l : Module.Dual K V} {g : V}
    (hr : WordReduced T l g) : Function.Injective (wordObservationMap T l) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot.mpr
  intro x y h
  apply sub_eq_zero.mp
  apply hr.observable
  intro u
  have hu := congrFun h u
  change l (linearWord T u x) = l (linearWord T u y) at hu
  simp only [map_sub, sub_eq_zero]
  exact hu

/-- Reduced state dimension is the intrinsic Hankel dimension. -/
theorem WordReduced.finrank_wordHankelSpan
    {T : A → Module.End K V} {l : Module.Dual K V} {g : V}
    (hr : WordReduced T l g) :
    Module.finrank K (wordHankelSpan (representedWord T l g)) = Module.finrank K V := by
  rw [wordHankelSpan_eq_map_reachable, hr.reachable, Submodule.map_top]
  exact LinearMap.finrank_range_of_inj hr.observation_injective

theorem end_eq_zero_of_context_zero
    {T : A → Module.End K V} {l : Module.Dual K V} {g : V}
    (hr : WordReduced T l g) (f : Module.End K V)
    (h : ∀ u z : List A, l (linearWord T u (f (linearWord T z g))) = 0) :
    f = 0 := by
  have hz (z : List A) : f (linearWord T z g) = 0 :=
    hr.observable _ (fun u => h u z)
  ext x
  have hx : x ∈ linearReachableSpan T g := by rw [hr.reachable]; trivial
  change x ∈ Submodule.span K (linearOrbit T g) at hx
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨z, rfl⟩ := hx; exact hz z
  | zero => simp
  | add x y hx hy ihx ihy => simp [map_add, ihx, ihy]
  | smul c x hx ih => simp [map_smul, ih]

/-- In a reduced representation, forbidden contextual weights force the matrix to vanish. -/
theorem matrix_eq_zero_of_forbidden_contexts
    {T : A → Module.End K V} {l : Module.Dual K V} {g : V}
    (hr : WordReduced T l g) (v : List A)
    (h : ∀ u z : List A, representedWord T l g (u ++ v ++ z) = 0) :
    linearWord T v = 0 := by
  apply end_eq_zero_of_context_zero hr
  intro u z
  simpa only [representedWord, linearWord_append, Module.End.mul_apply] using h u z

section Finite
variable [FiniteDimensional K V]

theorem rankOne_bilinear (f : Module.End K V) (hf : Module.finrank K f.range ≤ 1)
    (l₁ l₂ : Module.Dual K V) (x y : V) :
    l₁ (f x) * l₂ (f y) = l₁ (f y) * l₂ (f x) := by
  obtain ⟨b, hb⟩ := (finrank_le_one_iff (K := K) (V := f.range)).mp hf
  obtain ⟨c, hc⟩ := hb ⟨f x, LinearMap.mem_range_self f x⟩
  obtain ⟨d, hd⟩ := hb ⟨f y, LinearMap.mem_range_self f y⟩
  have hx : c • b.val = f x := congrArg Subtype.val hc
  have hy : d • b.val = f y := congrArg Subtype.val hd
  rw [← hx, ← hy]
  simp only [map_smul, smul_eq_mul]
  ring

theorem contextMarkov_of_rankOne
    (T : A → Module.End K V) (l : Module.Dual K V) (g : V) (k : ℕ)
    (h : ∀ v : List A, v.length = k → Module.finrank K (linearWord T v).range ≤ 1) :
    ContextMarkov (representedWord T l g) k := by
  intro u v z hv
  have hdet := rankOne_bilinear (linearWord T v) (h v hv)
    (l.comp (linearWord T u)) l (linearWord T z g) g
  simpa only [representedWord, linearWord_append, Module.End.mul_apply,
    LinearMap.comp_apply] using hdet

omit [FiniteDimensional K V] in
/-- The contextual identity forces a rank-one operator when its middle mass is nonzero. -/
theorem rankOne_of_context_identity_of_ne_zero
    {T : A → Module.End K V} {l : Module.Dual K V} {g : V}
    (hr : WordReduced T l g) (v : List A)
    (hv : representedWord T l g v ≠ 0)
    (h : ∀ u z : List A,
      representedWord T l g (u ++ v ++ z) * representedWord T l g v =
        representedWord T l g (u ++ v) * representedWord T l g (v ++ z)) :
    Module.finrank K (linearWord T v).range ≤ 1 := by
  let f := linearWord T v
  let p := representedWord T l g v
  let E : Module.End K V := p • f - (l.comp f).smulRight (f g)
  have hE : E = 0 := by
    apply end_eq_zero_of_context_zero hr
    intro u z
    have hh := h u z
    dsimp [representedWord] at hh
    simp only [linearWord_append, Module.End.mul_apply] at hh
    simp only [E, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smulRight_apply,
      LinearMap.comp_apply, map_sub, map_smul, smul_eq_mul]
    dsimp [f, p, representedWord]
    exact sub_eq_zero.mpr (by simpa only [mul_comm] using hh)
  have hfx (x : V) : p • f x = l (f x) • f g := by
    have he := LinearMap.congr_fun hE x
    change p • f x - l (f x) • f g = 0 at he
    exact sub_eq_zero.mp he
  apply finrank_le_one (⟨f g, LinearMap.mem_range_self f g⟩ : f.range)
  intro y
  obtain ⟨x, hx⟩ := y.property
  refine ⟨p⁻¹ * l (f x), ?_⟩
  apply Subtype.ext
  change (p⁻¹ * l (f x)) • f g = y.val
  calc
    (p⁻¹ * l (f x)) • f g = p⁻¹ • (l (f x) • f g) := mul_smul _ _ _
    _ = p⁻¹ • (p • f x) := by rw [hfx]
    _ = f x := by rw [smul_smul, inv_mul_cancel₀ hv, one_smul]
    _ = y.val := hx

/-- Holland's word-level equivalence, with forbidden contexts handled explicitly. -/
theorem contextMarkov_iff_rankOne
    {T : A → Module.End K V} {l : Module.Dual K V} {g : V}
    (hr : WordReduced T l g)
    (hforbidden : ∀ v : List A, representedWord T l g v = 0 →
      ∀ u z : List A, representedWord T l g (u ++ v ++ z) = 0) (k : ℕ) :
    ContextMarkov (representedWord T l g) k ↔
      ∀ v : List A, v.length = k → Module.finrank K (linearWord T v).range ≤ 1 := by
  constructor
  · intro h v hv
    by_cases hp : representedWord T l g v = 0
    · have hz := matrix_eq_zero_of_forbidden_contexts hr v (hforbidden v hp)
      rw [hz, LinearMap.range_zero]
      simp
    · exact rankOne_of_context_identity_of_ne_zero hr v hp (fun u z => h u v z hv)
  · exact contextMarkov_of_rankOne T l g k

/-- The binomial upper bound for reduced contextual word weights. -/
theorem contextMarkov_cutoff_choose_two
    {T : A → Module.End K V} {l : Module.Dual K V} {g : V}
    (hr : WordReduced T l g)
    (hforbidden : ∀ v : List A, representedWord T l g v = 0 →
      ∀ u z : List A, representedWord T l g (u ++ v ++ z) = 0)
    (hfinite : ∃ k, ContextMarkov (representedWord T l g) k) :
    ContextMarkov (representedWord T l g) ((Module.finrank K V).choose 2) := by
  apply (contextMarkov_iff_rankOne hr hforbidden _).mpr
  apply eventual_rankOne_cutoff_choose_two
  obtain ⟨k, hk⟩ := hfinite
  exact ⟨k, (contextMarkov_iff_rankOne hr hforbidden k).mp hk⟩

end Finite
end SoficMarkovOrder
