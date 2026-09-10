import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Data.Set.Finite.Lemmas

/-!
# Atomic stationary laws on finitely generated group flows

This file isolates the discrete maximum principle used after a probability
on a countable compact flow has been shown to be atomic.  No topology is
needed here: a summable nonnegative mass function, stationary for a positive
finite law whose support generates the acting group, is supported on finite
orbits and is constant on each positive-mass orbit.
-/

noncomputable section

open scoped BigOperators Pointwise
open Set

namespace IndependentZeroBlocks

variable {G X D : Type*} [Group G] [MulAction G X]

/-- Pointwise stationarity for a finite random walk.  The inverse in the
argument is the convention obtained from pushforward by the left action. -/
def IsStationaryMass [Fintype D] (step : D → G) (weight : D → ℝ)
    (mass : X → ℝ) : Prop :=
  ∀ x, mass x = ∑ d, weight d * mass ((step d)⁻¹ • x)

/-- A positive summable atom mass has only finitely many atoms at least as
large. -/
theorem finite_superlevel_of_summable_nonneg
    (mass : X → ℝ) (hmass : Summable mass)
    (hnonneg : ∀ x, 0 ≤ mass x) {x : X} (hx : 0 < mass x) :
    {y : X | mass x ≤ mass y}.Finite := by
  have h := hmass.tendsto_cofinite_zero.eventually_lt_const hx
  rw [Filter.eventually_cofinite] at h
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hnonneg _), not_lt] using h

/-- A nonnegative mass function with total mass one has a positive atom.
This formulation deliberately uses `HasSum`, so it applies on any index type
and does not require a chosen enumeration of a countable flow. -/
theorem exists_pos_of_hasSum_one
    (mass : X → ℝ) (hnonneg : ∀ x, 0 ≤ mass x)
    (hmass : HasSum mass 1) : ∃ x, 0 < mass x := by
  by_contra h
  push_neg at h
  have hz : mass = 0 := by
    funext x
    exact le_antisymm (h x) (hnonneg x)
  subst mass
  have hzero : HasSum (0 : X → ℝ) 0 := hasSum_zero
  have : (1 : ℝ) = 0 := hmass.unique hzero
  norm_num at this

section MaximumPrinciple

variable [Fintype D] [Nonempty D]
variable (step : D → G) (weight : D → ℝ) (mass : X → ℝ)

/-- The maximum-level set in an orbit is preserved by each inverse step.
Strict positivity of every step weight is the key maximum principle. -/
theorem inverse_step_mapsTo_maxLevel
    (hweight : ∀ d, 0 < weight d) (hweight_one : ∑ d, weight d = 1)
    (hstationary : IsStationaryMass step weight mass)
    {y : X} (hmax : ∀ z ∈ MulAction.orbit G y, mass z ≤ mass y) :
    ∀ d, MapsTo (fun z : X ↦ (step d)⁻¹ • z)
      {z | z ∈ MulAction.orbit G y ∧ mass z = mass y}
      {z | z ∈ MulAction.orbit G y ∧ mass z = mass y} := by
  intro d z hz
  have horbit : (step d)⁻¹ • z ∈ MulAction.orbit G y :=
    MulAction.mem_orbit_of_mem_orbit (step d)⁻¹ hz.1
  refine ⟨horbit, ?_⟩
  have hle : ∀ e, mass ((step e)⁻¹ • z) ≤ mass y := fun e ↦
    hmax _ (MulAction.mem_orbit_of_mem_orbit (step e)⁻¹ hz.1)
  have hnonneg : ∀ e ∈ (Finset.univ : Finset D),
      0 ≤ weight e * (mass y - mass ((step e)⁻¹ • z)) := by
    intro e _
    exact mul_nonneg (hweight e).le (sub_nonneg.mpr (hle e))
  have hsum : ∑ e, weight e * (mass y - mass ((step e)⁻¹ • z)) = 0 := by
    calc
      ∑ e, weight e * (mass y - mass ((step e)⁻¹ • z)) =
          mass y * (∑ e, weight e) -
            ∑ e, weight e * mass ((step e)⁻¹ • z) := by
              simp_rw [mul_sub]
              rw [Finset.sum_sub_distrib, Finset.mul_sum]
              apply congrArg (fun t : ℝ ↦ t - ∑ e, weight e * mass ((step e)⁻¹ • z))
              apply Finset.sum_congr rfl
              intro e _
              exact mul_comm _ _
      _ = 0 := by rw [hweight_one, ← hstationary z, hz.2]; ring
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum d (Finset.mem_univ d)
  have hdiff : mass y - mass ((step d)⁻¹ • z) = 0 := by
    exact (mul_eq_zero.mp hterm).resolve_left (ne_of_gt (hweight d))
  linarith

/-- Discrete stationary maximum principle.  The orbit of any positive atom
is finite, and the stationary mass is constant on that orbit. -/
theorem finite_orbit_and_constant_of_stationary
    (hweight : ∀ d, 0 < weight d) (hweight_one : ∑ d, weight d = 1)
    (hgenerate : Subgroup.closure (Set.range step) = ⊤)
    (hstationary : IsStationaryMass step weight mass)
    (hmass : Summable mass) (hnonneg : ∀ x, 0 ≤ mass x)
    {x : X} (hx : 0 < mass x) :
    ∃ y ∈ MulAction.orbit G x,
      (MulAction.orbit G y).Finite ∧
      ∀ z ∈ MulAction.orbit G y, mass z = mass y := by
  let A : Set X := {z | mass x ≤ mass z}
  have hAfin : A.Finite := finite_superlevel_of_summable_nonneg mass hmass hnonneg hx
  let B : Set X := A ∩ MulAction.orbit G x
  have hBfin : B.Finite := hAfin.inter_of_left _
  have hxB : x ∈ B := by
    change mass x ≤ mass x ∧ x ∈ MulAction.orbit G x
    exact ⟨le_rfl, MulAction.mem_orbit_self x⟩
  obtain ⟨y, hyB, hymaxB⟩ := Set.exists_max_image B mass hBfin ⟨x, hxB⟩
  have hyorbit : y ∈ MulAction.orbit G x := hyB.2
  have hypos : 0 < mass y := hx.trans_le hyB.1
  have hymax : ∀ z ∈ MulAction.orbit G y, mass z ≤ mass y := by
    intro z hz
    have hzx : z ∈ MulAction.orbit G x := by
      have heq : MulAction.orbit G y = MulAction.orbit G x :=
        MulAction.orbit_eq_iff.mpr hyorbit
      exact heq ▸ hz
    by_cases hlevel : mass x ≤ mass z
    · exact hymaxB z ⟨hlevel, hzx⟩
    · exact (lt_of_not_ge hlevel).le.trans hyB.1
  let F : Set X := {z | z ∈ MulAction.orbit G y ∧ mass z = mass y}
  have hFfin : F.Finite := by
    apply (finite_superlevel_of_summable_nonneg mass hmass hnonneg hypos).subset
    intro z hz
    exact hz.2.ge
  have hInvMaps : ∀ d, MapsTo (fun z : X ↦ (step d)⁻¹ • z) F F := by
    simpa only [F] using inverse_step_mapsTo_maxLevel step weight mass
      hweight hweight_one hstationary hymax
  have hStepMaps : ∀ d, MapsTo (fun z : X ↦ step d • z) F F := by
    intro d
    have hinj : Set.InjOn (fun z : X ↦ (step d)⁻¹ • z) F :=
      (MulAction.toPerm (step d)⁻¹).injective.injOn
    have hsurj : Set.SurjOn (fun z : X ↦ (step d)⁻¹ • z) F F :=
      (hFfin.injOn_iff_bijOn_of_mapsTo (hInvMaps d)).mp hinj |>.surjOn
    intro z hz
    obtain ⟨u, huF, hu⟩ := hsurj hz
    have : u = step d • z := by
      rw [← hu, smul_smul, mul_inv_cancel, one_smul]
    change step d • z ∈ F
    rw [← this]
    exact huF
  have hclosure : Subgroup.closure (Set.range step) ≤ MulAction.stabilizer G F := by
    rw [Subgroup.closure_le]
    rintro g ⟨d, rfl⟩
    apply (MulAction.mem_stabilizer_iff).2
    apply Set.Subset.antisymm
    · change (fun z : X ↦ step d • z) '' F ⊆ F
      exact Set.image_subset_iff.mpr (hStepMaps d)
    · change F ⊆ (fun z : X ↦ step d • z) '' F
      intro z hz
      refine ⟨(step d)⁻¹ • z, hInvMaps d hz, ?_⟩
      simp
  have htop : (⊤ : Subgroup G) ≤ MulAction.stabilizer G F := by
    rw [← hgenerate]
    exact hclosure
  have horbitF : MulAction.orbit G y ⊆ F := by
    rintro z ⟨g, rfl⟩
    have hg : g ∈ MulAction.stabilizer G F := htop (Subgroup.mem_top g)
    have hgEq : g • F = F := (MulAction.mem_stabilizer_iff).1 hg
    have hyF : y ∈ F := ⟨MulAction.mem_orbit_self y, rfl⟩
    exact hgEq ▸ ⟨y, hyF, rfl⟩
  refine ⟨y, hyorbit, hFfin.subset horbitF, ?_⟩
  intro z hz
  exact (horbitF hz).2

/-- A direct form of the maximum principle at the supplied positive atom. -/
theorem finite_orbit_and_constant_at_positive_atom
    (hweight : ∀ d, 0 < weight d) (hweight_one : ∑ d, weight d = 1)
    (hgenerate : Subgroup.closure (Set.range step) = ⊤)
    (hstationary : IsStationaryMass step weight mass)
    (hmass : Summable mass) (hnonneg : ∀ x, 0 ≤ mass x)
    {x : X} (hx : 0 < mass x) :
    (MulAction.orbit G x).Finite ∧
      ∀ z ∈ MulAction.orbit G x, mass z = mass x := by
  obtain ⟨y, hyorbit, hyfin, hyconst⟩ :=
    finite_orbit_and_constant_of_stationary step weight mass hweight hweight_one
      hgenerate hstationary hmass hnonneg hx
  have heq : MulAction.orbit G y = MulAction.orbit G x :=
    MulAction.orbit_eq_iff.mpr hyorbit
  refine ⟨heq ▸ hyfin, ?_⟩
  intro z hz
  have hzy : z ∈ MulAction.orbit G y := heq.symm ▸ hz
  have hxy : mass x = mass y :=
    hyconst x (MulAction.mem_orbit_symm.mp hyorbit)
  exact (hyconst z hzy).trans hxy.symm

/-- An atomic stationary mass is invariant under the whole generated group.
Zero-mass orbits are handled by applying the positive-orbit theorem at a
hypothetical positive translate. -/
theorem stationary_mass_invariant
    (hweight : ∀ d, 0 < weight d) (hweight_one : ∑ d, weight d = 1)
    (hgenerate : Subgroup.closure (Set.range step) = ⊤)
    (hstationary : IsStationaryMass step weight mass)
    (hmass : Summable mass) (hnonneg : ∀ x, 0 ≤ mass x) :
    ∀ (g : G) (x : X), mass (g • x) = mass x := by
  intro g x
  by_cases hx : mass x = 0
  · have hgx : mass (g • x) = 0 := by
      by_contra hne
      have hpos : 0 < mass (g • x) := lt_of_le_of_ne (hnonneg _) (Ne.symm hne)
      obtain ⟨_, hconst⟩ :=
        finite_orbit_and_constant_at_positive_atom step weight mass hweight hweight_one
          hgenerate hstationary hmass hnonneg hpos
      have hxorb : x ∈ MulAction.orbit G (g • x) := MulAction.mem_orbit_smul g x
      have hzero : mass (g • x) = 0 := (hconst x hxorb).symm.trans hx
      exact hne hzero
    exact hgx.trans hx.symm
  · have hpos : 0 < mass x := lt_of_le_of_ne (hnonneg x) (Ne.symm hx)
    obtain ⟨_, hconst⟩ :=
      finite_orbit_and_constant_at_positive_atom step weight mass hweight hweight_one
        hgenerate hstationary hmass hnonneg hpos
    exact hconst (g • x) (MulAction.mem_orbit x g)

/-- Every probability mass under the same hypotheses contains a finite
uniform orbit. -/
theorem exists_finite_uniform_orbit_of_stationary_probability
    (hweight : ∀ d, 0 < weight d) (hweight_one : ∑ d, weight d = 1)
    (hgenerate : Subgroup.closure (Set.range step) = ⊤)
    (hstationary : IsStationaryMass step weight mass)
    (hnonneg : ∀ x, 0 ≤ mass x) (hmass : HasSum mass 1) :
    ∃ y : X, (MulAction.orbit G y).Finite ∧ 0 < mass y ∧
      ∀ z ∈ MulAction.orbit G y, mass z = mass y := by
  obtain ⟨x, hx⟩ := exists_pos_of_hasSum_one mass hnonneg hmass
  obtain ⟨hxfin, hxconst⟩ :=
    finite_orbit_and_constant_at_positive_atom step weight mass hweight hweight_one
      hgenerate hstationary hmass.summable hnonneg hx
  exact ⟨x, hxfin, hx, hxconst⟩

end MaximumPrinciple

end IndependentZeroBlocks
