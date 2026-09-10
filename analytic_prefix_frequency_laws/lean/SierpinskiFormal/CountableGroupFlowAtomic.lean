import SierpinskiFormal.GroupFlowAtomic

/-!
# Atomic stationary laws with countable support

This file extends the discrete maximum principle from finite random laws to
arbitrary summable positive laws.  The index type need not carry a chosen
enumeration: `HasSum weight 1` is the countable-support hypothesis.
-/

noncomputable section

open scoped BigOperators Pointwise
open Set

namespace IndependentZeroBlocks

variable {G X D : Type*} [Group G] [MulAction G X]

/-- Pointwise stationarity for a summable random walk law. -/
def IsCountableStationaryMass (step : D → G) (weight : D → ℝ)
    (mass : X → ℝ) : Prop :=
  ∀ x, mass x = ∑' d, weight d * mass ((step d)⁻¹ • x)

/-- Multiplying a summable nonnegative law by values of a summable mass
function along arbitrary (possibly highly noninjective) steps is summable. -/
theorem summable_weight_mul_mass_pullback
    (step : D → G) (weight : D → ℝ) (mass : X → ℝ)
    (hweight : ∀ d, 0 ≤ weight d) (hweight_sum : HasSum weight 1)
    (hmass : Summable mass) (x : X) :
    Summable (fun d ↦ weight d * mass ((step d)⁻¹ • x)) := by
  let M : ℝ := ∑' y, |mass y|
  have hM : ∀ y, |mass y| ≤ M := by
    intro y
    exact hmass.abs.le_tsum y (fun z _ ↦ abs_nonneg (mass z))
  apply (hweight_sum.summable.mul_left M).of_norm_bounded
  intro d
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hweight d)]
  simpa [mul_comm] using mul_le_mul_of_nonneg_right (hM ((step d)⁻¹ • x)) (hweight d)

section MaximumPrinciple

variable (step : D → G) (weight : D → ℝ) (mass : X → ℝ)

/-- The maximum-level set in an orbit is preserved by each inverse step for
an arbitrary summable positive law. -/
theorem countable_inverse_step_mapsTo_maxLevel
    (hweight : ∀ d, 0 < weight d) (hweight_sum : HasSum weight 1)
    (hstationary : IsCountableStationaryMass step weight mass)
    (hmass : Summable mass)
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
  have hpull_summable :
      Summable (fun e ↦ weight e * mass ((step e)⁻¹ • z)) :=
    summable_weight_mul_mass_pullback step weight mass
      (fun e ↦ (hweight e).le) hweight_sum hmass z
  have hpull : HasSum (fun e ↦ weight e * mass ((step e)⁻¹ • z)) (mass y) := by
    rw [← hz.2, hstationary z]
    exact hpull_summable.hasSum
  have hdef : HasSum
      (fun e ↦ weight e * (mass y - mass ((step e)⁻¹ • z))) 0 := by
    simpa only [mul_sub, one_mul, sub_self] using
      (hweight_sum.mul_right (mass y)).sub hpull
  have hnonneg : ∀ e,
      0 ≤ weight e * (mass y - mass ((step e)⁻¹ • z)) := fun e ↦
    mul_nonneg (hweight e).le (sub_nonneg.mpr (hle e))
  have hzero := (hasSum_zero_iff_of_nonneg hnonneg).mp hdef
  have hterm : weight d * (mass y - mass ((step d)⁻¹ • z)) = 0 :=
    congrFun hzero d
  have hdiff : mass y - mass ((step d)⁻¹ • z) = 0 :=
    (mul_eq_zero.mp hterm).resolve_left (ne_of_gt (hweight d))
  linarith

/-- The orbit of every positive atom is finite, and its mass is constant on
that orbit, for a positive summable law generating the acting group. -/
theorem countable_finite_orbit_and_constant_of_stationary
    (hweight : ∀ d, 0 < weight d) (hweight_sum : HasSum weight 1)
    (hgenerate : Subgroup.closure (Set.range step) = ⊤)
    (hstationary : IsCountableStationaryMass step weight mass)
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
    simpa only [F] using countable_inverse_step_mapsTo_maxLevel step weight mass
      hweight hweight_sum hstationary hmass hymax
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

/-- Direct maximum-principle form at a supplied positive atom. -/
theorem countable_finite_orbit_and_constant_at_positive_atom
    (hweight : ∀ d, 0 < weight d) (hweight_sum : HasSum weight 1)
    (hgenerate : Subgroup.closure (Set.range step) = ⊤)
    (hstationary : IsCountableStationaryMass step weight mass)
    (hmass : Summable mass) (hnonneg : ∀ x, 0 ≤ mass x)
    {x : X} (hx : 0 < mass x) :
    (MulAction.orbit G x).Finite ∧
      ∀ z ∈ MulAction.orbit G x, mass z = mass x := by
  obtain ⟨y, hyorbit, hyfin, hyconst⟩ :=
    countable_finite_orbit_and_constant_of_stationary step weight mass hweight
      hweight_sum hgenerate hstationary hmass hnonneg hx
  have heq : MulAction.orbit G y = MulAction.orbit G x :=
    MulAction.orbit_eq_iff.mpr hyorbit
  refine ⟨heq ▸ hyfin, ?_⟩
  intro z hz
  have hzy : z ∈ MulAction.orbit G y := heq.symm ▸ hz
  have hxy : mass x = mass y :=
    hyconst x (MulAction.mem_orbit_symm.mp hyorbit)
  exact (hyconst z hzy).trans hxy.symm

/-- A stationary summable mass is invariant under every element of the
generated group. -/
theorem countable_stationary_mass_invariant
    (hweight : ∀ d, 0 < weight d) (hweight_sum : HasSum weight 1)
    (hgenerate : Subgroup.closure (Set.range step) = ⊤)
    (hstationary : IsCountableStationaryMass step weight mass)
    (hmass : Summable mass) (hnonneg : ∀ x, 0 ≤ mass x) :
    ∀ (g : G) (x : X), mass (g • x) = mass x := by
  intro g x
  by_cases hx : mass x = 0
  · have hgx : mass (g • x) = 0 := by
      by_contra hne
      have hpos : 0 < mass (g • x) := lt_of_le_of_ne (hnonneg _) (Ne.symm hne)
      obtain ⟨_, hconst⟩ :=
        countable_finite_orbit_and_constant_at_positive_atom step weight mass
          hweight hweight_sum hgenerate hstationary hmass hnonneg hpos
      have hxorb : x ∈ MulAction.orbit G (g • x) := MulAction.mem_orbit_smul g x
      have hzero : mass (g • x) = 0 := (hconst x hxorb).symm.trans hx
      exact hne hzero
    exact hgx.trans hx.symm
  · have hpos : 0 < mass x := lt_of_le_of_ne (hnonneg x) (Ne.symm hx)
    obtain ⟨_, hconst⟩ :=
      countable_finite_orbit_and_constant_at_positive_atom step weight mass
        hweight hweight_sum hgenerate hstationary hmass hnonneg hpos
    exact hconst (g • x) (MulAction.mem_orbit x g)

/-- Every stationary probability mass for a positive summable generating
law contains a finite uniform orbit. -/
theorem countable_exists_finite_uniform_orbit_of_stationary_probability
    (hweight : ∀ d, 0 < weight d) (hweight_sum : HasSum weight 1)
    (hgenerate : Subgroup.closure (Set.range step) = ⊤)
    (hstationary : IsCountableStationaryMass step weight mass)
    (hnonneg : ∀ x, 0 ≤ mass x) (hmass : HasSum mass 1) :
    ∃ y : X, (MulAction.orbit G y).Finite ∧ 0 < mass y ∧
      ∀ z ∈ MulAction.orbit G y, mass z = mass y := by
  obtain ⟨x, hx⟩ := exists_pos_of_hasSum_one mass hnonneg hmass
  obtain ⟨hxfin, hxconst⟩ :=
    countable_finite_orbit_and_constant_at_positive_atom step weight mass
      hweight hweight_sum hgenerate hstationary hmass.summable hnonneg hx
  exact ⟨x, hxfin, hx, hxconst⟩

end MaximumPrinciple

end IndependentZeroBlocks
