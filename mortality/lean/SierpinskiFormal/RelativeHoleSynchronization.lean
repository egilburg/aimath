import SierpinskiFormal.UniformRelativeHoles

set_option autoImplicit false

/-!
# Synchronization with uniformly porous exceptional supports

Uniform relative holes can be intersected with positive power intervals without
reducing the power exponent.  Taking the finite union of a perturbing family's
coefficient supports therefore preserves the host family's interval scale.
-/

namespace IndependentZeroBlocks

open SierpinskiFormal

/-- A finite family of supports with uniform relative holes can be adjoined to
common positive-power zero intervals without losing the host exponent. -/
theorem power_family_adjoin_uniformRelativeHoles
    {K ι κ : Type*} [Semiring K] [Fintype κ]
    (F : ι → PowerSeries K) (G : κ → PowerSeries K) (ρ : ℝ)
    (hF : HasPowerIntervals ρ
      (fun n => ∀ i, PowerSeries.coeff n (F i) = 0))
    (hρ : 0 < ρ)
    (hG : ∀ i, HasUniformRelativeHoles
      (fun n => PowerSeries.coeff n (G i) ≠ 0)) :
    HasPowerIntervals ρ (fun n =>
      (∀ i, PowerSeries.coeff n (F i) = 0) ∧
      (∀ i, PowerSeries.coeff n (G i) = 0)) := by
  have hbad := HasUniformRelativeHoles.finite_union
    (fun i n => PowerSeries.coeff n (G i) ≠ 0) hG
  apply (hF.avoid_uniformRelativeHoles hρ hbad).mono
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro i
  by_contra hi
  exact hn.2 ⟨i, hi⟩

/-- A finite family of supports with uniform relative holes can be adjoined to
common proportional zero intervals while retaining proportional size. -/
theorem proportional_family_adjoin_uniformRelativeHoles
    {K ι κ : Type*} [Semiring K] [Fintype κ]
    (F : ι → PowerSeries K) (G : κ → PowerSeries K)
    (hF : HasProportionalIntervals
      (fun n => ∀ i, PowerSeries.coeff n (F i) = 0))
    (hG : ∀ i, HasUniformRelativeHoles
      (fun n => PowerSeries.coeff n (G i) ≠ 0)) :
    HasProportionalIntervals (fun n =>
      (∀ i, PowerSeries.coeff n (F i) = 0) ∧
      (∀ i, PowerSeries.coeff n (G i) = 0)) := by
  rw [← hasPowerIntervals_one_iff] at hF ⊢
  exact power_family_adjoin_uniformRelativeHoles F G 1 hF
    (by norm_num) hG

/-- Adding one uniformly porous perturbation to each member of a finite family
preserves common positive-power zero intervals with the same exponent. -/
theorem power_family_uniformRelativeHole_perturbations
    {K ι : Type*} [Semiring K] [Fintype ι]
    (F G : ι → PowerSeries K) (ρ : ℝ)
    (hF : HasPowerIntervals ρ
      (fun n => ∀ i, PowerSeries.coeff n (F i) = 0))
    (hρ : 0 < ρ)
    (hG : ∀ i, HasUniformRelativeHoles
      (fun n => PowerSeries.coeff n (G i) ≠ 0)) :
    HasPowerIntervals ρ
      (fun n => ∀ i, PowerSeries.coeff n (F i + G i) = 0) := by
  apply (power_family_adjoin_uniformRelativeHoles F G ρ hF hρ hG).mono
  intro n hn i
  rw [map_add, hn.1 i, hn.2 i, add_zero]

/-- Adding one uniformly porous perturbation to each member of a finite family
preserves common proportional zero intervals. -/
theorem proportional_family_uniformRelativeHole_perturbations
    {K ι : Type*} [Semiring K] [Fintype ι]
    (F G : ι → PowerSeries K)
    (hF : HasProportionalIntervals
      (fun n => ∀ i, PowerSeries.coeff n (F i) = 0))
    (hG : ∀ i, HasUniformRelativeHoles
      (fun n => PowerSeries.coeff n (G i) ≠ 0)) :
    HasProportionalIntervals
      (fun n => ∀ i, PowerSeries.coeff n (F i + G i) = 0) := by
  rw [← hasPowerIntervals_one_iff] at hF ⊢
  exact power_family_uniformRelativeHole_perturbations F G 1 hF
    (by norm_num) hG

end IndependentZeroBlocks
