import SierpinskiFormal.PowerExceptionalGaps
import SierpinskiFormal.PowerSupportFamilies
import SierpinskiFormal.SparseIntervalBridges
import SierpinskiFormal.DilationInitialZero

set_option autoImplicit false

namespace IndependentZeroBlocks

open SierpinskiFormal

/-- A finite family of power-sparse coefficient supports can be adjoined to
power-sized common host intervals. The exponents subtract. -/
theorem power_family_adjoin_powerBound
    {K ι κ : Type*} [Semiring K] [Fintype κ]
    (F : ι → PowerSeries K) (G : κ → PowerSeries K) (ρ α : ℝ)
    (hF : HasPowerIntervals ρ (fun n => ∀ i, PowerSeries.coeff n (F i) = 0))
    (hG : ∀ i, HasPowerPredicateBound α (fun n => PowerSeries.coeff n (G i) ≠ 0))
    (hα : 0 ≤ α) (hgap : α < ρ) :
    HasPowerIntervals (ρ - α) (fun n =>
      (∀ i, PowerSeries.coeff n (F i) = 0) ∧
      (∀ i, PowerSeries.coeff n (G i) = 0)) := by
  have hbad := HasPowerPredicateBound.finite_union
    (fun i n => PowerSeries.coeff n (G i) ≠ 0) hG
  apply (hF.avoid_powerBound hbad hα hgap).mono
  intro n hn
  refine ⟨hn.1, ?_⟩
  intro i
  by_contra hi
  exact hn.2 ⟨i, hi⟩

/-- The proportional-host case has surviving exponent `1-α`. -/
theorem proportional_family_adjoin_powerBound
    {K ι κ : Type*} [Semiring K] [Fintype κ]
    (F : ι → PowerSeries K) (G : κ → PowerSeries K) (α : ℝ)
    (hF : HasProportionalIntervals (fun n => ∀ i, PowerSeries.coeff n (F i) = 0))
    (hG : ∀ i, HasPowerPredicateBound α (fun n => PowerSeries.coeff n (G i) ≠ 0))
    (hα : 0 ≤ α) (hgap : α < 1) :
    HasPowerIntervals (1 - α) (fun n =>
      (∀ i, PowerSeries.coeff n (F i) = 0) ∧
      (∀ i, PowerSeries.coeff n (G i) = 0)) :=
  power_family_adjoin_powerBound F G 1 α
    ((hasPowerIntervals_one_iff _).mpr hF) hG hα hgap

/-- Quantitative preservation under adding a power-sparse perturbation to
each member of a finite family. -/
theorem power_family_power_perturbations
    {K ι : Type*} [Semiring K] [Fintype ι]
    (F G : ι → PowerSeries K) (ρ α : ℝ)
    (hF : HasPowerIntervals ρ (fun n => ∀ i, PowerSeries.coeff n (F i) = 0))
    (hG : ∀ i, HasPowerPredicateBound α (fun n => PowerSeries.coeff n (G i) ≠ 0))
    (hα : 0 ≤ α) (hgap : α < ρ) :
    HasPowerIntervals (ρ - α)
      (fun n => ∀ i, PowerSeries.coeff n (F i + G i) = 0) := by
  apply (power_family_adjoin_powerBound F G ρ α hF hG hα hgap).mono
  intro n hn i
  rw [map_add, hn.1 i, hn.2 i, add_zero]

/-- Existing common geometric seed blocks yield a quantitative perturbation
theorem once an exceptional-support exponent is supplied. -/
theorem seed_family_power_perturbations
    {K ι : Type*} [Semiring K] [Fintype ι]
    (q seed : ℕ) (hq : 2 ≤ q) (hseed : 1 ≤ seed)
    (F G : ι → PowerSeries K) (α : ℝ)
    (hF : ∀ i, HasSeedBlocks q seed (F i))
    (hG : ∀ i, HasPowerPredicateBound α (fun n => PowerSeries.coeff n (G i) ≠ 0))
    (hα : 0 ≤ α) (hgap : α < 1) :
    HasPowerIntervals (1 - α)
      (fun n => ∀ i, PowerSeries.coeff n (F i + G i) = 0) := by
  apply power_family_power_perturbations F G 1 α
    ((hasPowerIntervals_one_iff _).mpr
      (proportionalIntervals_of_seed_family F hF hq hseed)) hG hα hgap

/-- For a polynomial matrix dilation system, common long late gaps amplify
to proportional common gaps. This connects the matrix criterion to the
earlier sparse-exception interface. -/
theorem proportionalIntervals_of_polynomial_dilation_zeroBlocks
    {K ι : Type*} [CommRing K] [Fintype ι]
    (B : ι → ι → Polynomial K) (U : ι → PowerSeries K)
    (b : ℕ) (hb : 2 ≤ b)
    (hEq : ∀ i, U i = ∑ j, (B i j : PowerSeries K) * dilate b (U j))
    (hblocks : HasArbitrarilyLongZeroBlocks
      (fun n i => PowerSeries.coeff n (U i))) :
    HasProportionalIntervals (fun n => ∀ i, PowerSeries.coeff n (U i) = 0) := by
  let m := polynomialDilationWindowThreshold B b
  have hm : 1 ≤ m := polynomialDilationWindowThreshold_pos B b
  obtain ⟨s, hs, hz⟩ :=
    (polynomial_dilation_matrix_zeroBlocks_iff_threshold B U b hb hEq).mp hblocks
  let n := s + m - 1
  have hn : m ≤ n := by dsimp [n]; omega
  have hdegree : ∀ i j, (B i j).natDegree ≤ (b - 1) * m := by
    intro i j
    exact (entry_natDegree_le_polynomialDilationMatrixDegree B i j).trans
      (polynomialDilationMatrixDegree_le_threshold_mul B b hb)
  have htrail : ∀ i t, t < m → PowerSeries.coeff (n - t) (U i) = 0 := by
    intro i t ht
    have hindex : n - t = s + (m - 1 - t) := by dsimp [n]; omega
    rw [hindex]
    exact hz i (m - 1 - t) (by change m - 1 - t < m; omega)
  have hdesc := polynomial_dilation_matrix_descendants B U b m n hb hm hn
    hdegree hEq htrail
  have hseed : ∀ i, HasSeedBlocks b n (U i) := by
    intro i
    refine ⟨0, 0, ?_⟩
    intro E _ j _ hj
    exact hdesc E j hj i
  exact proportionalIntervals_of_seed_family U hseed hb (by omega)

/-- The computed finite-window criterion for a polynomial matrix system
survives power-sparse additive perturbations with exponent `1-α`. -/
theorem polynomial_dilation_matrix_power_perturbations
    {K ι : Type*} [CommRing K] [Fintype ι]
    (B : ι → ι → Polynomial K) (U G : ι → PowerSeries K)
    (b : ℕ) (hb : 2 ≤ b)
    (hEq : ∀ i, U i = ∑ j, (B i j : PowerSeries K) * dilate b (U j))
    (hwindow : ∃ s, ∀ i t, t < polynomialDilationWindowThreshold B b →
      PowerSeries.coeff (s + t) (U i) = 0)
    (α : ℝ)
    (hG : ∀ i, HasPowerPredicateBound α (fun n => PowerSeries.coeff n (G i) ≠ 0))
    (hα : 0 ≤ α) (hgap : α < 1) :
    HasPowerIntervals (1 - α)
      (fun n => ∀ i, PowerSeries.coeff n (U i + G i) = 0) := by
  have hblocks := (polynomial_dilation_matrix_zeroBlocks_iff_any_window
    B U b hb hEq).mpr hwindow
  exact power_family_power_perturbations U G 1 α
    ((hasPowerIntervals_one_iff _).mpr
      (proportionalIntervals_of_polynomial_dilation_zeroBlocks B U b hb hEq hblocks))
    hG hα hgap

end IndependentZeroBlocks
