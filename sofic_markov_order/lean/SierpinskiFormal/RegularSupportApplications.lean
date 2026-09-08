import SierpinskiFormal.RegularSupportClassification
import SierpinskiFormal.MatrixRadixRegularity
import SierpinskiFormal.UnifiedObservationTheorem

set_option autoImplicit false
namespace IndependentZeroBlocks
open SierpinskiFormal
open scoped BigOperators

/-- Finite forbidden factors synchronize by concatenation, without needing
a shared state representation of the individual sequences. -/
theorem avoidsDigitWord_finset_union
    {J : Type*} (b : ℕ) (bad : J → ℕ → Prop) (s : Finset J)
    (h : ∀ i ∈ s, ∃ w : List (Fin b), AvoidsDigitWord b (bad i) w) :
    ∃ w : List (Fin b), ∀ i ∈ s, AvoidsDigitWord b (bad i) w := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨[], by simp⟩
  | @insert i s hi ih =>
    obtain ⟨wi, hwi⟩ := h i (Finset.mem_insert_self i s)
    obtain ⟨ws, hws⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    refine ⟨wi ++ ws, ?_⟩
    intro j hj v z
    rcases Finset.mem_insert.mp hj with rfl | hj
    · simpa only [List.append_assoc] using hwi v (ws ++ z)
    · simpa only [List.append_assoc] using hws j hj (v ++ wi) z

theorem hasForbiddenDigitWord_finite_union_iff
    {J : Type*} [Fintype J] (b : ℕ) (hb : 2 ≤ b) (bad : J → ℕ → Prop) :
    HasForbiddenDigitWord b (fun n => ∃ i, bad i n) ↔
      ∀ i, HasForbiddenDigitWord b (bad i) := by
  constructor
  · rintro ⟨w, hlen, hw⟩ i
    exact ⟨w, hlen, fun v z hbad => hw v z ⟨i, hbad⟩⟩
  · intro h
    obtain ⟨w, hw⟩ := avoidsDigitWord_finset_union b bad Finset.univ
      (fun i _ => by obtain ⟨w, _, hw⟩ := h i; exact ⟨w, hw⟩)
    let r : Fin b := ⟨0, by omega⟩
    refine ⟨r :: w, by simp, ?_⟩
    intro v z hbad
    obtain ⟨i, hi⟩ := hbad
    have hh := hw i (Finset.mem_univ i) (v ++ [r]) z
    apply hh
    simpa only [List.append_assoc, List.singleton_append] using hi

/-- Intrinsic finite-family theorem: individual regular sequences need
only share the radix, not a supplied common representation. -/
theorem radixRegular_family_support_classification
    {K J : Type*} [CommRing K] [Fintype J] (b : ℕ) (hb : 2 ≤ b)
    (f : J → ℕ → K) (hregular : ∀ i, IsRadixRegular b (f i)) :
    (HasZeroPredicateDensity (fun n => ∃ i, f i n ≠ 0) ↔
      HasForbiddenDigitWord b (fun n => ∃ i, f i n ≠ 0)) ∧
    (HasUniformRelativeHoles (fun n => ∃ i, f i n ≠ 0) ↔
      HasForbiddenDigitWord b (fun n => ∃ i, f i n ≠ 0)) ∧
    ((∃ α : ℝ, α < 1 ∧ HasUniformPowerIntervalBound α (fun n => ∃ i, f i n ≠ 0)) ↔
      HasForbiddenDigitWord b (fun n => ∃ i, f i n ≠ 0)) ∧
    (HasPositiveLowerPredicateDensity (fun n => ∃ i, f i n ≠ 0) ↔
      ¬HasForbiddenDigitWord b (fun n => ∃ i, f i n ≠ 0)) := by
  have hc := fun i => radixRegular_support_classification b hb (f i) (hregular i)
  have hg := finite_support_geometry_of_component_classification
    (fun i n => f i n ≠ 0) (fun i => HasForbiddenDigitWord b (fun n => f i n ≠ 0))
    (fun i => (hc i).1) (fun i => (hc i).2.1) (fun i => (hc i).2.2.2)
  have hs := hasForbiddenDigitWord_finite_union_iff b hb (fun i n => f i n ≠ 0)
  exact ⟨hg.1.trans hs.symm, hg.2.1.trans hs.symm, hg.2.2.1.trans hs.symm,
    hg.2.2.2.trans (not_congr hs.symm)⟩

/-- Every current coefficient observation of a polynomial matrix dilation
system is intrinsically regular, over any commutative ring. -/
theorem polynomialMatrix_currentObservation_isRadixRegular
    {K I : Type*} [CommRing K] [Fintype I]
    (B : I → I → Polynomial K) (U : I → PowerSeries K)
    (b : ℕ) (hb : 2 ≤ b)
    (hEq : ∀ i, U i = ∑ j, (B i j : PowerSeries K) * dilate b (U j))
    (l : Module.Dual K (I → K)) :
    IsRadixRegular b (fun n => l (fun i => PowerSeries.coeff n (U i))) := by
  let m := polynomialDilationWindowThreshold B b
  let L := matrixCurrentObservation l m (polynomialDilationWindowThreshold_pos B b)
  have h := matrix_observation_isRadixRegular b hb
    (fun r => matrixWindowTransition B b m r.val) (matrixWindowState U m)
    (matrixWindowEnd_recurrence B U b hb hEq) L
  simpa only [L, matrixCurrentObservation_windowState] using h

end IndependentZeroBlocks
