import SierpinskiFormal.ObservationClassification

set_option autoImplicit false
namespace IndependentZeroBlocks

section Certificates
variable {K V I J : Type*} [CommSemiring K] [AddCommMonoid V] [Module K V]

/-- One word annihilates every observed output in all surrounding contexts. -/
def ObservedFamilyWordMortal (T : I → Module.End K V)
    (l : J → Module.Dual K V) (v0 : V) : Prop :=
  ∃ w : List I, ∀ i v z, l i (linearWord T (v ++ w ++ z) v0) = 0

theorem observedFamilyWordMortal_finset
    (T : I → Module.End K V) (l : J → Module.Dual K V) (v0 : V)
    (s : Finset J) (hs : ∀ i ∈ s, ObservedWordMortal T (l i) v0) :
    ∃ w : List I, ∀ i ∈ s, ∀ v z, l i (linearWord T (v ++ w ++ z) v0) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨[], by simp⟩
  | @insert i s hi ih =>
    obtain ⟨wi, hwi⟩ := hs i (Finset.mem_insert_self i s)
    obtain ⟨ws, hws⟩ := ih (fun j hj => hs j (Finset.mem_insert_of_mem hj))
    refine ⟨wi ++ ws, ?_⟩
    intro j hj v z
    rcases Finset.mem_insert.mp hj with rfl | hj
    · simpa only [List.append_assoc] using hwi v (ws ++ z)
    · simpa only [List.append_assoc] using hws j hj (v ++ wi) z

/-- Individual invisible words synchronize by concatenation, including
empty families. No compatibility of observations needs to be assumed. -/
theorem observedFamilyWordMortal_iff [Fintype J]
    (T : I → Module.End K V) (l : J → Module.Dual K V) (v0 : V) :
    ObservedFamilyWordMortal T l v0 ↔ ∀ i, ObservedWordMortal T (l i) v0 := by
  constructor
  · rintro ⟨w, hw⟩ i
    exact ⟨w, hw i⟩
  · intro h
    obtain ⟨w, hw⟩ := observedFamilyWordMortal_finset T l v0 Finset.univ (fun i _ => h i)
    exact ⟨w, fun i => hw i (Finset.mem_univ i)⟩

end Certificates

theorem predicateCount_le_of_imp {small big : ℕ → Prop}
    (h : ∀ n, small n → big n) (N : ℕ) :
    predicateCount small N ≤ predicateCount big N := by
  classical
  unfold predicateCount
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, h n hn.2⟩

theorem HasZeroPredicateDensity.mono {small big : ℕ → Prop}
    (hz : HasZeroPredicateDensity big) (h : ∀ n, small n → big n) :
    HasZeroPredicateDensity small := by
  apply zeroPredicateDensity_of_affine_count_bound small big 1 1 0 (by decide) _ hz
  intro N
  simpa using predicateCount_le_of_imp h N

theorem HasPositiveLowerPredicateDensity.mono {small big : ℕ → Prop}
    (hp : HasPositiveLowerPredicateDensity small) (h : ∀ n, small n → big n) :
    HasPositiveLowerPredicateDensity big := by
  obtain ⟨c, hc, N0, hN⟩ := hp
  refine ⟨c, hc, N0, fun N hN0 => (hN N hN0).trans ?_⟩
  exact_mod_cast predicateCount_le_of_imp h N

/-- Componentwise sparse/dense classification synchronizes for any finite
family, independently of the algebraic source of its support predicates. -/
theorem finite_support_geometry_of_component_classification
    {J : Type*} [Fintype J] (bad : J → ℕ → Prop) (cert : J → Prop)
    (hz : ∀ i, HasZeroPredicateDensity (bad i) ↔ cert i)
    (hh : ∀ i, HasUniformRelativeHoles (bad i) ↔ cert i)
    (hp : ∀ i, HasPositiveLowerPredicateDensity (bad i) ↔ ¬cert i) :
    (HasZeroPredicateDensity (fun n => ∃ i, bad i n) ↔ ∀ i, cert i) ∧
    (HasUniformRelativeHoles (fun n => ∃ i, bad i n) ↔ ∀ i, cert i) ∧
    ((∃ α : ℝ, α < 1 ∧ HasUniformPowerIntervalBound α (fun n => ∃ i, bad i n)) ↔
      ∀ i, cert i) ∧
    (HasPositiveLowerPredicateDensity (fun n => ∃ i, bad i n) ↔ ¬∀ i, cert i) := by
  have hzero : HasZeroPredicateDensity (fun n => ∃ i, bad i n) ↔ ∀ i, cert i := by
    constructor
    · intro h i
      exact (hz i).mp (h.mono (fun n hn => ⟨i, hn⟩))
    · intro h
      exact (HasUniformRelativeHoles.finite_union bad (fun i => (hh i).mpr (h i))).toZeroPredicateDensity
  have hholes : HasUniformRelativeHoles (fun n => ∃ i, bad i n) ↔ ∀ i, cert i := by
    constructor
    · intro h
      exact hzero.mp h.toZeroPredicateDensity
    · intro h
      exact HasUniformRelativeHoles.finite_union bad (fun i => (hh i).mpr (h i))
  refine ⟨hzero, hholes, ?_, ?_⟩
  · constructor
    · rintro ⟨α, hα, h⟩
      exact hzero.mp (h.toPowerPredicateBound.toZeroPredicateDensity hα)
    · intro h
      obtain ⟨α, _, hα, hc⟩ := (hholes.mpr h).exists_uniform_interval_power_bound
      exact ⟨α, hα, hc⟩
  · constructor
    · intro h hcert
      exact h.not_zeroDensity (hzero.mpr hcert)
    · intro h
      push_neg at h
      obtain ⟨i, hi⟩ := h
      exact ((hp i).mpr hi).mono (fun n hn => ⟨i, hn⟩)

end IndependentZeroBlocks
