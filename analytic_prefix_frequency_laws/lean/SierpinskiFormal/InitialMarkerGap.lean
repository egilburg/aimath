import SierpinskiFormal.FiniteIIDWordLaw
import SierpinskiFormal.OneBoundaryMixture

/-! # The initial marker-free gap of an actual one-sided path -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Function
open scoped BigOperators ENNReal
namespace IndependentZeroBlocks

variable {A : Type*} [DecidableEq A]

def firstMarkerTime (e : A) (ω : ℕ → A) : ℕ := by
  classical
  exact if h : ∃ n, ω n = e then Nat.find h else 0

theorem firstMarkerTime_spec (e : A) (ω : ℕ → A) (h : ∃ n, ω n = e) :
    ω (firstMarkerTime e ω) = e := by
  simp only [firstMarkerTime, dif_pos h]
  exact Nat.find_spec h

theorem firstMarkerTime_min (e : A) (ω : ℕ → A) {k : ℕ}
    (hk : k < firstMarkerTime e ω) : ω k ≠ e := by
  by_cases h : ∃ n, ω n = e
  · simpa only [firstMarkerTime, dif_pos h] using Nat.find_min h
      (show k < Nat.find h by simpa [firstMarkerTime, h] using hk)
  · simp [firstMarkerTime, h] at hk

def initialMarkerGap (e : A) (ω : ℕ → A) : GapWords e :=
  ⟨List.ofFn (fun i : Fin (firstMarkerTime e ω) ↦ ω i.val), by
    simp only [List.mem_ofFn, not_exists]
    intro i hi
    exact firstMarkerTime_min e ω i.isLt hi⟩

def wordCylinder (w : List A) : Set (ℕ → A) :=
  {ω | ∀ i : Fin w.length, ω i.val = w[i.val]}

theorem mem_wordCylinder_iff (w : List A) (ω : ℕ → A) :
    ω ∈ wordCylinder w ↔ List.ofFn (fun i : Fin w.length ↦ ω i.val) = w := by
  constructor
  · intro h
    calc
      _ = List.ofFn (fun i : Fin w.length ↦ w[i.val]) := congrArg List.ofFn (funext h)
      _ = w := List.ofFn_getElem
  · intro h i
    have hh := congrArg (fun l : List A ↦ l[i.val]?) h
    simpa using hh

theorem firstMarkerTime_of_cylinder (e : A) (u : GapWords e) (ω : ℕ → A)
    (h : ω ∈ wordCylinder (u.1 ++ [e])) : firstMarkerTime e ω = u.1.length := by
  have he : ω u.1.length = e := by
    simpa using h ⟨u.1.length, by simp⟩
  have hex : ∃ n, ω n = e := ⟨_, he⟩
  apply le_antisymm
  · simp only [firstMarkerTime, dif_pos hex]
    exact Nat.find_min' hex he
  · by_contra hh
    have hlt : firstMarkerTime e ω < u.1.length := by omega
    have hc := h ⟨firstMarkerTime e ω, by simp; omega⟩
    rw [List.getElem_append_left hlt] at hc
    have heq : e = u.1[firstMarkerTime e ω] := (firstMarkerTime_spec e ω hex).symm.trans hc
    exact u.2 ((congrArg (fun a : A ↦ a ∈ u.1) heq).mpr (List.getElem_mem hlt))

theorem initialMarkerGap_of_cylinder (e : A) (u : GapWords e) (ω : ℕ → A)
    (h : ω ∈ wordCylinder (u.1 ++ [e])) : initialMarkerGap e ω = u := by
  apply Subtype.ext
  change List.ofFn (fun i : Fin (firstMarkerTime e ω) ↦ ω i.val) = u.1
  rw [firstMarkerTime_of_cylinder e u ω h]
  apply (mem_wordCylinder_iff u.1 ω).mp
  intro i
  have hc := h ⟨i.val, by simp⟩
  simpa [List.getElem_append_left i.isLt] using hc

theorem mem_initialMarkerGap_cylinder (e : A) (ω : ℕ → A)
    (h : ∃ n, ω n = e) : ω ∈ wordCylinder ((initialMarkerGap e ω).1 ++ [e]) := by
  apply (mem_wordCylinder_iff _ _).mpr
  simp only [initialMarkerGap, List.length_append, List.length_ofFn, List.length_singleton]
  rw [List.ofFn_succ']
  simp [List.concat_eq_append, firstMarkerTime_spec e ω h]

theorem initialMarkerCylinders_disjoint (e : A) :
    Pairwise (Disjoint on fun u : GapWords e ↦ wordCylinder (u.1 ++ [e])) := by
  intro u v huv
  apply Set.disjoint_left.mpr
  intro ω hu hv
  exact huv ((initialMarkerGap_of_cylinder e u ω hu).symm.trans
    (initialMarkerGap_of_cylinder e v ω hv))

theorem eventually_prefix_after_initialMarker (e : A) (ω : ℕ → A)
    (h : ∃ n, ω n = e) : ∀ᶠ n in Filter.atTop, ∃ t : List A,
      stationaryPrefix digitHead digitShift (n + 1) ω =
        (initialMarkerGap e ω).1 ++ [e] ++ t := by
  filter_upwards [Filter.eventually_ge_atTop (firstMarkerTime e ω)] with n hn
  let k := firstMarkerTime e ω + 1
  have hk : k ≤ n + 1 := by dsimp [k]; omega
  refine ⟨List.ofFn (fun i : Fin (n + 1 - k) ↦ ω (k + i.val)), ?_⟩
  rw [FiniteProbabilityWeights.stationaryPrefix_digit_eq_ofFn]
  have hdecomp : n + 1 = k + (n + 1 - k) := by omega
  rw [List.ofFn_congr hdecomp, List.ofFn_add]
  congr 1
  have hc := (mem_wordCylinder_iff _ ω).mp (mem_initialMarkerGap_cylinder e ω h)
  simpa [k, initialMarkerGap] using hc

variable [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]

instance gapWords_countable (e : A) : Countable (GapWords e) :=
  inferInstanceAs (Countable {w : List A // e ∉ w})

instance gapWords_measurableSpace (e : A) : MeasurableSpace (GapWords e) := ⊤

instance gapWords_measurableSingletonClass (e : A) : MeasurableSingletonClass (GapWords e) :=
  ⟨fun _ ↦ trivial⟩

theorem measurableSet_wordCylinder (w : List A) : MeasurableSet (wordCylinder w) := by
  have heq : wordCylinder w = (fun ω : ℕ → A ↦ fun i : Fin w.length ↦ ω i.val) ⁻¹'
      {fun i : Fin w.length ↦ w[i.val]} := by ext ω; simp [wordCylinder, funext_iff]
  rw [heq]
  exact (FiniteProbabilityWeights.measurable_firstCoordinates _)
    (measurableSet_singleton _)

theorem iidMeasure_wordCylinder (P : FiniteProbabilityWeights A) (w : List A) :
    P.iidMeasure (wordCylinder w) = ENNReal.ofReal (wordWeight P.weight w) := by
  let φ : (ℕ → A) → (Fin w.length → A) := fun ω i ↦ ω i.val
  let v : Fin w.length → A := fun i ↦ w[i.val]
  have heq : wordCylinder w = φ ⁻¹' {v} := by ext ω; simp [wordCylinder, φ, v, funext_iff]
  rw [heq, ← Measure.map_apply (FiniteProbabilityWeights.measurable_firstCoordinates _) (measurableSet_singleton v),
    P.map_iidMeasure_firstCoordinates]
  simp only [Measure.infinitePi_singleton_of_fintype, P.letterMeasure_singleton]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ P.nonneg (v i))]
  congr 1
  simp [wordWeight, v, ← List.prod_ofFn, ← List.map_ofFn]

theorem measurableSet_hasMarker (e : A) :
    MeasurableSet {ω : ℕ → A | ∃ n, ω n = e} := by
  simp only [setOf_exists]
  exact MeasurableSet.iUnion fun n ↦ measurableSet_eq_fun (measurable_pi_apply n) measurable_const

theorem hasMarker_eq_union_cylinders (e : A) :
    {ω : ℕ → A | ∃ n, ω n = e} = ⋃ u : GapWords e, wordCylinder (u.1 ++ [e]) := by
  ext ω
  constructor
  · intro h
    exact mem_iUnion.mpr ⟨initialMarkerGap e ω, mem_initialMarkerGap_cylinder e ω h⟩
  · intro h
    obtain ⟨u, hu⟩ := mem_iUnion.mp h
    exact ⟨u.1.length, by simpa using hu ⟨u.1.length, by simp⟩⟩

theorem measurable_initialMarkerGap (e : A) : Measurable (initialMarkerGap e) := by
  apply measurable_to_countable'
  intro u
  let z : GapWords e := ⟨[], by simp⟩
  have hz (ω : ℕ → A) (hω : ¬∃ n, ω n = e) : initialMarkerGap e ω = z := by
    apply Subtype.ext
    simp [initialMarkerGap, firstMarkerTime, hω, z]
  have heq : initialMarkerGap e ⁻¹' {u} = wordCylinder (u.1 ++ [e]) ∪
      ({ω : ℕ → A | ¬∃ n, ω n = e} ∩ {ω : ℕ → A | z = u}) := by
    ext ω
    change initialMarkerGap e ω = u ↔ ω ∈ wordCylinder (u.1 ++ [e]) ∨
      (¬∃ n, ω n = e) ∧ z = u
    constructor
    · intro h
      by_cases hh : ∃ n, ω n = e
      · left
        simpa only [h] using mem_initialMarkerGap_cylinder e ω hh
      · exact Or.inr ⟨hh, (hz ω hh).symm.trans h⟩
    · rintro (h | ⟨hh, rfl⟩)
      · exact initialMarkerGap_of_cylinder e u ω h
      · exact hz ω hh
  rw [heq]
  apply (measurableSet_wordCylinder _).union
  apply (measurableSet_hasMarker e).compl.inter
  by_cases h : z = u <;> simp [h]

variable [Nonempty A] [TopologicalSpace A] [DiscreteTopology A]

theorem ae_hasMarker (P : FiniteProbabilityWeights A) (e : A)
    (he : 0 < P.weight e) : ∀ᵐ ω ∂P.iidMeasure, ∃ n, ω n = e := by
  apply (mem_ae_iff_prob_eq_one (measurableSet_hasMarker e)).mpr
  rw [hasMarker_eq_union_cylinders, measure_iUnion (initialMarkerCylinders_disjoint e)
    (fun u ↦ measurableSet_wordCylinder (u.1 ++ [e]))]
  have ht (u : GapWords e) : P.iidMeasure (wordCylinder (u.1 ++ [e])) =
      ENNReal.ofReal (P.weight e * wordWeight P.weight u.1) := by
    rw [iidMeasure_wordCylinder, wordWeight_append]
    simp [wordWeight, mul_comm]
  simp only [ht]
  have hs := hasSum_markerGapWeight_one P.weight e P.nonneg P.sum_eq_one he
  have hnonneg : ∀ u : GapWords e, 0 ≤ P.weight e * wordWeight P.weight u.1 :=
    fun u ↦ mul_nonneg he.le (wordWeight_nonneg P.weight P.nonneg u.1)
  rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg hs.summable, hs.tsum_eq]
  simp

theorem initialMarkerGap_fiber_ae (P : FiniteProbabilityWeights A) (e : A)
    (he : 0 < P.weight e) (u : GapWords e) :
    initialMarkerGap e ⁻¹' {u} =ᵐ[P.iidMeasure] wordCylinder (u.1 ++ [e]) := by
  filter_upwards [ae_hasMarker P e he] with ω hω
  apply propext
  change initialMarkerGap e ω = u ↔ ω ∈ wordCylinder (u.1 ++ [e])
  constructor
  · intro hh
    change initialMarkerGap e ω = u at hh
    simpa only [hh] using mem_initialMarkerGap_cylinder e ω hω
  · exact initialMarkerGap_of_cylinder e u ω

theorem iidMeasure_initialMarkerGap (P : FiniteProbabilityWeights A) (e : A)
    (he : 0 < P.weight e) (u : GapWords e) :
    P.iidMeasure (initialMarkerGap e ⁻¹' {u}) =
      ENNReal.ofReal (P.weight e * wordWeight P.weight u.1) := by
  rw [measure_congr (initialMarkerGap_fiber_ae P e he u), iidMeasure_wordCylinder]
  simp [wordWeight_append, mul_comm]

end IndependentZeroBlocks
