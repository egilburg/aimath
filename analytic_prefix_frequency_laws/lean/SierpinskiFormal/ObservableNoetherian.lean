import SierpinskiFormal.ObservableSpan

set_option autoImplicit false
namespace IndependentZeroBlocks
open scoped BigOperators

/-- Finite generation of a span can be witnessed by finitely many members
of the original generating family. -/
theorem finite_original_generators_of_fg_span_range
    {K M I : Type*} [Semiring K] [AddCommMonoid M] [Module K M]
    (f : I → M) (hfg : (Submodule.span K (Set.range f)).FG) :
    ∃ (d : ℕ) (w : Fin d → I),
      Submodule.span K (Set.range fun i => f (w i)) =
        Submodule.span K (Set.range f) := by
  classical
  obtain ⟨s, hs⟩ := hfg
  have hmem : ∀ x : s, (x : M) ∈ Submodule.span K (Set.range f) := by
    intro x
    rw [← hs]
    exact Submodule.subset_span x.property
  choose t ht hxt using fun x : s => Submodule.mem_span_finite_of_mem_span (hmem x)
  let S : Finset M := Finset.univ.biUnion t
  have hsub : (S : Set M) ⊆ Set.range f := by
    intro x hx
    obtain ⟨y, _, hy⟩ := Finset.mem_biUnion.mp hx
    exact ht y hy
  have hspan : Submodule.span K (S : Set M) = Submodule.span K (Set.range f) := by
    apply le_antisymm (Submodule.span_mono hsub)
    rw [← hs]
    apply Submodule.span_le.mpr
    intro x hx
    apply Submodule.span_mono (show (t ⟨x, hx⟩ : Set M) ⊆ (S : Set M) from ?_) (hxt ⟨x, hx⟩)
    intro y hy
    exact Finset.mem_biUnion.mpr ⟨⟨x, hx⟩, Finset.mem_univ _, hy⟩
  let e := (Fintype.equivFin S).symm
  have hwords : ∀ i : Fin (Fintype.card S), ∃ w, f w = (e i).val := by
    intro i
    exact hsub (e i).property
  choose w hw using hwords
  refine ⟨Fintype.card S, w, ?_⟩
  have hrange : (Set.range fun i => f (w i)) = (S : Set M) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      change f (w i) ∈ (S : Set M)
      rw [hw]
      exact (e i).property
    · intro hx
      obtain ⟨i, hi⟩ := e.surjective ⟨x, hx⟩
      exact ⟨i, (hw i).trans (congrArg Subtype.val hi)⟩
  rw [hrange, hspan]

/-- Over a commutative semiring, a finitely generated observable row module
already supplies a finite model made of actual word observations. -/
theorem observable_exists_finite_word_model_of_fg
    {K V I : Type*} [CommSemiring K] [AddCommMonoid V] [Module K V]
    (T : I → Module.End K V) (l : Module.Dual K V)
    (hfg : (Submodule.span K (Set.range fun w : List I => l.comp (linearWord T w))).FG) :
    ∃ (d : ℕ) (w : Fin d → List I) (a : Fin d → K)
      (C : I → Matrix (Fin d) (Fin d) K),
      (∀ x, l x = ∑ j, a j * l (linearWord T (w j) x)) ∧
      (∀ r i x, l (linearWord T (w i) (T r x)) =
        ∑ j, C r i j * l (linearWord T (w j) x)) := by
  classical
  obtain ⟨d, w, hw⟩ := finite_original_generators_of_fg_span_range
    (fun w : List I => l.comp (linearWord T w)) hfg
  have hl : l ∈ Submodule.span K (Set.range fun i => l.comp (linearWord T (w i))) := by
    rw [hw]
    apply Submodule.subset_span
    refine ⟨[], ?_⟩
    ext x
    simp
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hl
  have hr : ∀ r i, (l.comp (linearWord T (w i))).comp (T r) ∈
      Submodule.span K (Set.range fun j => l.comp (linearWord T (w j))) := by
    intro r i
    rw [hw]
    apply Submodule.subset_span
    refine ⟨w i ++ [r], ?_⟩
    ext x
    simp [linearWord_append, Module.End.mul_apply]
  have hc : ∀ r i, ∃ c : Fin d → K,
      ∑ j, c j • l.comp (linearWord T (w j)) =
        (l.comp (linearWord T (w i))).comp (T r) := by
    intro r i
    exact (Submodule.mem_span_range_iff_exists_fun K).mp (hr r i)
  choose C hC using hc
  refine ⟨d, w, a, C, ?_, ?_⟩
  · intro x
    have h := congrArg (fun f : Module.Dual K V => f x) ha
    simpa using h.symm
  · intro r i x
    have h := congrArg (fun f : Module.Dual K V => f x) (hC r i)
    simpa using h.symm

/-- No supplied observability hypothesis is necessary when the dual module
is Noetherian. This includes finite modules over Noetherian commutative rings. -/
theorem noetherian_observable_exists_finite_word_model
    {K V I : Type*} [CommSemiring K] [AddCommMonoid V] [Module K V]
    [IsNoetherian K (Module.Dual K V)]
    (T : I → Module.End K V) (l : Module.Dual K V) :
    ∃ (d : ℕ) (w : Fin d → List I) (a : Fin d → K)
      (C : I → Matrix (Fin d) (Fin d) K),
      (∀ x, l x = ∑ j, a j * l (linearWord T (w j) x)) ∧
      (∀ r i x, l (linearWord T (w i) (T r x)) =
        ∑ j, C r i j * l (linearWord T (w j) x)) := by
  exact observable_exists_finite_word_model_of_fg T l (isNoetherian_def.mp inferInstance _)

end IndependentZeroBlocks
