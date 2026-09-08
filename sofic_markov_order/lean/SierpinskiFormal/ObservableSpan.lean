import SierpinskiFormal.LinearDigitGeometry
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

set_option autoImplicit false
namespace IndependentZeroBlocks
open scoped BigOperators

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

def observableWordRow (T : ι → Module.End K V) (l : Module.Dual K V)
    (w : List ι) : Module.Dual K V := l.comp (linearWord T w)

def observableSpan (T : ι → Module.End K V) (l : Module.Dual K V) :
    Submodule K (Module.Dual K V) :=
  Submodule.span K (Set.range (observableWordRow T l))

@[simp] theorem observableWordRow_apply
    (T : ι → Module.End K V) (l : Module.Dual K V) (w : List ι) (x : V) :
    observableWordRow T l w x = l (linearWord T w x) := rfl

@[simp] theorem observableWordRow_nil
    (T : ι → Module.End K V) (l : Module.Dual K V) :
    observableWordRow T l [] = l := by
  ext x
  simp [observableWordRow]

theorem observableWordRow_append_singleton
    (T : ι → Module.End K V) (l : Module.Dual K V) (w : List ι) (r : ι) :
    (observableWordRow T l w).comp (T r) = observableWordRow T l (w ++ [r]) := by
  ext x
  simp [observableWordRow, linearWord_append, Module.End.mul_apply]

/-- The observable row space has generators which are actual finite words,
not arbitrary linear combinations of observations. -/
theorem observableSpan_exists_word_generators [FiniteDimensional K V]
    (T : ι → Module.End K V) (l : Module.Dual K V) :
    ∃ (d : ℕ) (w : Fin d → List ι),
      d ≤ Module.finrank K (Module.Dual K V) ∧
      Submodule.span K (Set.range fun i => observableWordRow T l (w i)) =
        observableSpan T l := by
  classical
  obtain ⟨s, hsub, hcard, hspan, hind⟩ :=
    Submodule.exists_finset_span_eq_linearIndepOn K (Set.range (observableWordRow T l))
  let e := (Fintype.equivFin s).symm
  have hwords : ∀ i : Fin (Fintype.card s),
      ∃ w, observableWordRow T l w = (e i).val := by
    intro i
    exact hsub (e i).property
  choose w hw using hwords
  refine ⟨Fintype.card s, w, ?_, ?_⟩
  · simp only [Fintype.card_coe]
    rw [hcard]
    exact Submodule.finrank_le _
  · have hrange : (Set.range fun i => observableWordRow T l (w i)) = (s : Set _) := by
      ext f
      constructor
      · rintro ⟨i, rfl⟩
        change observableWordRow T l (w i) ∈ (s : Set _)
        rw [hw]
        exact (e i).property
      · intro hf
        obtain ⟨i, hi⟩ := e.surjective ⟨f, hf⟩
        exact ⟨i, (hw i).trans (congrArg Subtype.val hi)⟩
    rw [hrange]
    exact hspan

/-- A finite scalar observation admits a closed finite digit model made
entirely of actual future observations. The seed observation is recovered
linearly, and no supplied observability condition is needed. -/
theorem observableSpan_exists_finite_word_model [FiniteDimensional K V]
    (T : ι → Module.End K V) (l : Module.Dual K V) :
    ∃ (d : ℕ) (w : Fin d → List ι) (a : Fin d → K)
      (C : ι → Matrix (Fin d) (Fin d) K),
      d ≤ Module.finrank K V ∧
      (∀ x, l x = ∑ j, a j * l (linearWord T (w j) x)) ∧
      (∀ r i x, l (linearWord T (w i) (T r x)) =
        ∑ j, C r i j * l (linearWord T (w j) x)) := by
  classical
  obtain ⟨d, w, hd, hw⟩ := observableSpan_exists_word_generators T l
  have hl : l ∈ Submodule.span K (Set.range fun i => observableWordRow T l (w i)) := by
    rw [hw]
    exact Submodule.subset_span ⟨[], observableWordRow_nil T l⟩
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hl
  have hr : ∀ r i, (observableWordRow T l (w i)).comp (T r) ∈
      Submodule.span K (Set.range fun j => observableWordRow T l (w j)) := by
    intro r i
    rw [hw, observableWordRow_append_singleton]
    exact Submodule.subset_span ⟨w i ++ [r], rfl⟩
  have hc : ∀ r i, ∃ c : Fin d → K,
      ∑ j, c j • observableWordRow T l (w j) =
        (observableWordRow T l (w i)).comp (T r) := by
    intro r i
    exact (Submodule.mem_span_range_iff_exists_fun K).mp (hr r i)
  choose C hC using hc
  refine ⟨d, w, a, C, by simpa using hd, ?_, ?_⟩
  · intro x
    have h := congrArg (fun f : Module.Dual K V => f x) ha
    simpa using h.symm
  · intro r i x
    have h := congrArg (fun f : Module.Dual K V => f x) (hC r i)
    simpa using h.symm

end IndependentZeroBlocks
