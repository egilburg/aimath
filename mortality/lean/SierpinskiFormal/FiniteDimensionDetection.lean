import SierpinskiFormal.ObservationCertificate
import SierpinskiFormal.ObservableSpan

set_option autoImplicit false

/-!
# Dimension-bounded detecting contexts

In a finite-dimensional linear representation, both the reachable column
space and the observable row space are spanned by actual words of length
strictly smaller than the ambient dimension.  Consequently failure of an
all-context forbidden word can already be witnessed by one of at most
`d^2` pairs of such short contexts.
-/

namespace IndependentZeroBlocks

section ShortOrbit

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The span of orbit vectors represented by words shorter than `n`. -/
def boundedLinearOrbitSpan (T : ι → Module.End K V) (v0 : V) (n : ℕ) :
    Submodule K V :=
  Submodule.span K (Set.range fun w : {w : List ι // w.length < n} =>
    linearWord T w.1 v0)

theorem boundedLinearOrbitSpan_mono (T : ι → Module.End K V) (v0 : V)
    {m n : ℕ} (hmn : m ≤ n) :
    boundedLinearOrbitSpan T v0 m ≤ boundedLinearOrbitSpan T v0 n := by
  apply Submodule.span_mono
  rintro x ⟨w, rfl⟩
  exact ⟨⟨w.1, w.2.trans_le hmn⟩, rfl⟩

theorem boundedLinearOrbitSpan_le_reachable (T : ι → Module.End K V)
    (v0 : V) (n : ℕ) :
    boundedLinearOrbitSpan T v0 n ≤ linearReachableSpan T v0 := by
  apply Submodule.span_le.mpr
  rintro x ⟨w, rfl⟩
  exact linearWord_mem_linearReachableSpan T v0 w.1

/-- Once two consecutive bounded orbit spans agree, that span is invariant
and therefore already equals the full reachable span. -/
theorem boundedLinearOrbitSpan_eq_reachable_of_succ_eq
    (T : ι → Module.End K V) (v0 : V) (n : ℕ)
    (hstable : boundedLinearOrbitSpan T v0 n =
      boundedLinearOrbitSpan T v0 (n + 1)) :
    boundedLinearOrbitSpan T v0 n = linearReachableSpan T v0 := by
  have hinvariant (r : ι) (x : V)
      (hx : x ∈ boundedLinearOrbitSpan T v0 n) :
      T r x ∈ boundedLinearOrbitSpan T v0 n := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨w, rfl⟩ := hx
        rw [← Module.End.mul_apply, ← linearWord_cons]
        rw [hstable]
        apply Submodule.subset_span
        exact ⟨⟨r :: w.1, by simpa using Nat.succ_le_succ w.2⟩, rfl⟩
    | zero => simp
    | add x y hx hy ihx ihy => simpa using Submodule.add_mem _ ihx ihy
    | smul c x hx ih => simpa using Submodule.smul_mem _ c ih
  apply le_antisymm (boundedLinearOrbitSpan_le_reachable T v0 n)
  apply Submodule.span_le.mpr
  rintro x ⟨w, rfl⟩
  induction w with
  | nil =>
      rw [hstable]
      apply Submodule.subset_span
      exact ⟨⟨[], by simp⟩, by simp⟩
  | cons r w ih =>
      change linearWord T (r :: w) v0 ∈ boundedLinearOrbitSpan T v0 n
      rw [linearWord_cons, Module.End.mul_apply]
      exact hinvariant r _ ih

/-- Words shorter than the ambient dimension span the whole reachable
space.  This includes the zero-dimensional case. -/
theorem boundedLinearOrbitSpan_finrank_eq_reachable [FiniteDimensional K V]
    (T : ι → Module.End K V) (v0 : V) :
    boundedLinearOrbitSpan T v0 (Module.finrank K V) =
      linearReachableSpan T v0 := by
  let d := Module.finrank K V
  by_contra hne
  have hstrict : ∀ n, n < d →
      boundedLinearOrbitSpan T v0 n < boundedLinearOrbitSpan T v0 (n + 1) := by
    intro n hn
    have hle := boundedLinearOrbitSpan_mono T v0 (Nat.le_succ n)
    exact lt_of_le_of_ne hle (fun heq => hne <| le_antisymm
      (boundedLinearOrbitSpan_le_reachable T v0 d) <| by
        rw [← boundedLinearOrbitSpan_eq_reachable_of_succ_eq T v0 n heq]
        exact boundedLinearOrbitSpan_mono T v0 hn.le)
  have hrank : ∀ n, n ≤ d →
      n ≤ Module.finrank K (boundedLinearOrbitSpan T v0 n) := by
    intro n hn
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih =>
        have hnlt : n < d := by omega
        exact (Nat.succ_le_succ (ih (by omega))).trans
          (Nat.succ_le_of_lt (Submodule.finrank_lt_finrank_of_lt (hstrict n hnlt)))
  have hproper : boundedLinearOrbitSpan T v0 d < linearReachableSpan T v0 :=
    lt_of_le_of_ne (boundedLinearOrbitSpan_le_reachable T v0 d) hne
  have hlt := Submodule.finrank_lt_finrank_of_lt hproper
  have hreach : Module.finrank K (linearReachableSpan T v0) ≤ d :=
    Submodule.finrank_le _
  exact (Nat.not_lt_of_ge (hrank d le_rfl)) (hlt.trans_le hreach)

/-- A reachable space has a basis selected from actual words of length
strictly less than the ambient dimension. -/
theorem exists_short_reachable_basisWords [FiniteDimensional K V]
    (T : ι → Module.End K V) (v0 : V) :
    ∃ (q : ℕ) (cols : Fin q → List ι),
      q ≤ Module.finrank K V ∧
      (∀ j, (cols j).length < Module.finrank K V) ∧
      Submodule.span K (Set.range fun j => linearWord T (cols j) v0) =
        linearReachableSpan T v0 := by
  classical
  let d := Module.finrank K V
  let short : Set V := Set.range fun w : {w : List ι // w.length < d} =>
    linearWord T w.1 v0
  obtain ⟨s, hsub, hcard, hspan, _hind⟩ :=
    Submodule.exists_finset_span_eq_linearIndepOn K short
  let e := (Fintype.equivFin s).symm
  have hwords : ∀ j : Fin (Fintype.card s),
      ∃ w : List ι, w.length < d ∧ linearWord T w v0 = (e j).1 := by
    intro j
    obtain ⟨w, hw⟩ := hsub (e j).2
    exact ⟨w.1, w.2, hw⟩
  choose cols hcolsLen hcols using hwords
  refine ⟨Fintype.card s, cols, ?_, hcolsLen, ?_⟩
  · rw [Fintype.card_coe, hcard]
    exact Submodule.finrank_le _
  · have hrange :
        (Set.range fun j => linearWord T (cols j) v0) = (s : Set V) := by
      ext x
      constructor
      · rintro ⟨j, rfl⟩
        change linearWord T (cols j) v0 ∈ (s : Set V)
        rw [hcols j]
        exact (e j).2
      · intro hx
        obtain ⟨j, hj⟩ := e.surjective ⟨x, hx⟩
        exact ⟨j, (hcols j).trans (congrArg Subtype.val hj)⟩
    rw [hrange, hspan]
    exact boundedLinearOrbitSpan_finrank_eq_reachable T v0

end ShortOrbit

section DetectingContexts

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- The action on observation rows induced by precomposition with a digit
transition. -/
def observableDualDigit (T : ι → Module.End K V) (r : ι) :
    Module.End K (Module.Dual K V) :=
  (T r).dualMap

omit [FiniteDimensional K V] in
@[simp] theorem linearWord_observableDualDigit
    (T : ι → Module.End K V) (l : Module.Dual K V) (w : List ι) :
    linearWord (observableDualDigit T) w l = observableWordRow T l w.reverse := by
  induction w with
  | nil => simp [observableDualDigit]
  | cons r w ih =>
      rw [linearWord_cons, Module.End.mul_apply, ih, List.reverse_cons,
        ← observableWordRow_append_singleton]
      rfl

omit [FiniteDimensional K V] in
theorem dual_reachableSpan_eq_observableSpan
    (T : ι → Module.End K V) (l : Module.Dual K V) :
    linearReachableSpan (observableDualDigit T) l = observableSpan T l := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro f ⟨w, rfl⟩
    change linearWord (observableDualDigit T) w l ∈ observableSpan T l
    rw [linearWord_observableDualDigit]
    exact Submodule.subset_span ⟨w.reverse, rfl⟩
  · apply Submodule.span_le.mpr
    rintro f ⟨w, rfl⟩
    rw [← List.reverse_reverse w, ← linearWord_observableDualDigit]
    exact linearWord_mem_linearReachableSpan _ _ w.reverse

/-- The observable row space has a basis of actual word rows whose words
have length strictly less than the ambient dimension. -/
theorem exists_short_observable_basisWords
    (T : ι → Module.End K V) (l : Module.Dual K V) :
    ∃ (p : ℕ) (rows : Fin p → List ι),
      p ≤ Module.finrank K V ∧
      (∀ i, (rows i).length < Module.finrank K V) ∧
      Submodule.span K (Set.range fun i => observableWordRow T l (rows i)) =
        observableSpan T l := by
  obtain ⟨p, words, hp, hlen, hspan⟩ :=
    exists_short_reachable_basisWords (observableDualDigit T) l
  let rows : Fin p → List ι := fun i => (words i).reverse
  refine ⟨p, rows, ?_, ?_, ?_⟩
  · simpa [Subspace.dual_finrank_eq] using hp
  · intro i
    simpa [rows, Subspace.dual_finrank_eq] using hlen i
  · have heq : (Set.range fun i => observableWordRow T l (rows i)) =
        Set.range fun i => linearWord (observableDualDigit T) (words i) l := by
      ext f
      simp only [Set.mem_range]
      constructor <;> rintro ⟨i, rfl⟩ <;>
        exact ⟨i, by simp [rows]⟩
    rw [heq, hspan, dual_reachableSpan_eq_observableSpan]

omit [FiniteDimensional K V] in
/-- If all pairs from short spanning row and column families vanish around
one middle word, that middle word vanishes in every left and right context. -/
theorem observedWordMortal_of_zero_short_basis_contexts
    (T : ι → Module.End K V) (l : Module.Dual K V) (v0 : V)
    {p q : ℕ} (rows : Fin p → List ι) (cols : Fin q → List ι)
    (hrows : Submodule.span K
        (Set.range fun i => observableWordRow T l (rows i)) = observableSpan T l)
    (hcols : Submodule.span K
        (Set.range fun j => linearWord T (cols j) v0) = linearReachableSpan T v0)
    (middle : List ι)
    (hzero : ∀ i j, l (linearWord T (rows i ++ middle ++ cols j) v0) = 0) :
    ∀ x y : List ι, l (linearWord T (x ++ middle ++ y) v0) = 0 := by
  have hrow_on_reachable (i : Fin p) (z : V)
      (hz : z ∈ linearReachableSpan T v0) :
      observableWordRow T l (rows i) (linearWord T middle z) = 0 := by
    rw [← hcols] at hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨j, rfl⟩ := hz
        simpa only [observableWordRow_apply, ← Module.End.mul_apply,
          ← linearWord_append, List.append_assoc] using hzero i j
    | zero => simp
    | add x y hx hy ihx ihy => simp [map_add, ihx, ihy]
    | smul c x hx ih => simp [map_smul, ih]
  intro x y
  have hy : linearWord T y v0 ∈ linearReachableSpan T v0 :=
    linearWord_mem_linearReachableSpan T v0 y
  have hx : observableWordRow T l x ∈ observableSpan T l :=
    Submodule.subset_span ⟨x, rfl⟩
  rw [← hrows] at hx
  have hfunctional (f : Module.Dual K V)
      (hf : f ∈ Submodule.span K
        (Set.range fun i => observableWordRow T l (rows i))) :
      f (linearWord T middle (linearWord T y v0)) = 0 := by
    induction hf using Submodule.span_induction with
    | mem f hf =>
        obtain ⟨i, rfl⟩ := hf
        exact hrow_on_reachable i _ hy
    | zero => simp
    | add f g hf hg ihf ihg => simp [ihf, ihg]
    | smul c f hf ih => simp [ih]
  simpa only [observableWordRow_apply, ← Module.End.mul_apply,
    ← linearWord_append, List.append_assoc] using hfunctional _ hx

/-- Failure of an all-context forbidden word is detected for every middle
word by one of at most `d^2` pairs of contexts, each shorter than `d`. -/
theorem exists_short_detecting_context_bases
    (T : ι → Module.End K V) (l : Module.Dual K V) (v0 : V)
    (himmortal : ¬ObservedWordMortal T l v0) :
    ∃ (p q : ℕ) (rows : Fin p → List ι) (cols : Fin q → List ι),
      p ≤ Module.finrank K V ∧ q ≤ Module.finrank K V ∧
      (∀ i, (rows i).length < Module.finrank K V) ∧
      (∀ j, (cols j).length < Module.finrank K V) ∧
      ∀ middle : List ι, ∃ i j,
        l (linearWord T (rows i ++ middle ++ cols j) v0) ≠ 0 := by
  obtain ⟨p, rows, hp, hrowsLen, hrows⟩ :=
    exists_short_observable_basisWords T l
  obtain ⟨q, cols, hq, hcolsLen, hcols⟩ :=
    exists_short_reachable_basisWords T v0
  refine ⟨p, q, rows, cols, hp, hq, hrowsLen, hcolsLen, ?_⟩
  intro middle
  by_contra hnone
  push_neg at hnone
  apply himmortal
  exact ⟨middle, observedWordMortal_of_zero_short_basis_contexts
    T l v0 rows cols hrows hcols middle hnone⟩

end DetectingContexts

end IndependentZeroBlocks
