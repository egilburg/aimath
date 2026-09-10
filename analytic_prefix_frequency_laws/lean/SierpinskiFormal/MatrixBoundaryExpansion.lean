import SierpinskiFormal.WeightedWordEnumeration
import SierpinskiFormal.FieldReturnGroup
import SierpinskiFormal.RenewalBoundaryMixture
import SierpinskiFormal.RenewalWordGenerating
import Mathlib.Data.Set.Finite.List

set_option autoImplicit false

/-!
# First/last marker expansion of weighted matrix words

Words with at least two occurrences of a distinguished marker have unique
marker-free left and right boundary gaps and an arbitrary middle word.
This file connects that coding to the original exact-length IID word clock.
-/

noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace IndependentZeroBlocks

variable {A : Type*} [DecidableEq A]

structure MarkerBoundary (e : A) where
  left : List A
  middle : List A
  right : List A
  left_free : e ∉ left
  right_free : e ∉ right

/-- Reassemble a word from its first/last marker boundary data. -/
def MarkerBoundary.word (e : A) (t : MarkerBoundary e) : List A :=
  t.left ++ [e] ++ t.middle ++ [e] ++ t.right

@[simp] theorem MarkerBoundary.length_word (e : A) (t : MarkerBoundary e) :
    (t.word e).length = t.left.length + t.middle.length + t.right.length + 2 := by
  simp only [MarkerBoundary.word, List.length_append, List.length_singleton]
  omega

@[simp] theorem MarkerBoundary.wordWeight_word {R : Type*} [CommMonoid R]
    (p : A → R) (e : A) (t : MarkerBoundary e) :
    wordWeight p (t.word e) =
      p e ^ 2 * wordWeight p t.left * wordWeight p t.middle * wordWeight p t.right := by
  simp [MarkerBoundary.word, pow_two]
  ac_rfl

theorem append_marker_inj_of_prefix_free (e : A) :
    ∀ {x₁ x₂ t₁ t₂ : List A}, e ∉ x₁ → e ∉ x₂ →
      x₁ ++ e :: t₁ = x₂ ++ e :: t₂ → x₁ = x₂ ∧ t₁ = t₂ := by
  intro x₁
  induction x₁ with
  | nil =>
      intro x₂ t₁ t₂ _ hx₂ h
      cases x₂ with
      | nil => simpa using h
      | cons a x₂ =>
          simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
          rcases h with ⟨rfl, _⟩
          exact (hx₂ (by simp)).elim
  | cons a x₁ ih =>
      intro x₂ t₁ t₂ hx₁ hx₂ h
      cases x₂ with
      | nil =>
          simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
          rcases h with ⟨rfl, _⟩
          exact (hx₁ (by simp)).elim
      | cons b x₂ =>
          simp only [List.cons_append, List.cons.injEq] at h
          rcases h with ⟨rfl, htail⟩
          simp only [List.mem_cons, not_or] at hx₁ hx₂
          obtain ⟨hx, ht⟩ := ih hx₁.2 hx₂.2 htail
          exact ⟨by simp [hx], ht⟩

theorem marker_append_inj_of_suffix_free (e : A)
    {t₁ t₂ z₁ z₂ : List A} (hz₁ : e ∉ z₁) (hz₂ : e ∉ z₂)
    (h : t₁ ++ e :: z₁ = t₂ ++ e :: z₂) : t₁ = t₂ ∧ z₁ = z₂ := by
  have hr : z₁.reverse ++ e :: t₁.reverse = z₂.reverse ++ e :: t₂.reverse := by
    simpa using congrArg List.reverse h
  obtain ⟨hz, ht⟩ := append_marker_inj_of_prefix_free e
    (by simpa using hz₁) (by simpa using hz₂) hr
  exact ⟨List.reverse_injective ht, List.reverse_injective hz⟩

theorem MarkerBoundary.word_injective (e : A) :
    Function.Injective (MarkerBoundary.word e) := by
  intro t₁ t₂ h
  have h' : t₁.left ++ e :: (t₁.middle ++ e :: t₁.right) =
      t₂.left ++ e :: (t₂.middle ++ e :: t₂.right) := by
    simpa [MarkerBoundary.word, List.append_assoc] using h
  obtain ⟨hleft, htail⟩ := append_marker_inj_of_prefix_free e
    t₁.left_free t₂.left_free h'
  obtain ⟨hmiddle, hright⟩ := marker_append_inj_of_suffix_free e
    t₁.right_free t₂.right_free htail
  cases t₁
  cases t₂
  simp_all

/-- Separate the two marker-free boundary gaps from the unrestricted middle
word. -/
def markerBoundaryEquiv (e : A) :
    MarkerBoundary e ≃ (GapWords e × GapWords e) × List A where
  toFun t := ((⟨t.left, t.left_free⟩, ⟨t.right, t.right_free⟩), t.middle)
  invFun iy :=
    { left := iy.1.1.1
      middle := iy.2
      right := iy.1.2.1
      left_free := iy.1.1.2
      right_free := iy.1.2.2 }
  left_inv t := by cases t; rfl
  right_inv iy := by cases iy; rfl

section Weighted

variable [Fintype A]

/-- Product-weighted sum over all words of one exact length. -/
def exactLengthWordSum (p : A → ℝ) (f : List A → ℝ) (N : ℕ) : ℝ :=
  ∑' w : List A, ({w : List A | w.length = N}.indicator
    (fun u => wordWeight p u * f u)) w

theorem exactLengthWordSum_eq_tuple_sum
    (p : A → ℝ) (f : List A → ℝ) (N : ℕ) :
    exactLengthWordSum p f N =
      ∑ x : Fin N → A, wordWeight p (List.ofFn x) * f (List.ofFn x) := by
  rw [exactLengthWordSum, ← tsum_subtype]
  rw [← tsum_fintype (L := SummationFilter.unconditional (Fin N → A))]
  change (∑' v : List.Vector A N, wordWeight p v.1 * f v.1) = _
  calc
    _ = ∑' v : List.Vector A N,
        wordWeight p (List.ofFn ((Equiv.vectorEquivFin A N) v)) *
          f (List.ofFn ((Equiv.vectorEquivFin A N) v)) := by
      apply tsum_congr
      intro v
      have hlist : List.ofFn ((Equiv.vectorEquivFin A N) v) = v.1 := by
        have hv := congrArg List.Vector.toList (List.Vector.ofFn_get v)
        change List.ofFn v.get = v.toList
        simpa only [List.Vector.toList_ofFn] using hv
      rw [hlist]
    _ = _ := (Equiv.vectorEquivFin A N).tsum_eq
      (fun x : Fin N → A => wordWeight p (List.ofFn x) * f (List.ofFn x))

/-- Exact-length words which do not possess two distinguished boundary
markers. -/
def rareBoundaryWordSum (p : A → ℝ) (f : List A → ℝ) (e : A) (N : ℕ) : ℝ :=
  ∑' w : List A, ({w : List A | w.length = N}.indicator
    ((Set.range (MarkerBoundary.word e))ᶜ.indicator
      (fun u => wordWeight p u * f u))) w

/-- Exact-length contribution parameterized by the unique first and last
marker. -/
def markerBoundaryWordSum (p : A → ℝ) (f : List A → ℝ) (e : A) (N : ℕ) : ℝ :=
  ∑' t : MarkerBoundary e, if (t.word e).length = N then
    wordWeight p (t.word e) * f (t.word e) else 0

theorem exactLengthWordSum_eq_rare_add_markerBoundary
    (p : A → ℝ) (f : List A → ℝ) (e : A) (N : ℕ) :
    exactLengthWordSum p f N =
      rareBoundaryWordSum p f e N + markerBoundaryWordSum p f e N := by
  let lengthSet : Set (List A) := {w | w.length = N}
  let boundarySet : Set (List A) := Set.range (MarkerBoundary.word e)
  let term : List A → ℝ := fun w => wordWeight p w * f w
  have hrare : Summable (fun w : List A =>
      lengthSet.indicator (boundarySetᶜ.indicator term) w) := by
    apply summable_of_finite_support
    exact (List.finite_length_eq A N).subset (by
      intro w hw
      have hmem : w ∈ lengthSet := by
        by_contra hnot
        exact hw (Set.indicator_of_notMem hnot _)
      simpa [lengthSet] using hmem)
  have hboundary : Summable (fun w : List A =>
      lengthSet.indicator (boundarySet.indicator term) w) := by
    apply summable_of_finite_support
    exact (List.finite_length_eq A N).subset (by
      intro w hw
      have hmem : w ∈ lengthSet := by
        by_contra hnot
        exact hw (Set.indicator_of_notMem hnot _)
      simpa [lengthSet] using hmem)
  have hsplit : exactLengthWordSum p f N =
      (∑' w : List A, lengthSet.indicator (boundarySetᶜ.indicator term) w) +
      ∑' w : List A, lengthSet.indicator (boundarySet.indicator term) w := by
    rw [← hrare.tsum_add hboundary]
    apply tsum_congr
    intro w
    by_cases hlen : w ∈ lengthSet
    · rw [Set.indicator_of_mem hlen, Set.indicator_of_mem hlen]
      by_cases hb : w ∈ boundarySet
      · simp [exactLengthWordSum, lengthSet, term, hlen, hb, boundarySet]
      · simp [exactLengthWordSum, lengthSet, term, hlen, hb, boundarySet]
    · simp [exactLengthWordSum, lengthSet, hlen]
  rw [hsplit]
  congr 1
  rw [markerBoundaryWordSum]
  let E : MarkerBoundary e ≃ boundarySet :=
    Equiv.ofInjective (MarkerBoundary.word e) (MarkerBoundary.word_injective e)
  calc
    (∑' w : List A, lengthSet.indicator (boundarySet.indicator term) w) =
        ∑' w : boundarySet, lengthSet.indicator term w.1 := by
      rw [tsum_subtype]
      apply tsum_congr
      intro w
      by_cases hb : w ∈ boundarySet
      · by_cases hl : w ∈ lengthSet <;> simp [hl, hb]
      · by_cases hl : w ∈ lengthSet <;> simp [hl, hb]
    _ = ∑' t : MarkerBoundary e,
        lengthSet.indicator term (E t).1 := (E.tsum_eq _).symm
    _ = _ := by
      apply tsum_congr
      intro t
      simp only [E, Equiv.ofInjective_apply]
      have hEt : ((Equiv.ofInjective (MarkerBoundary.word e)
          (MarkerBoundary.word_injective e)) t).1 = t.word e := rfl
      rw [hEt]
      by_cases hlen : (t.word e).length = N
      · have hlen' : t.left.length + t.middle.length + t.right.length + 2 = N := by
          simpa using hlen
        simp [lengthSet, term, hlen, hlen']
      · have hlen' : ¬t.left.length + t.middle.length + t.right.length + 2 = N := by
          simpa using hlen
        simp [lengthSet, term, hlen, hlen']

end Weighted

section Matrix

variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]

/-- The original scalar nonvanishing predicate on matrix words. -/
def matrixCoefficientNonzero (M : A → Matrix ι ι F)
    (lambda gamma : ι → F) (w : List A) : Bool :=
  nonzeroBool (coordinateRowDual lambda ((matrixWord M w).mulVec gamma))

/-- With fixed marker-free boundaries, the middle word is observed through
its compressed return matrix. -/
def matrixBoundaryCentralPredicate {r : ℕ}
    (M : A → Matrix ι ι F) (U : Matrix ι (Fin r) F)
    (V : Matrix (Fin r) ι F) (lambda gamma : ι → F)
    (x z y : List A) : Bool :=
  nonzeroBool (returnBoundaryDual M x U lambda
    ((returnMatrix M U V y).mulVec (returnBoundarySeed M z V gamma)))

theorem matrixCoefficientNonzero_boundary {r : ℕ}
    (M : A → Matrix ι ι F) (e : A)
    (U : Matrix ι (Fin r) F) (V : Matrix (Fin r) ι F)
    (hfac : matrixWord M [e] = U * V)
    (lambda gamma : ι → F) (x y z : List A) :
    matrixCoefficientNonzero M lambda gamma (x ++ [e] ++ y ++ [e] ++ z) =
      matrixBoundaryCentralPredicate M U V lambda gamma x z y := by
  apply congrArg nonzeroBool
  have h := coefficient_boundary_resetSandwichWord
    M [e] x z U V hfac [y] lambda gamma
  simpa [matrixCoefficientNonzero, matrixBoundaryCentralPredicate,
    returnBoundaryDual, returnBoundarySeed, resetSandwichWord,
    List.append_assoc, Matrix.mul_assoc] using h

variable [TopologicalSpace A] [DiscreteTopology A] [Fintype A] [Nonempty A]

def matrixBoundaryWeight (p : A → ℝ) (e : A)
    (i : GapWords e × GapWords e) : ℝ :=
  p e ^ 2 * wordWeight p i.1.1 * wordWeight p i.2.1

def matrixBoundaryDelay (e : A) (i : GapWords e × GapWords e) : ℕ :=
  i.1.1.length + i.2.1.length + 2

def matrixBoundaryCentralSequence {r : ℕ}
    (p : A → ℝ) (e : A) (M : A → Matrix ι ι F)
    (U : Matrix ι (Fin r) F) (V : Matrix (Fin r) ι F)
    (lambda gamma : ι → F) (i : GapWords e × GapWords e) (n : ℕ) : ℝ :=
  weightedWordExtensionAverage p
    (booleanWordIndicator (matrixBoundaryCentralPredicate M U V lambda gamma
      i.1.1 i.2.1)) n []

def matrixBoundaryMixture {r : ℕ}
    (p : A → ℝ) (M : A → Matrix ι ι F) (e : A)
    (U : Matrix ι (Fin r) F) (V : Matrix (Fin r) ι F)
    (lambda gamma : ι → F) : ℕ → ℝ :=
  renewalBoundaryMixture (matrixBoundaryWeight p e) (matrixBoundaryDelay e)
    (matrixBoundaryCentralSequence p e M U V lambda gamma)

theorem markerBoundaryMatrixSum_eq_mixture {r : ℕ}
    (p : A → ℝ) (M : A → Matrix ι ι F) (e : A)
    (U : Matrix ι (Fin r) F) (V : Matrix (Fin r) ι F)
    (lambda gamma : ι → F) (N : ℕ) :
    (∑' t : MarkerBoundary e,
      if (t.word e).length = N then
        p e ^ 2 * wordWeight p t.left * wordWeight p t.middle *
          wordWeight p t.right *
          boolIndicator (matrixBoundaryCentralPredicate
            M U V lambda gamma t.left t.right t.middle)
      else 0) = matrixBoundaryMixture p M e U V lambda gamma N := by
  let E := markerBoundaryEquiv e
  let original : MarkerBoundary e → ℝ := fun t =>
    if (t.word e).length = N then
      p e ^ 2 * wordWeight p t.left * wordWeight p t.middle *
        wordWeight p t.right *
        boolIndicator (matrixBoundaryCentralPredicate
          M U V lambda gamma t.left t.right t.middle)
    else 0
  let separated : (GapWords e × GapWords e) × List A → ℝ := fun iy =>
    if matrixBoundaryDelay e iy.1 + iy.2.length = N then
      matrixBoundaryWeight p e iy.1 * wordWeight p iy.2 *
        boolIndicator (matrixBoundaryCentralPredicate
          M U V lambda gamma iy.1.1.1 iy.1.2.1 iy.2)
    else 0
  have horiginal : Summable original := by
    apply summable_of_finite_support
    have hfin := (List.finite_length_eq A N).preimage
      (MarkerBoundary.word_injective e).injOn
    exact hfin.subset (by
      intro t ht
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      by_contra hlen
      apply ht
      dsimp only [original]
      rw [if_neg hlen])
  have hcompose : separated ∘ E = original := by
    funext t
    change separated (markerBoundaryEquiv e t) = original t
    change (if t.left.length + t.right.length + 2 + t.middle.length = N then
        p e ^ 2 * wordWeight p t.left * wordWeight p t.right *
          wordWeight p t.middle * boolIndicator (matrixBoundaryCentralPredicate
            M U V lambda gamma t.left t.right t.middle) else 0) =
      if (t.word e).length = N then
        p e ^ 2 * wordWeight p t.left * wordWeight p t.middle *
          wordWeight p t.right * boolIndicator (matrixBoundaryCentralPredicate
            M U V lambda gamma t.left t.right t.middle) else 0
    by_cases hsep : t.left.length + t.right.length + 2 + t.middle.length = N
    · have hword : (t.word e).length = N := by
        rw [MarkerBoundary.length_word]
        omega
      rw [if_pos hsep, if_pos hword]
      ring
    · have hword : ¬(t.word e).length = N := by
        intro h
        apply hsep
        rw [MarkerBoundary.length_word] at h
        omega
      rw [if_neg hsep, if_neg hword]
  have hseparated : Summable separated := by
    apply (E.summable_iff).mp
    rw [hcompose]
    exact horiginal
  change (∑' t : MarkerBoundary e, original t) = _
  calc
    (∑' t : MarkerBoundary e, original t) =
        ∑' iy : (GapWords e × GapWords e) × List A, separated iy := by
      rw [← E.tsum_eq separated]
      exact tsum_congr (fun t => (congrFun hcompose t).symm)
    _ = ∑' i : GapWords e × GapWords e, ∑' y : List A, separated (i, y) :=
      hseparated.tsum_prod
    _ = matrixBoundaryMixture p M e U V lambda gamma N := by
      rw [matrixBoundaryMixture, renewalBoundaryMixture]
      apply tsum_congr
      intro i
      by_cases hd : matrixBoundaryDelay e i ≤ N
      · let m := N - matrixBoundaryDelay e i
        have hlen (y : List A) :
            matrixBoundaryDelay e i + y.length = N ↔ y.length = m := by
          dsimp [m]
          omega
        calc
          (∑' y : List A, separated (i, y)) =
              matrixBoundaryWeight p e i *
                exactLengthWordSum p
                  (fun y => boolIndicator (matrixBoundaryCentralPredicate
                    M U V lambda gamma i.1.1 i.2.1 y)) m := by
            rw [exactLengthWordSum]
            rw [← tsum_mul_left]
            apply tsum_congr
            intro y
            by_cases hy : y.length = m
            · have hc : matrixBoundaryDelay e i + y.length = N := (hlen y).mpr hy
              rw [show separated (i, y) = matrixBoundaryWeight p e i *
                  wordWeight p y * boolIndicator (matrixBoundaryCentralPredicate
                    M U V lambda gamma i.1.1 i.2.1 y) by
                dsimp only [separated]
                rw [if_pos hc]]
              rw [Set.indicator_of_mem (by simpa using hy)]
              ring
            · have hc : ¬matrixBoundaryDelay e i + y.length = N :=
                fun h => hy ((hlen y).mp h)
              rw [show separated (i, y) = 0 by
                dsimp only [separated]
                rw [if_neg hc]]
              rw [Set.indicator_of_notMem (by simpa using hy)]
              simp
          _ = matrixBoundaryWeight p e i *
              matrixBoundaryCentralSequence p e M U V lambda gamma i m := by
            rw [exactLengthWordSum_eq_tuple_sum]
            rw [matrixBoundaryCentralSequence,
              weightedWordExtensionAverage_eq_tuple_sum]
            simp only [List.nil_append, booleanWordIndicator_apply]
          _ = matrixBoundaryWeight p e i *
              delayedSequence (matrixBoundaryDelay e i)
                (matrixBoundaryCentralSequence p e M U V lambda gamma i) N := by
            simp [delayedSequence, hd, m]
      · have hnone : ∀ y : List A,
            ¬matrixBoundaryDelay e i + y.length = N := by
          intro y h
          omega
        simp [separated, hnone, delayedSequence, hd]

/-- Exact first/last marker expansion for the scalar matrix-word support
average at physical word length `N`.  The rare term consists precisely of
words having fewer than two marker occurrences; every remaining word is
represented once by `MarkerBoundary.word_injective`. -/
theorem weightedMatrixCoefficient_eq_rare_add_boundary {r : ℕ}
    (p : A → ℝ) (M : A → Matrix ι ι F) (e : A)
    (U : Matrix ι (Fin r) F) (V : Matrix (Fin r) ι F)
    (hfac : matrixWord M [e] = U * V)
    (lambda gamma : ι → F) (N : ℕ) :
    weightedWordExtensionAverage p
        (booleanWordIndicator (matrixCoefficientNonzero M lambda gamma)) N [] =
      rareBoundaryWordSum p
          (fun w => boolIndicator (matrixCoefficientNonzero M lambda gamma w)) e N +
        ∑' t : MarkerBoundary e,
          if (t.word e).length = N then
            p e ^ 2 * wordWeight p t.left * wordWeight p t.middle *
              wordWeight p t.right *
              boolIndicator (matrixBoundaryCentralPredicate
                M U V lambda gamma t.left t.right t.middle)
          else 0 := by
  rw [weightedWordExtensionAverage_eq_tuple_sum]
  simp only [List.nil_append, booleanWordIndicator_apply]
  rw [← exactLengthWordSum_eq_tuple_sum p
    (fun w => boolIndicator (matrixCoefficientNonzero M lambda gamma w)) N]
  rw [exactLengthWordSum_eq_rare_add_markerBoundary]
  congr 1
  rw [markerBoundaryWordSum]
  apply tsum_congr
  intro t
  by_cases hlen : (t.word e).length = N
  · simp only [hlen, if_true]
    rw [MarkerBoundary.wordWeight_word]
    rw [show t.word e = t.left ++ [e] ++ t.middle ++ [e] ++ t.right by rfl]
    rw [matrixCoefficientNonzero_boundary M e U V hfac]
  · have hlen' : ¬t.left.length + t.middle.length + t.right.length + 2 = N := by
      simpa using hlen
    simp [hlen, hlen']

/-- The same exact expansion in the delayed-mixture form consumed by
`tendsto_realCesaroMean_renewalBoundaryMixture`. -/
theorem weightedMatrixCoefficient_eq_rare_add_mixture {r : ℕ}
    (p : A → ℝ) (M : A → Matrix ι ι F) (e : A)
    (U : Matrix ι (Fin r) F) (V : Matrix (Fin r) ι F)
    (hfac : matrixWord M [e] = U * V)
    (lambda gamma : ι → F) (N : ℕ) :
    weightedWordExtensionAverage p
        (booleanWordIndicator (matrixCoefficientNonzero M lambda gamma)) N [] =
      rareBoundaryWordSum p
          (fun w => boolIndicator (matrixCoefficientNonzero M lambda gamma w)) e N +
        matrixBoundaryMixture p M e U V lambda gamma N := by
  rw [weightedMatrixCoefficient_eq_rare_add_boundary
    p M e U V hfac lambda gamma N]
  rw [markerBoundaryMatrixSum_eq_mixture]

end Matrix

end IndependentZeroBlocks
