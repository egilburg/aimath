import SierpinskiFormal.MinimalRankCompression
import Mathlib.Data.List.SplitOn

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace IndependentZeroBlocks

section Words
variable {C R : Type*} [DecidableEq C]

def markerGaps (e : C) (w : List C) : List (List C) := w.splitOn e

theorem markerGaps_ne_nil (e : C) (w : List C) : markerGaps e w ≠ [] :=
  List.splitOnP_ne_nil _ _

@[simp] theorem intercalate_markerGaps (e : C) (w : List C) :
    [e].intercalate (markerGaps e w) = w :=
  List.intercalate_splitOn (xs := w) e

theorem marker_not_mem_of_mem_markerGaps (e : C) (w g : List C)
    (hg : g ∈ markerGaps e w) : e ∉ g := by
  induction w generalizing g with
  | nil =>
      simp [markerGaps] at hg
      subst g
      simp
  | cons a w ih =>
      by_cases ha : a = e
      · subst a
        simp only [markerGaps, List.splitOn, List.splitOnP_cons,
          beq_self_eq_true, if_true, List.mem_cons] at hg
        rcases hg with rfl | hg
        · simp
        · exact ih g hg
      · have hbeq : (a == e) = false := by simp [ha]
        rw [show markerGaps e (a :: w) =
          (markerGaps e w).modifyHead (a :: ·) by
            simp [markerGaps, List.splitOn, List.splitOnP_cons, hbeq]] at hg
        have hne : markerGaps e w ≠ [] := markerGaps_ne_nil e w
        cases hs : markerGaps e w with
        | nil => exact (hne hs).elim
        | cons d ds =>
            simp only [hs, List.modifyHead_cons, List.mem_cons] at hg
            rcases hg with rfl | hg
            · simp only [List.mem_cons, not_or]
              exact ⟨fun hea ↦ ha hea.symm,
                ih d (by simpa [hs])⟩
            · exact ih g (by simpa [hs] using Or.inr hg)

theorem markerGaps_unique (e : C) (w : List C) (gs : List (List C))
    (hfree : ∀ g ∈ gs, e ∉ g) (hne : gs ≠ [])
    (hw : [e].intercalate gs = w) :
    markerGaps e w = gs := by
  rw [← hw]
  exact List.splitOn_intercalate e hfree hne

/-- Nonempty marker-free gap lists, the canonical renewal coordinates for
finite words. -/
def MarkerGapLists (e : C) :=
  {gs : List (List C) // gs ≠ [] ∧ ∀ g ∈ gs, e ∉ g}

/-- Splitting on the distinguished marker is a bijection between words and
nonempty marker-free gap lists. -/
def markerGapEquiv (e : C) : List C ≃ MarkerGapLists e where
  toFun w := ⟨markerGaps e w, markerGaps_ne_nil e w,
    fun g hg ↦ marker_not_mem_of_mem_markerGaps e w g hg⟩
  invFun gs := [e].intercalate gs.1
  left_inv w := intercalate_markerGaps e w
  right_inv gs := by
    apply Subtype.ext
    exact markerGaps_unique e ([e].intercalate gs.1) gs.1 gs.2.2 gs.2.1 rfl

def wordWeight [Monoid R] (p : C → R) (w : List C) : R :=
  (w.map p).prod

@[simp] theorem wordWeight_nil [Monoid R] (p : C → R) :
    wordWeight p [] = 1 := by simp [wordWeight]

@[simp] theorem wordWeight_cons [Monoid R] (p : C → R) (a : C) (w : List C) :
    wordWeight p (a :: w) = p a * wordWeight p w := by simp [wordWeight]

@[simp] theorem wordWeight_append [Monoid R] (p : C → R) (u v : List C) :
    wordWeight p (u ++ v) = wordWeight p u * wordWeight p v := by
  simp [wordWeight]

def tiltedWordWeight [Monoid R] (s : R) (p : C → R) (w : List C) : R :=
  s ^ w.length * wordWeight p w

@[simp] theorem tiltedWordWeight_nil [Monoid R] (s : R) (p : C → R) :
    tiltedWordWeight s p [] = 1 := by simp [tiltedWordWeight]

@[simp] theorem tiltedWordWeight_append [CommMonoid R]
    (s : R) (p : C → R) (u v : List C) :
    tiltedWordWeight s p (u ++ v) =
      tiltedWordWeight s p u * tiltedWordWeight s p v := by
  simp only [tiltedWordWeight, List.length_append, wordWeight_append, pow_add]
  ac_rfl

theorem length_intercalate_marker (e : C) (g : List C) (gs : List (List C)) :
    ([e].intercalate (g :: gs)).length =
      ((g :: gs).map List.length).sum + gs.length := by
  induction gs generalizing g with
  | nil => simp [List.intercalate]
  | cons z zs ih =>
      simp only [show [e].intercalate (g :: z :: zs) =
        g ++ [e] ++ [e].intercalate (z :: zs) by simp [List.intercalate]]
      simp [ih]
      omega

theorem wordWeight_intercalate_marker [CommMonoid R]
    (p : C → R) (e : C) (g : List C) (gs : List (List C)) :
    wordWeight p ([e].intercalate (g :: gs)) =
      (p e) ^ gs.length * ((g :: gs).map (wordWeight p)).prod := by
  induction gs generalizing g with
  | nil => simp [List.intercalate]
  | cons z zs ih =>
      rw [show [e].intercalate (g :: z :: zs) =
        g ++ [e] ++ [e].intercalate (z :: zs) by simp [List.intercalate]]
      rw [wordWeight_append, wordWeight_append, ih]
      simp only [wordWeight_cons, wordWeight_nil, mul_one, List.length_cons,
        List.map_cons, List.prod_cons, pow_succ]
      ac_rfl

theorem tiltedWordWeight_intercalate_marker [CommMonoid R]
    (s : R) (p : C → R) (e : C) (g : List C) (gs : List (List C)) :
    tiltedWordWeight s p ([e].intercalate (g :: gs)) =
      tiltedWordWeight s p [e] ^ gs.length *
        ((g :: gs).map (tiltedWordWeight s p)).prod := by
  induction gs generalizing g with
  | nil => simp [List.intercalate]
  | cons z zs ih =>
      rw [show [e].intercalate (g :: z :: zs) =
        g ++ [e] ++ [e].intercalate (z :: zs) by simp [List.intercalate]]
      rw [tiltedWordWeight_append, tiltedWordWeight_append, ih]
      simp only [List.length_cons, List.map_cons, List.prod_cons, pow_succ]
      ac_rfl

end Words

section ReturnMatrices
variable {F C ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]
  [DecidableEq C]

theorem returnMatrix_prod_intercalate_marker {r : ℕ}
    (M : C → Matrix ι ι F) (e : C)
    (U : Matrix ι (Fin r) F) (V : Matrix (Fin r) ι F)
    (hfac : matrixWord M [e] = U * V)
    (g : List C) (gs : List (List C)) :
    ((g :: gs).map (returnMatrix M U V)).prod =
      returnMatrix M U V ([e].intercalate (g :: gs)) := by
  induction gs generalizing g with
  | nil => simp [List.intercalate]
  | cons z zs ih =>
      rw [show [e].intercalate (g :: z :: zs) =
        g ++ [e] ++ [e].intercalate (z :: zs) by simp [List.intercalate]]
      rw [List.map_cons, List.prod_cons, ih]
      rw [returnMatrix_mul M [e] U V hfac]

theorem returnMatrix_prod_markerGaps {r : ℕ}
    (M : C → Matrix ι ι F) (e : C)
    (U : Matrix ι (Fin r) F) (V : Matrix (Fin r) ι F)
    (hfac : matrixWord M [e] = U * V) (w : List C) :
    ((markerGaps e w).map (returnMatrix M U V)).prod =
      returnMatrix M U V w := by
  have hne := markerGaps_ne_nil e w
  cases hs : markerGaps e w with
  | nil => exact (hne hs).elim
  | cons g gs =>
      have hw : [e].intercalate (g :: gs) = w := by
        rw [← hs]
        exact intercalate_markerGaps e w
      rw [returnMatrix_prod_intercalate_marker M e U V hfac, hw]

end ReturnMatrices
end IndependentZeroBlocks
