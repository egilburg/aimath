import FiniteMonoidMortality.FlagMortality
import FiniteMonoidMortality.LinearMortality
import Mathlib.LinearAlgebra.Quotient.Basic

set_option autoImplicit false

noncomputable section

namespace FiniteMonoidMortality

section Quotients

variable {E A : Type*} [AddCommGroup E] [Module ℝ E]

theorem endWord_mem (T : A → Module.End ℝ E) (U : Submodule ℝ E)
    (hU : ∀ a x, x ∈ U → T a x ∈ U) (w : List A) :
    ∀ x ∈ U, endWord T w x ∈ U := by
  induction w with
  | nil => simpa [endWord]
  | cons a w ih =>
    intro x hx
    exact hU a _ (ih x hx)

abbrev flagSection (U V : Submodule ℝ E) := U ⧸ V.comap U.subtype

def flagSectionLetter (T : A → Module.End ℝ E) (U V : Submodule ℝ E)
    (hU : ∀ a x, x ∈ U → T a x ∈ U) (hV : ∀ a x, x ∈ V → T a x ∈ V)
    (a : A) : Module.End ℝ (flagSection U V) :=
  (V.comap U.subtype).mapQ (V.comap U.subtype)
    ((T a).restrict (fun x hx => hU a x hx)) (by
      intro x hx
      exact hV a x hx)

theorem flagSection_word_apply (T : A → Module.End ℝ E) (U V : Submodule ℝ E)
    (hU : ∀ a x, x ∈ U → T a x ∈ U) (hV : ∀ a x, x ∈ V → T a x ∈ V)
    (w : List A) (x : U) :
    endWord (flagSectionLetter T U V hU hV) w (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (⟨endWord T w x,endWord_mem T U hU w x x.property⟩ : U) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    change flagSectionLetter T U V hU hV a
      (endWord (flagSectionLetter T U V hU hV) w (Submodule.Quotient.mk x)) = _
    rw [ih]
    rfl

theorem exists_short_word_maps_into
    [FiniteDimensional ℝ E] (T : A → Module.End ℝ E) (U V : Submodule ℝ E)
    (hU : ∀ a x, x ∈ U → T a x ∈ U) (hV : ∀ a x, x ∈ V → T a x ∈ V)
    (hf : (Set.range (endWord T)).Finite) (hz : ∃w, endWord T w=0) :
    ∃ w : List A, (∀ x ∈ U, endWord T w x ∈ V) ∧
      w.length ≤ factorMortalityBound (Module.finrank ℝ (flagSection U V)) := by
  let F := flagSectionLetter T U V hU hV
  have hFfinite : (Set.range (endWord F)).Finite := by
    apply finite_range_of_fibers (endWord T) (endWord F) hf
    intro w z he
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      change endWord (flagSectionLetter T U V hU hV) w (Submodule.Quotient.mk x) =
        endWord (flagSectionLetter T U V hU hV) z (Submodule.Quotient.mk x)
      rw [flagSection_word_apply,flagSection_word_apply]
      congr 1
      apply Subtype.ext
      exact LinearMap.congr_fun he x
  have hFzero : ∃ w, endWord F w=0 := by
    obtain ⟨w,hw⟩ := hz
    refine ⟨w,?_⟩
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      change endWord (flagSectionLetter T U V hU hV) w (Submodule.Quotient.mk x)=0
      rw [flagSection_word_apply]
      have he : (⟨endWord T w x,endWord_mem T U hU w x x.property⟩ : U)=0 := by
        apply Subtype.ext
        simp [hw]
      rw [he]
      rfl
  obtain ⟨w,hw,hl⟩ := exists_factor_zero_end F hFfinite hFzero
  refine ⟨w,?_,hl⟩
  intro x hx
  have he := LinearMap.congr_fun hw (Submodule.Quotient.mk (⟨x,hx⟩ : U))
  change endWord (flagSectionLetter T U V hU hV) w (Submodule.Quotient.mk (⟨x,hx⟩ : U))=0 at he
  rw [flagSection_word_apply] at he
  exact (Submodule.Quotient.mk_eq_zero (V.comap U.subtype)).mp he

theorem exists_zero_word_of_invariant_flag
    [FiniteDimensional ℝ E] (T : A → Module.End ℝ E) (V : ℕ → Submodule ℝ E)
    (n : ℕ) (hbot : V 0=⊥) (htop : V n=⊤)
    (hV : ∀ a i, i ≤ n → ∀ x ∈ V i, T a x ∈ V i)
    (hf : (Set.range (endWord T)).Finite) (hz : ∃w, endWord T w=0) :
    ∃ w : List A, endWord T w=0 ∧
      w.length ≤ ((List.range n).map (fun i =>
        factorMortalityBound (Module.finrank ℝ (flagSection (V (i+1)) (V i))))).sum := by
  classical
  have hlocal : ∀ i : Fin n, ∃ w : List A,
      (∀ x ∈ V (i.val+1), endWord T w x ∈ V i.val) ∧
        w.length ≤ factorMortalityBound (Module.finrank ℝ (flagSection (V (i.val+1)) (V i.val))) := by
    intro i
    exact exists_short_word_maps_into T (V (i.val+1)) (V i.val)
      (fun a => hV a _ (by omega)) (fun a => hV a _ (by omega)) hf hz
  choose ws hws hlen using hlocal
  let wsN : ℕ → List A := fun i => if h : i<n then ws ⟨i,h⟩ else []
  have hmaps : ∀ i<n, ∀ x ∈ V (i+1), endWord T (wsN i) x ∈ V i := by
    intro i hi
    simpa only [wsN,dif_pos hi] using hws ⟨i,hi⟩
  have hlengths : ∀ i<n, (wsN i).length ≤
      factorMortalityBound (Module.finrank ℝ (flagSection (V (i+1)) (V i))) := by
    intro i hi
    simpa only [wsN,dif_pos hi] using hlen ⟨i,hi⟩
  let w := ((List.range n).map wsN).flatten
  refine ⟨w,?_,?_⟩
  · have hp : ∀ L : List (List A), endWord T L.flatten=(L.map (endWord T)).prod := by
      intro L
      induction L with
      | nil => simp [endWord]
      | cons l L ih => simpa [endWord,List.map_append,List.prod_append] using congrArg (fun X => endWord T l*X) ih
    rw [show w=((List.range n).map wsN).flatten from rfl,hp]
    simpa only [List.map_map,Function.comp_def] using
      flag_product_eq_zero V (fun i => endWord T (wsN i)) n hbot htop hmaps
  · have hh := List.sum_le_sum (l := List.range n) (fun i hi => hlengths i (List.mem_range.mp hi))
    simpa only [w,List.length_flatten,List.map_map,Function.comp_def] using hh

theorem flagSection_finrank_add [FiniteDimensional ℝ E] (U V : Submodule ℝ E) (hVU : V ≤ U) :
    Module.finrank ℝ (flagSection U V)+Module.finrank ℝ V=Module.finrank ℝ U := by
  have hh := (V.comap U.subtype).finrank_quotient_add_finrank
  rw [(Submodule.comapSubtypeEquivOfLe hVU).finrank_eq] at hh
  exact hh

theorem flag_dimensions_sum [FiniteDimensional ℝ E] (V : ℕ → Submodule ℝ E)
    (n : ℕ) (hmono : ∀ i<n, V i ≤ V (i+1)) :
    ((List.range n).map (fun i => Module.finrank ℝ (flagSection (V (i+1)) (V i)))).sum +
      Module.finrank ℝ (V 0)=Module.finrank ℝ (V n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hi := ih (fun i hi => hmono i (by omega))
    have hs := flagSection_finrank_add (V (n+1)) (V n) (hmono n (by omega))
    simp only [List.range_succ,List.map_append,List.map_singleton,List.sum_append,List.sum_singleton]
    omega

theorem exists_zero_word_linear_bound_of_small_factors
    [FiniteDimensional ℝ E] (T : A → Module.End ℝ E) (V : ℕ → Submodule ℝ E)
    (n : ℕ) (hbot : V 0=⊥) (htop : V n=⊤)
    (hmono : ∀ i<n, V i ≤ V (i+1))
    (hsmall : ∀ i<n, Module.finrank ℝ (flagSection (V (i+1)) (V i))=1 ∨
      Module.finrank ℝ (flagSection (V (i+1)) (V i))=2)
    (hV : ∀ a i, i ≤ n → ∀ x ∈ V i, T a x ∈ V i)
    (hf : (Set.range (endWord T)).Finite) (hz : ∃w, endWord T w=0) :
    ∃ w : List A, endWord T w=0 ∧ w.length ≤ 2*Module.finrank ℝ E := by
  obtain ⟨w,hw,hl⟩ := exists_zero_word_of_invariant_flag T V n hbot htop hV hf hz
  refine ⟨w,hw,hl.trans ?_⟩
  have hd := flag_dimensions_sum V n hmono
  have hb0 : Module.finrank ℝ (V 0)=0 := by rw [hbot]; exact finrank_bot ℝ E
  have htn : Module.finrank ℝ (V n)=Module.finrank ℝ E := by rw [htop]; exact finrank_top ℝ E
  rw [hb0,htn,Nat.add_zero] at hd
  have hb : ∀ i ∈ List.range n,
      factorMortalityBound (Module.finrank ℝ (flagSection (V (i+1)) (V i))) ≤
        2*Module.finrank ℝ (flagSection (V (i+1)) (V i)) := by
    intro i hi
    rcases hsmall i (List.mem_range.mp hi) with h | h <;> simp [h]
  have hh := List.sum_le_sum hb
  simpa only [List.sum_map_mul_left,hd] using hh

theorem small_factor_cost_sum (ds : List ℕ) (hds : ∀ d ∈ ds, d=1 ∨ d=2) :
    (ds.map factorMortalityBound).sum=ds.count 1+4*ds.count 2 := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    have hd := hds d (by simp)
    have hi := ih (fun x hx => hds x (by simp [hx]))
    rcases hd with rfl | rfl <;> simp [hi] <;> omega

theorem exists_zero_word_prescribed_small_factors
    [FiniteDimensional ℝ E] (T : A → Module.End ℝ E) (V : ℕ → Submodule ℝ E)
    (n k1 k2 : ℕ) (hbot : V 0=⊥) (htop : V n=⊤)
    (hsmall : ∀ i<n, Module.finrank ℝ (flagSection (V (i+1)) (V i))=1 ∨
      Module.finrank ℝ (flagSection (V (i+1)) (V i))=2)
    (hk1 : ((List.range n).map (fun i => Module.finrank ℝ (flagSection (V (i+1)) (V i)))).count 1=k1)
    (hk2 : ((List.range n).map (fun i => Module.finrank ℝ (flagSection (V (i+1)) (V i)))).count 2=k2)
    (hV : ∀ a i, i ≤ n → ∀ x ∈ V i, T a x ∈ V i)
    (hf : (Set.range (endWord T)).Finite) (hz : ∃w, endWord T w=0) :
    ∃ w : List A, endWord T w=0 ∧ w.length ≤ k1+4*k2 := by
  obtain ⟨w,hw,hl⟩ := exists_zero_word_of_invariant_flag T V n hbot htop hV hf hz
  have hh := small_factor_cost_sum ((List.range n).map (fun i =>
    Module.finrank ℝ (flagSection (V (i+1)) (V i)))) (by
      intro d hd
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hd
      exact hsmall i (List.mem_range.mp hi))
  rw [hk1,hk2] at hh
  simp only [List.map_map,Function.comp_def] at hh
  exact ⟨w,hw,by simpa only [hh] using hl⟩

end Quotients

end FiniteMonoidMortality
