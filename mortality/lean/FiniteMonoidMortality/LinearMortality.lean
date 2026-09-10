import FiniteMonoidMortality.FlagMortality
import FiniteMonoidMortality.ImprovedMortalityBound
import FiniteMonoidMortality.MinimalRankCompression
import FiniteMonoidMortality.TwoDimensionalMortality

set_option autoImplicit false

noncomputable section

namespace FiniteMonoidMortality

def endWord {K E A : Type*} [Ring K] [AddCommGroup E] [Module K E]
    (T : A → Module.End K E) (w : List A) : Module.End K E := (w.map T).prod

def factorMortalityBound (d : ℕ) : ℕ := if d=2 then 4 else improvedMortalityBound d

@[simp] theorem factorMortalityBound_one : factorMortalityBound 1=1 := by norm_num [factorMortalityBound,improvedMortalityBound]

@[simp] theorem factorMortalityBound_two : factorMortalityBound 2=4 := by norm_num [factorMortalityBound]

theorem exists_factor_zero_matrix {A : Type*} {d : ℕ} (T : A → Matrix (Fin d) (Fin d) ℝ)
    (hf : (Set.range (matrixWord T)).Finite) (hz : ∃w, matrixWord T w=0) :
    ∃ w, matrixWord T w=0 ∧ w.length ≤ factorMortalityBound d := by
  by_cases hd : d=2
  · subst d
    simpa only [factorMortalityBound_two] using exists_zero_word_length_le_four_real T hf hz
  · simpa only [factorMortalityBound,if_neg hd] using exists_improved_short_zero_word_of_finite_real_monoid T hf hz

theorem exists_factor_zero_end {E A : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (T : A → Module.End ℝ E)
    (hf : (Set.range (endWord T)).Finite) (hz : ∃w, endWord T w=0) :
    ∃ w, endWord T w=0 ∧ w.length ≤ factorMortalityBound (Module.finrank ℝ E) := by
  let b := Module.finBasis ℝ E
  let e := LinearMap.toMatrixAlgEquiv b
  let M := fun a => e (T a)
  have he : ∀w, matrixWord M w=e (endWord T w) := by
    intro w
    induction w with
    | nil => simp [matrixWord,endWord]
    | cons a w ih => simpa [matrixWord,endWord] using congrArg (fun X => e (T a)*X) ih
  have hfm : (Set.range (matrixWord M)).Finite := by
    have hr : Set.range (matrixWord M) = e '' Set.range (endWord T) := by
      rw [← Set.range_comp]
      congr 1
      funext w
      exact he w
    rw [hr]; exact hf.image e
  have hzm : ∃w, matrixWord M w=0 := by
    obtain ⟨w,hw⟩ := hz
    exact ⟨w,by rw [he,hw,map_zero]⟩
  obtain ⟨w,hw,hl⟩ := exists_factor_zero_matrix M hfm hzm
  refine ⟨w,?_,hl⟩
  apply e.injective
  simpa only [he,map_zero] using hw

theorem finite_range_of_fibers {X Y Z : Type*} (f : X → Y) (g : X → Z)
    (hf : (Set.range f).Finite) (hfg : ∀ x y, f x=f y → g x=g y) : (Set.range g).Finite := by
  classical
  let pick : Set.range f → X := fun y => Classical.choose y.property
  let gp : Set.range f → Z := fun y => g (pick y)
  letI : Fintype (Set.range f) := hf.fintype
  apply (Set.finite_range gp).subset
  rintro _ ⟨x,rfl⟩
  refine ⟨⟨f x,⟨x,rfl⟩⟩,?_⟩
  exact hfg _ _ (Classical.choose_spec (show f x ∈ Set.range f from ⟨x,rfl⟩))

end FiniteMonoidMortality
