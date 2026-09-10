import FiniteMonoidMortality.ImprovedMortalityBound
import FiniteMonoidMortality.MinimalRankCompression

set_option autoImplicit false

namespace FiniteMonoidMortality

section Flag

variable {K E : Type*} [Ring K] [AddCommGroup E] [Module K E]

theorem flag_product_mem (V : ℕ → Submodule K E) (T : ℕ → Module.End K E)
    (n : ℕ) (hT : ∀ i < n, ∀ x ∈ V (i+1), T i x ∈ V i) :
    ∀ x ∈ V n, ((List.range n).map T).prod x ∈ V 0 := by
  induction n with
  | zero => simpa
  | succ n ih =>
    intro x hx
    have hn : T n x ∈ V n := hT n (by omega) x hx
    have hp := ih (fun i hi => hT i (by omega)) (T n x) hn
    simpa only [List.range_succ, List.map_append, List.map_singleton,
      List.prod_append, List.prod_singleton, Module.End.mul_apply] using hp

theorem flag_product_eq_zero (V : ℕ → Submodule K E) (T : ℕ → Module.End K E)
    (n : ℕ) (hbot : V 0 = ⊥) (htop : V n = ⊤)
    (hT : ∀ i < n, ∀ x ∈ V (i+1), T i x ∈ V i) :
    ((List.range n).map T).prod = 0 := by
  ext x
  have h := flag_product_mem V T n hT x (by simp [htop])
  simpa [hbot] using h

end Flag

theorem matrixWord_flatten {R A ι : Type*} [Semiring R] [Fintype ι] [DecidableEq ι]
    (M : A → Matrix ι ι R) (ws : List (List A)) :
    matrixWord M ws.flatten = (ws.map (matrixWord M)).prod := by
  induction ws with
  | nil => simp [matrixWord]
  | cons w ws ih => simpa [matrixWord, List.map_append, List.prod_append] using congrArg (fun X => matrixWord M w * X) ih

end FiniteMonoidMortality
