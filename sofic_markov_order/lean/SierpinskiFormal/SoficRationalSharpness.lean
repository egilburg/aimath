import SierpinskiFormal.SoficSharpLaw

set_option autoImplicit false
noncomputable section
namespace IndependentZeroBlocks
open scoped BigOperators

/-- The pair enumeration is arbitrary; the construction works for every enumeration. -/
def canonicalPairEnumeration (n : ℕ) : Fin (n.choose 2) ≃ Set.powersetCard (Fin n) 2 :=
  (Fintype.equivFinOfCardEq (by
    rw [Fintype.card_eq_nat_card, Set.powersetCard.card, Nat.card_fin])).symm

def RationalReal (x : ℝ) : Prop := ∃ q : ℚ, (q : ℝ) = x

namespace RationalReal
@[simp] theorem natCast (n : ℕ) : RationalReal (n : ℝ) := ⟨n, by simp⟩
@[simp] theorem zero : RationalReal 0 := ⟨0, by simp⟩
@[simp] theorem one : RationalReal 1 := ⟨1, by simp⟩
theorem add {x y : ℝ} (hx : RationalReal x) (hy : RationalReal y) : RationalReal (x+y) := by
  rcases hx with ⟨x, rfl⟩; rcases hy with ⟨y, rfl⟩; exact ⟨x+y, by simp⟩
theorem sub {x y : ℝ} (hx : RationalReal x) (hy : RationalReal y) : RationalReal (x-y) := by
  rcases hx with ⟨x, rfl⟩; rcases hy with ⟨y, rfl⟩; exact ⟨x-y, by simp⟩
theorem mul {x y : ℝ} (hx : RationalReal x) (hy : RationalReal y) : RationalReal (x*y) := by
  rcases hx with ⟨x, rfl⟩; rcases hy with ⟨y, rfl⟩; exact ⟨x*y, by simp⟩
theorem inv {x : ℝ} (hx : RationalReal x) : RationalReal x⁻¹ := by
  rcases hx with ⟨x, rfl⟩; exact ⟨x⁻¹, by simp⟩
theorem sum {I : Type*} (s : Finset I) (f : I → ℝ) (h : ∀ i ∈ s, RationalReal (f i)) :
    RationalReal (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (h i (by simp)).add (ih (fun j hj => h j (by simp [hj])))
end RationalReal

variable {Q : Type*} [Fintype Q] [DecidableEq Q] [LinearOrder Q] [Nonempty Q] {D : ℕ}

theorem completionEpsilon_rational : RationalReal (completionEpsilon (Q := Q) D) := by
  unfold completionEpsilon
  rw [one_div]
  exact ((RationalReal.natCast 2).mul (RationalReal.natCast _ ) |>.mul
    (RationalReal.natCast D)).inv

theorem pairTransition_entry_rational (s t : Set.powersetCard Q 2) (i j : Q) :
    RationalReal (endEntry (pairTransition (Pi.basisFun ℝ Q) s t) i j) := by
  simp only [endEntry, pairTransition_pi_apply, Pi.single_apply]
  split_ifs <;> norm_num <;> simp [RationalReal] <;> exact ⟨2, by norm_num⟩

theorem completionResidual_entry_rational (e : Fin D ≃ Set.powersetCard Q 2) (i j : Q) :
    RationalReal (endEntry (completionResidual e) i j) := by
  simp only [endEntry, completionResidual, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  rw [show uniformMean (Pi.single j (1 : ℝ)) i = (Fintype.card Q : ℝ)⁻¹ from
    endEntry_uniformMean i j]
  change RationalReal ((Fintype.card Q : ℝ)⁻¹ - completionEpsilon (Q := Q) D *
    ∑ s : Fin (D-1), endEntry (soficPairChain (Pi.basisFun ℝ Q) e s) i j)
  exact (RationalReal.natCast _).inv.sub (completionEpsilon_rational.mul
    (RationalReal.sum _ _ (fun s _ => pairTransition_entry_rational _ _ i j)))

theorem sharpLetter_entry_rational (e : Fin D ≃ Set.powersetCard Q 2)
    (a : SharpAlphabet Q D) (i j : Q) : RationalReal (endEntry (sharpLetter e a) i j) := by
  cases a with
  | inl s => exact completionEpsilon_rational.mul (pairTransition_entry_rational _ _ i j)
  | inr ij =>
      change RationalReal (endEntry (completionResidual e) ij.1 ij.2 *
        entryMap ij.1 ij.2 (Pi.single j 1) i)
      apply (completionResidual_entry_rational e _ _).mul
      simp only [entryMap_apply, Pi.single_apply]
      split_ifs <;> norm_num <;> exact RationalReal.one

/-- Every dimension at least two has a stationary rational word law of exact
binomial order and that intrinsic Hankel dimension, including dimension two. -/
theorem exists_rational_sharp_word_law (n : ℕ) (hn : 2 ≤ n) :
    ∃ (A : Type) (_ : Fintype A) (L : StationaryWordLaw A)
      (T : A → Module.End ℝ (Fin n → ℝ)),
      (∀ w, L.mass w = representedWord T averageRow (fun _ => 1) w) ∧
      WordReduced T averageRow (fun _ => 1) ∧
      (∀ a i j, RationalReal (endEntry (T a) i j)) ∧
      (∀ a x, (∀ i, 0 ≤ x i) → ∀ i, 0 ≤ T a x i) ∧
      (∑ a, T a) = uniformMean ∧
      Module.finrank ℝ (wordHankelSpan L.mass) = n ∧
      L.ConditionalMarkov (n.choose 2) ∧
      (∀ k < n.choose 2, ¬L.ConditionalMarkov k) := by
  letI : NeZero n := ⟨by omega⟩
  let e := canonicalPairEnumeration n
  have hD := Nat.choose_pos hn
  refine ⟨SharpAlphabet (Fin n) (n.choose 2), inferInstance, sharpLaw e hD,
    sharpLetter e, fun _ => rfl, sharp_reduced e hD, sharpLetter_entry_rational e,
    sharpLetter_nonneg e hD, sum_sharpLetter e, ?_, sharpLaw_exact_order e hD⟩
  simpa using sharpLaw_hankel_dimension e hD

end IndependentZeroBlocks
