import SoficMarkovOrder.PositiveCompletion

set_option autoImplicit false
noncomputable section

namespace SoficMarkovOrder
open scoped BigOperators

variable {Q : Type*} [Fintype Q] [DecidableEq Q] [LinearOrder Q] [Nonempty Q]
  {D : ℕ}

abbrev SharpAlphabet (Q : Type*) (D : ℕ) := Sum (Fin (D - 1)) (Q × Q)

def sharpLetter (e : Fin D ≃ Set.powersetCard Q 2) :
    SharpAlphabet Q D → Module.End ℝ (Q → ℝ)
  | .inl s => completionEpsilon (Q := Q) D • pairChain (Pi.basisFun ℝ Q) e s
  | .inr ij => endEntry (completionResidual e) ij.1 ij.2 • entryMap ij.1 ij.2

theorem sum_sharpLetter (e : Fin D ≃ Set.powersetCard Q 2) :
    (∑ a : SharpAlphabet Q D, sharpLetter e a) = uniformMean := by
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [sharpLetter]
  rw [← Finset.smul_sum, end_eq_sum_entryMap]
  simp [completionResidual]

theorem sharpLetter_nonneg (e : Fin D ≃ Set.powersetCard Q 2) (hD : 0 < D)
    (a : SharpAlphabet Q D) (x : Q → ℝ) (hx : ∀ i, 0 ≤ x i) (i : Q) :
    0 ≤ sharpLetter e a x i := by
  cases a with
  | inl s =>
      exact mul_nonneg (completionEpsilon_pos (Q := Q) hD).le
        (pairTransition_nonneg _ _ x hx i)
  | inr ij =>
      change 0 ≤ endEntry (completionResidual e) ij.1 ij.2 * entryMap ij.1 ij.2 x i
      apply mul_nonneg (completionResidual_entry_pos e hD _ _).le
      rw [entryMap_apply]
      exact mul_nonneg (hx _) (by split_ifs <;> norm_num)

theorem sharpWord_nonneg (e : Fin D ≃ Set.powersetCard Q 2) (hD : 0 < D)
    (w : List (SharpAlphabet Q D)) (x : Q → ℝ) (hx : ∀ i, 0 ≤ x i) (i : Q) :
    0 ≤ linearWord (sharpLetter e) w x i := by
  induction w generalizing i with
  | nil => exact hx i
  | cons a w ih =>
      rw [linearWord_cons, Module.End.mul_apply]
      exact sharpLetter_nonneg e hD a _ (fun j => ih j) i

def sharpLaw (e : Fin D ≃ Set.powersetCard Q 2) (hD : 0 < D) :
    StationaryWordLaw (SharpAlphabet Q D) where
  mass := representedWord (sharpLetter e) averageRow (fun _ => 1)
  nonneg w := by
    unfold representedWord
    rw [averageRow_apply]
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg fun i _ => sharpWord_nonneg e hD w _ (fun _ => by norm_num) i
  mass_nil := by simp [representedWord, averageRow_ones]
  sum_append w := by
    simp only [representedWord, linearWord_append, Module.End.mul_apply]
    have hone (a : SharpAlphabet Q D) : linearWord (sharpLetter e) [a] = sharpLetter e a :=
      by simp [linearWord]
    simp only [hone]
    rw [← map_sum, ← map_sum, ← LinearMap.sum_apply, sum_sharpLetter, uniformMean_ones]
  sum_prepend w := by
    simp only [representedWord, linearWord_cons, Module.End.mul_apply]
    rw [← map_sum, ← LinearMap.sum_apply, sum_sharpLetter, averageRow_uniformMean]

theorem sharp_reduced (e : Fin D ≃ Set.powersetCard Q 2) (hD : 0 < D) :
    WordReduced (sharpLetter e) averageRow (fun _ => 1) := by
  classical
  let q₀ : Q := Classical.arbitrary Q
  constructor
  · apply top_unique
    rw [← (Pi.basisFun ℝ Q).span_eq]
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    have hmem := linearWord_mem_linearReachableSpan (sharpLetter e) (fun _ => 1)
      [Sum.inr (i, q₀)]
    have he : linearWord (sharpLetter e) [Sum.inr (i, q₀)] (fun _ => 1) =
        endEntry (completionResidual e) i q₀ • Pi.single i 1 := by
      simp [linearWord, sharpLetter, entryMap]
    rw [he] at hmem
    have hp := completionResidual_entry_pos e hD i q₀
    have hm := (linearReachableSpan (sharpLetter e) (fun _ => 1)).smul_mem
      (endEntry (completionResidual e) i q₀)⁻¹ hmem
    simpa [Pi.basisFun_apply, smul_smul, hp.ne'] using hm
  · intro x hx
    funext j
    have h := hx [Sum.inr (q₀, j)]
    have hp := completionResidual_entry_pos e hD q₀ j
    have hn : (Fintype.card Q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp only [linearWord, List.map_singleton, List.prod_singleton, sharpLetter,
      LinearMap.smul_apply, map_smul, smul_eq_mul, averageRow_apply, entryMap] at h
    simp only [LinearMap.smulRight_apply, LinearMap.proj_apply, Pi.smul_apply,
      smul_eq_mul, Finset.mul_sum] at h
    simp [Pi.single_apply, Finset.sum_ite_eq, mul_ite, hn, hp.ne'] at h
    exact h

theorem rankOne_word_of_rankOne_letter {A : Type*} {V : Type*}
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (T : A → Module.End ℝ V) (w : List A) (a : A) (ha : a ∈ w)
    (hr : Module.finrank ℝ (T a).range ≤ 1) :
    Module.finrank ℝ (linearWord T w).range ≤ 1 := by
  apply (exteriorSquare_zero_iff_rank_le_one _).mp
  rw [← linearWord_exteriorPower]
  have hz := (exteriorSquare_zero_iff_rank_le_one _).mpr hr
  induction w with
  | nil => simp at ha
  | cons b w ih =>
      rw [linearWord_cons]
      rcases List.mem_cons.mp ha with h | h
      · subst b; rw [hz, zero_mul]
      · rw [ih h, mul_zero]

theorem sharpLetter_filler_rankOne (e : Fin D ≃ Set.powersetCard Q 2) (hD : 0 < D)
    (ij : Q × Q) :
    Module.finrank ℝ (sharpLetter e (.inr ij)).range ≤ 1 := by
  have h := (completionResidual_entry_pos e hD ij.1 ij.2).ne'
  have hmem : Pi.single ij.1 1 ∈ (sharpLetter e (.inr ij)).range := by
    refine ⟨(endEntry (completionResidual e) ij.1 ij.2)⁻¹ • Pi.single ij.2 1, ?_⟩
    simp [sharpLetter, entryMap, h, smul_smul]
  apply finrank_le_one (⟨Pi.single ij.1 1, hmem⟩ : (sharpLetter e (.inr ij)).range)
  intro y
  obtain ⟨x, hx⟩ := y.property
  refine ⟨endEntry (completionResidual e) ij.1 ij.2 * x ij.2, ?_⟩
  apply Subtype.ext
  change (endEntry (completionResidual e) ij.1 ij.2 * x ij.2) • Pi.single ij.1 1 = y.val
  rw [← hx]
  simp [sharpLetter, entryMap, smul_smul]

theorem sharpLetter_pure_word (e : Fin D ≃ Set.powersetCard Q 2)
    (v : List (Fin (D - 1))) :
    linearWord (sharpLetter e) (v.map Sum.inl) =
      linearWord (fun s => completionEpsilon (Q := Q) D •
        pairChain (Pi.basisFun ℝ Q) e s) v := by
  simp only [linearWord, List.map_map, Function.comp_def, sharpLetter]

theorem sharp_rankOne_at_cutoff (e : Fin D ≃ Set.powersetCard Q 2) (hD : 0 < D)
    (w : List (SharpAlphabet Q D)) (hw : w.length = D) :
    Module.finrank ℝ (linearWord (sharpLetter e) w).range ≤ 1 := by
  classical
  by_cases hf : ∃ ij : Q × Q, Sum.inr ij ∈ w
  · obtain ⟨ij, hij⟩ := hf
    exact rankOne_word_of_rankOne_letter _ _ _ hij (sharpLetter_filler_rankOne e hD ij)
  · have hpure : ∃ v : List (Fin (D - 1)), w = v.map Sum.inl := by
      clear hw
      induction w with
      | nil => exact ⟨[], rfl⟩
      | cons a w ih =>
          cases a with
          | inr ij => exact False.elim (hf ⟨ij, by simp⟩)
          | inl s =>
              obtain ⟨v, hv⟩ := ih (fun h => hf (by rcases h with ⟨ij, hij⟩; exact ⟨ij, by simp [hij]⟩))
              exact ⟨s :: v, by simp [hv]⟩
    obtain ⟨v, rfl⟩ := hpure
    rw [sharpLetter_pure_word, linearWord_uniform_smul_range _ _
      (completionEpsilon_pos (Q := Q) hD).ne']
    exact pairChain_rankOne_at_cutoff _ e v (by simpa using hw)

def sharpCriticalWord : List (SharpAlphabet Q D) :=
  (basisChainWord (D - 1) le_rfl).map Sum.inl

@[simp] theorem sharpCriticalWord_length :
    (sharpCriticalWord (Q := Q) (D := D)).length = D - 1 := by
  simp [sharpCriticalWord]

theorem sharp_critical_rank (e : Fin D ≃ Set.powersetCard Q 2) (hD : 0 < D) :
    ¬Module.finrank ℝ (linearWord (sharpLetter e) sharpCriticalWord).range ≤ 1 := by
  rw [sharpCriticalWord, sharpLetter_pure_word, linearWord_uniform_smul_range _ _
    (completionEpsilon_pos (Q := Q) hD).ne']
  exact pairChain_critical_rank _ e hD

theorem rankOne_of_prefix {A V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (T : A → Module.End ℝ V) (u v : List A)
    (hu : Module.finrank ℝ (linearWord T u).range ≤ 1) :
    Module.finrank ℝ (linearWord T (u ++ v)).range ≤ 1 := by
  apply (exteriorSquare_zero_iff_rank_le_one _).mp
  have hz := (exteriorSquare_zero_iff_rank_le_one _).mpr hu
  rw [← linearWord_exteriorPower, linearWord_append, linearWord_exteriorPower,
    hz, zero_mul]

theorem sharpLaw_exact_order (e : Fin D ≃ Set.powersetCard Q 2) (hD : 0 < D) :
    (sharpLaw e hD).ConditionalMarkov D ∧
      ∀ k < D, ¬(sharpLaw e hD).ConditionalMarkov k := by
  have hcrit := sharp_critical_rank e hD
  have hiff := fun k => (sharpLaw e hD).conditionalMarkov_iff_rankOne
    (sharpLetter e) averageRow (fun _ => 1) rfl (sharp_reduced e hD) k
  constructor
  · exact (hiff D).mpr (sharp_rankOne_at_cutoff e hD)
  · intro k hk hmarkov
    apply hcrit
    have hr := (hiff k).mp hmarkov
    have hlen : k ≤ (sharpCriticalWord (Q := Q) (D := D)).length := by
      rw [sharpCriticalWord_length]; omega
    let w := sharpCriticalWord (Q := Q) (D := D)
    have hp := hr (w.take k) (List.length_take_of_le hlen)
    have he := rankOne_of_prefix (sharpLetter e) (w.take k) (w.drop k) hp
    rw [List.take_append_drop] at he
    exact he

theorem sharpLaw_hankel_dimension (e : Fin D ≃ Set.powersetCard Q 2) (hD : 0 < D) :
    Module.finrank ℝ (wordHankelSpan (sharpLaw e hD).mass) = Fintype.card Q := by
  change Module.finrank ℝ (wordHankelSpan
    (representedWord (sharpLetter e) averageRow (fun _ => 1))) = _
  rw [(sharp_reduced e hD).finrank_wordHankelSpan]
  exact Module.finrank_eq_card_basis (Pi.basisFun ℝ Q)

end SoficMarkovOrder
