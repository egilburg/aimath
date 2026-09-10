import FiniteMonoidMortality.ImprovedMortalityBound
import FiniteMonoidMortality.MatrixWordScalarExtension
import FiniteMonoidMortality.MinimalRankCompression
import FiniteMonoidMortality.PlaneEllipse
import FiniteMonoidMortality.PlaneInvariantForm
import FiniteMonoidMortality.RankOneSandwich
import FiniteMonoidMortality.RankOneTrace

set_option autoImplicit false

noncomputable section

open Matrix

namespace FiniteMonoidMortality

theorem shorten_three_unit_middle
    (S : Set (Matrix (Fin 2) (Fin 2) ℝ)) (hf : S.Finite) (h1 : 1 ∈ S)
    (hm : ∀ ⦃X Y⦄, X ∈ S → Y ∈ S → X*Y ∈ S)
    (A B C D E : Matrix (Fin 2) (Fin 2) ℝ)
    (hB : B ∈ S) (hC : C ∈ S) (hD : D ∈ S) (hE : E ∈ S)
    (uB : IsUnit B) (uC : IsUnit C) (uD : IsUnit D)
    (e0 : E ≠ 0) (ue : ¬ IsUnit E) (hz : A*B*C*D*E=0) :
    A*B*C*E=0 ∨ A*B*E=0 ∨ A*E=0 ∨ A*B*D*E=0 ∨ A*D*E=0 ∨ A*C*D*E=0 := by
  obtain ⟨u,v,hu,hv,he⟩ := exists_outer_of_two_nonunit E e0 ue
  obtain ⟨Q,hQ,hQi⟩ := exists_invariant_vector_form S hf hm
  have hdet : E.det=0 := by simpa [Matrix.isUnit_iff_isUnit_det] using ue
  have hpow : ∀ X ∈ S, ∀ j : ℕ, X^j ∈ S := by
    intro X hX j
    induction j with
    | zero => simpa using h1
    | succ j ih => simpa [pow_succ] using hm ih hX
  have hpfinite (X : Matrix (Fin 2) (Fin 2) ℝ) (hX : X ∈ S) :
      (Set.range (fun j : ℕ => X^j)).Finite := hf.subset (by rintro _ ⟨j,rfl⟩; exact hpow X hX j)
  have nz (g : Matrix (Fin 2) (Fin 2) ℝ) (ug : IsUnit g) : g *ᵥ u ≠ 0 := by
    intro hh
    apply hu
    apply Matrix.mulVec_injective_iff_isUnit.mpr ug
    simpa using hh
  have htr (g : Matrix (Fin 2) (Fin 2) ℝ) (hg : g ∈ S) (ug : IsUnit g) :
      planeLine (v 0) (v 1) (g *ᵥ u)=0 ∨ planeLine (v 0) (v 1) (g *ᵥ u)=1 ∨
        planeLine (v 0) (v 1) (g *ᵥ u)= -1 := by
    have hn : g*E ≠ 0 := by
      intro hh
      rw [he,Matrix.mul_vecMulVec,Matrix.vecMulVec_eq_zero] at hh
      exact hh.elim (nz g ug) hv
    have ht := matrix_two_trace_quantized (g*E) hn (by rw [Matrix.det_mul,hdet,mul_zero]) (hpfinite _ (hm hg hE))
    have htq : (g*E).trace=planeLine (v 0) (v 1) (g *ᵥ u) := by
      rw [he,Matrix.mul_vecMulVec]
      simp [Matrix.trace,Matrix.vecMulVec,planeLine,Fin.sum_univ_two]
      ring
    simpa only [htq] using ht
  have hv' : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    ext i; fin_cases i <;> simp_all
  have hq (g : Matrix (Fin 2) (Fin 2) ℝ) (hg : g ∈ S) (ug : IsUnit g) := planeQuad_invariant Q g (hQi g hg ug) u
  have hx := planeQuad_quantized_four (Q 0 0) (Q 0 1+Q 1 0) (Q 1 1) (v 0) (v 1)
    (planeQuad (Q 0 0) (Q 0 1+Q 1 0) (Q 1 1) u) hv' (planeQuad_pos_of_posDef Q hQ)
    u (D *ᵥ u) ((C*D) *ᵥ u) ((B*C*D) *ᵥ u)
    (by simpa using htr 1 h1 isUnit_one) (htr D hD uD)
    (htr (C*D) (hm hC hD) (uC.mul uD))
    (htr (B*C*D) (hm (hm hB hC) hD) ((uB.mul uC).mul uD))
    rfl (hq D hD uD) (hq (C*D) (hm hC hD) (uC.mul uD))
    (hq (B*C*D) (hm (hm hB hC) hD) ((uB.mul uC).mul uD))
  have hzv : (A*B*C*D) *ᵥ u=0 := by
    rw [he,Matrix.mul_vecMulVec,Matrix.vecMulVec_eq_zero] at hz
    exact hz.resolve_right hv
  have liftzero (g : Matrix (Fin 2) (Fin 2) ℝ) (hg : g *ᵥ u=0) : g*E=0 := by
    rw [he,Matrix.mul_vecMulVec,hg]; simp
  have detsym (x y : Fin 2 → ℝ) (h : planeDet x y=0) : planeDet y x=0 := by dsimp [planeDet] at *; linarith
  rcases hx with h | h | h | h | h | h
  · left; apply liftzero
    exact mulVec_zero_of_planeDet_zero (A*B*C) (D *ᵥ u) u (nz D uD) (detsym _ _ h) (by simpa only [Matrix.mulVec_mulVec,Matrix.mul_assoc] using hzv)
  · right; left; apply liftzero
    exact mulVec_zero_of_planeDet_zero (A*B) ((C*D) *ᵥ u) u (nz (C*D) (uC.mul uD)) (detsym _ _ h) (by simpa only [Matrix.mulVec_mulVec,Matrix.mul_assoc] using hzv)
  · right; right; left; apply liftzero
    exact mulVec_zero_of_planeDet_zero A ((B*C*D) *ᵥ u) u (nz (B*C*D) ((uB.mul uC).mul uD)) (detsym _ _ h) (by simpa only [Matrix.mulVec_mulVec,Matrix.mul_assoc] using hzv)
  · right; right; right; left; apply liftzero
    have hh := mulVec_zero_of_planeDet_zero (A*B) ((C*D) *ᵥ u) (D *ᵥ u) (nz (C*D) (uC.mul uD)) (detsym _ _ h) (by simpa only [Matrix.mulVec_mulVec,Matrix.mul_assoc] using hzv)
    simpa only [Matrix.mulVec_mulVec] using hh
  · right; right; right; right; left; apply liftzero
    have hh := mulVec_zero_of_planeDet_zero A ((B*C*D) *ᵥ u) (D *ᵥ u) (nz (B*C*D) ((uB.mul uC).mul uD)) (detsym _ _ h) (by simpa only [Matrix.mulVec_mulVec,Matrix.mul_assoc] using hzv)
    simpa only [Matrix.mulVec_mulVec] using hh
  · right; right; right; right; right; apply liftzero
    have hh := mulVec_zero_of_planeDet_zero A ((B*C*D) *ᵥ u) ((C*D) *ᵥ u) (nz (B*C*D) ((uB.mul uC).mul uD)) (detsym _ _ h) (by simpa only [Matrix.mulVec_mulVec,Matrix.mul_assoc] using hzv)
    simpa only [Matrix.mulVec_mulVec,Matrix.mul_assoc] using hh

theorem exists_zero_word_length_le_four_real
    {Alphabet : Type*} (M : Alphabet → Matrix (Fin 2) (Fin 2) ℝ)
    (hf : (Set.range (matrixWord M)).Finite)
    (hzero : ∃ w : List Alphabet, matrixWord M w=0) :
    ∃ w : List Alphabet, matrixWord M w=0 ∧ w.length ≤ 4 := by
  obtain ⟨w,hw,hl⟩ := exists_improved_short_zero_word_of_finite_real_monoid M hf hzero
  norm_num [improvedMortalityBound] at hl
  by_contra h
  have hs : ∀ v : List Alphabet, v.length ≤ 4 → matrixWord M v ≠ 0 := by
    intro v hv hz
    exact h ⟨v,hz,hv⟩
  have hlen : w.length=5 := by
    have hn : ¬ w.length ≤ 4 := fun hle => hs w hle hw
    omega
  obtain ⟨a,w,rfl⟩ := List.exists_of_length_succ w hlen
  simp only [List.length_cons] at hlen
  obtain ⟨b,w,rfl⟩ := List.exists_of_length_succ w (show w.length=4 by omega)
  simp only [List.length_cons] at hlen
  obtain ⟨c,w,rfl⟩ := List.exists_of_length_succ w (show w.length=3 by omega)
  simp only [List.length_cons] at hlen
  obtain ⟨d,w,rfl⟩ := List.exists_of_length_succ w (show w.length=2 by omega)
  simp only [List.length_cons] at hlen
  obtain ⟨e,w,rfl⟩ := List.exists_of_length_succ w (show w.length=1 by omega)
  simp only [List.length_cons] at hlen
  have hw0 : w=[] := by simpa using (show w.length=0 by omega)
  subst w
  have hz : M a*M b*M c*M d*M e=0 := by simpa [matrixWord,Matrix.mul_assoc] using hw
  have neletter (x : Alphabet) : M x ≠ 0 := by simpa [matrixWord] using hs [x] (by simp)
  have ub : IsUnit (M b) := by
    by_contra hb
    have hh := two_nonunit_sandwich_zero (M a) (M b) (M c*M d*M e)
      (neletter b) hb (by simpa only [Matrix.mul_assoc] using hz)
    rcases hh with hh | hh
    · exact hs [a,b] (by simp) (by simpa [matrixWord] using hh)
    · exact hs [b,c,d,e] (by simp) (by simpa [matrixWord,Matrix.mul_assoc] using hh)
  have uc : IsUnit (M c) := by
    by_contra hc
    have hh := two_nonunit_sandwich_zero (M a*M b) (M c) (M d*M e)
      (neletter c) hc (by simpa only [Matrix.mul_assoc] using hz)
    rcases hh with hh | hh
    · exact hs [a,b,c] (by simp) (by simpa [matrixWord,Matrix.mul_assoc] using hh)
    · exact hs [c,d,e] (by simp) (by simpa [matrixWord,Matrix.mul_assoc] using hh)
  have ud : IsUnit (M d) := by
    by_contra hd
    have hh := two_nonunit_sandwich_zero (M a*M b*M c) (M d) (M e)
      (neletter d) hd hz
    rcases hh with hh | hh
    · exact hs [a,b,c,d] (by simp) (by simpa [matrixWord,Matrix.mul_assoc] using hh)
    · exact hs [d,e] (by simp) (by simpa [matrixWord] using hh)
  have ue : ¬ IsUnit (M e) := by
    intro he
    have hh : M a*M b*M c*M d=0 := he.mul_left_injective (by simpa using hz)
    exact hs [a,b,c,d] (by simp) (by simpa [matrixWord,Matrix.mul_assoc] using hh)
  have hm : ∀ ⦃X Y⦄, X ∈ Set.range (matrixWord M) → Y ∈ Set.range (matrixWord M) →
      X*Y ∈ Set.range (matrixWord M) := by
    rintro X Y ⟨x,rfl⟩ ⟨y,rfl⟩
    exact ⟨x++y,matrixWord_append M x y⟩
  have mem (x : Alphabet) : M x ∈ Set.range (matrixWord M) := ⟨[x],by simp [matrixWord]⟩
  have hh := shorten_three_unit_middle (Set.range (matrixWord M)) hf ⟨[],by simp⟩ hm
    (M a) (M b) (M c) (M d) (M e) (mem b) (mem c) (mem d) (mem e)
    ub uc ud (neletter e) ue hz
  rcases hh with hh | hh | hh | hh | hh | hh
  · exact hs [a,b,c,e] (by simp) (by simpa [matrixWord,Matrix.mul_assoc] using hh)
  · exact hs [a,b,e] (by simp) (by simpa [matrixWord,Matrix.mul_assoc] using hh)
  · exact hs [a,e] (by simp) (by simpa [matrixWord,Matrix.mul_assoc] using hh)
  · exact hs [a,b,d,e] (by simp) (by simpa [matrixWord,Matrix.mul_assoc] using hh)
  · exact hs [a,d,e] (by simp) (by simpa [matrixWord,Matrix.mul_assoc] using hh)
  · exact hs [a,c,d,e] (by simp) (by simpa [matrixWord,Matrix.mul_assoc] using hh)

theorem exists_zero_word_length_le_four_rational
    {Alphabet : Type*} (M : Alphabet → Matrix (Fin 2) (Fin 2) ℚ)
    (hf : (Set.range (matrixWord M)).Finite)
    (hzero : ∃ w : List Alphabet, matrixWord M w=0) :
    ∃ w : List Alphabet, matrixWord M w=0 ∧ w.length ≤ 4 := by
  let f : ℚ →+* ℝ := Rat.castHom ℝ
  let MR := fun a => (M a).map f
  obtain ⟨z,hz⟩ := hzero
  obtain ⟨w,hw,hl⟩ := exists_zero_word_length_le_four_real MR
    (finite_matrixWord_range_map f M hf) ⟨z,(matrixWord_map_eq_zero_iff f M z).mpr hz⟩
  exact ⟨w,(matrixWord_map_eq_zero_iff f M w).mp hw,hl⟩

end FiniteMonoidMortality
