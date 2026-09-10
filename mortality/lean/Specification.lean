import Publication

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open FiniteMonoidMortality

namespace ManuscriptSpecification

-- Exact source statement under the documented identifier renaming.
theorem exists_minimum_rank_word_real_of_finite : ∀ {A : Type*} {n : ℕ} (M : A → Matrix (Fin n) (Fin n) ℝ)
    (hfinite : (Set.range (matrixWord M)).Finite),
  ∃ w : List A,
      (∀ v : List A, (matrixWord M w).rank ≤ (matrixWord M v).rank) ∧
      w.length ≤ minimumRankBound n (matrixWord M w).rank :=
  @FiniteMonoidMortality.exists_minimum_rank_word_real_of_finite

-- Exact source statement under the documented identifier renaming.
theorem exists_minimum_rank_word_rational_of_finite : ∀ {A : Type*} {n : ℕ} (M : A → Matrix (Fin n) (Fin n) ℚ)
    (hfinite : (Set.range (matrixWord M)).Finite),
  ∃ w : List A,
      (∀ v : List A, (matrixWord M w).rank ≤ (matrixWord M v).rank) ∧
      w.length ≤ minimumRankBound n (matrixWord M w).rank :=
  @FiniteMonoidMortality.exists_minimum_rank_word_rational_of_finite

-- Exact source statement under the documented identifier renaming.
theorem exists_improved_short_zero_word_of_finite_real_monoid : ∀ {A : Type*} {n : ℕ} (M : A → Matrix (Fin n) (Fin n) ℝ)
    (hfinite : (Set.range (matrixWord M)).Finite)
    (hzero : ∃ z : List A, matrixWord M z = 0),
  ∃ z : List A, matrixWord M z = 0 ∧ z.length ≤ improvedMortalityBound n :=
  @FiniteMonoidMortality.exists_improved_short_zero_word_of_finite_real_monoid

-- Exact source statement under the documented identifier renaming.
theorem exists_improved_short_zero_word_of_finite_rational_monoid : ∀ {A : Type*} {n : ℕ} (M : A → Matrix (Fin n) (Fin n) ℚ)
    (hfinite : (Set.range (matrixWord M)).Finite)
    (hzero : ∃ z : List A, matrixWord M z = 0),
  ∃ z : List A, matrixWord M z = 0 ∧ z.length ≤ improvedMortalityBound n :=
  @FiniteMonoidMortality.exists_improved_short_zero_word_of_finite_rational_monoid

-- Exact source statement under the documented identifier renaming.
theorem exists_zero_word_length_le_four_real : ∀ {Alphabet : Type*} (M : Alphabet → Matrix (Fin 2) (Fin 2) ℝ)
    (hf : (Set.range (matrixWord M)).Finite)
    (hzero : ∃ w : List Alphabet, matrixWord M w=0),
  ∃ w : List Alphabet, matrixWord M w=0 ∧ w.length ≤ 4 :=
  @FiniteMonoidMortality.exists_zero_word_length_le_four_real

-- Exact source statement under the documented identifier renaming.
theorem exists_zero_word_length_le_four_rational : ∀ {Alphabet : Type*} (M : Alphabet → Matrix (Fin 2) (Fin 2) ℚ)
    (hf : (Set.range (matrixWord M)).Finite)
    (hzero : ∃ w : List Alphabet, matrixWord M w=0),
  ∃ w : List Alphabet, matrixWord M w=0 ∧ w.length ≤ 4 :=
  @FiniteMonoidMortality.exists_zero_word_length_le_four_rational

-- Exact source statement under the documented identifier renaming.
theorem mortalityExample_threshold_four : (Set.range (matrixWord mortalityExample)).Finite ∧
    (∃ w : List Bool, matrixWord mortalityExample w = 0 ∧ w.length = 4) ∧
    (∀ w : List Bool, matrixWord mortalityExample w = 0 → 4 ≤ w.length) :=
  @FiniteMonoidMortality.mortalityExample_threshold_four

-- Exact source statement under the documented identifier renaming.
theorem exists_zero_word_of_invariant_flag : ∀ {E A : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E] (T : A → Module.End ℝ E) (V : ℕ → Submodule ℝ E)
    (n : ℕ) (hbot : V 0=⊥) (htop : V n=⊤)
    (hV : ∀ a i, i ≤ n → ∀ x ∈ V i, T a x ∈ V i)
    (hf : (Set.range (endWord T)).Finite) (hz : ∃w, endWord T w=0),
  ∃ w : List A, endWord T w=0 ∧
      w.length ≤ ((List.range n).map (fun i =>
        factorMortalityBound (Module.finrank ℝ (flagSection (V (i+1)) (V i))))).sum :=
  @FiniteMonoidMortality.exists_zero_word_of_invariant_flag

-- Exact source statement under the documented identifier renaming.
theorem exists_zero_word_prescribed_small_factors : ∀ {E A : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E] (T : A → Module.End ℝ E) (V : ℕ → Submodule ℝ E)
    (n k1 k2 : ℕ) (hbot : V 0=⊥) (htop : V n=⊤)
    (hsmall : ∀ i<n, Module.finrank ℝ (flagSection (V (i+1)) (V i))=1 ∨
      Module.finrank ℝ (flagSection (V (i+1)) (V i))=2)
    (hk1 : ((List.range n).map (fun i => Module.finrank ℝ (flagSection (V (i+1)) (V i)))).count 1=k1)
    (hk2 : ((List.range n).map (fun i => Module.finrank ℝ (flagSection (V (i+1)) (V i)))).count 2=k2)
    (hV : ∀ a i, i ≤ n → ∀ x ∈ V i, T a x ∈ V i)
    (hf : (Set.range (endWord T)).Finite) (hz : ∃w, endWord T w=0),
  ∃ w : List A, endWord T w=0 ∧ w.length ≤ k1+4*k2 :=
  @FiniteMonoidMortality.exists_zero_word_prescribed_small_factors

-- Exact source statement under the documented identifier renaming.
theorem exists_zero_word_linear_bound_of_small_factors : ∀ {E A : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E] (T : A → Module.End ℝ E) (V : ℕ → Submodule ℝ E)
    (n : ℕ) (hbot : V 0=⊥) (htop : V n=⊤)
    (hmono : ∀ i<n, V i ≤ V (i+1))
    (hsmall : ∀ i<n, Module.finrank ℝ (flagSection (V (i+1)) (V i))=1 ∨
      Module.finrank ℝ (flagSection (V (i+1)) (V i))=2)
    (hV : ∀ a i, i ≤ n → ∀ x ∈ V i, T a x ∈ V i)
    (hf : (Set.range (endWord T)).Finite) (hz : ∃w, endWord T w=0),
  ∃ w : List A, endWord T w=0 ∧ w.length ≤ 2*Module.finrank ℝ E :=
  @FiniteMonoidMortality.exists_zero_word_linear_bound_of_small_factors

-- Exact source statement under the documented identifier renaming.
theorem sharp_small_block_threshold : ∀ (k1 k2 : ℕ),
  Fintype.card (Σ i : smallBlockIndex k1 k2, Fin (smallBlockDim i))=k1+2*k2 ∧
    (Set.range (matrixWord (blockMortalityDigit smallBlockDim
      (@smallBlockDigit k1 k2)))).Finite ∧
    (∃ w, matrixWord (blockMortalityDigit smallBlockDim (@smallBlockDigit k1 k2)) w=0 ∧
      w.length=k1+4*k2) ∧
    (∀ w, matrixWord (blockMortalityDigit smallBlockDim (@smallBlockDigit k1 k2)) w=0 →
      k1+4*k2 ≤ w.length) :=
  @FiniteMonoidMortality.sharp_small_block_threshold

-- Exact source statement under the documented identifier renaming.
theorem mortalityRotation_irreducible : ∀ (U : Submodule ℝ (Fin 2 → ℝ))
    (hU : ∀ x ∈ U, (mortalityRotation.map (Int.castRingHom ℝ)).mulVec x ∈ U),
  U=⊥ ∨ U=⊤ :=
  @FiniteMonoidMortality.mortalityRotation_irreducible

-- Exact source statement under the documented identifier renaming.
theorem bounded_periodic_mortality_no_uniform_bound : ∀ (N : ℕ),
  Module.finrank ℝ ℂ=2 ∧
    ∃ T : Bool → (ℂ →L[ℝ] ℂ),
      Bornology.IsBounded (Set.range (continuousWord T)) ∧
      (∀ a, (Set.range (fun k : ℕ => (T a)^k)).Finite) ∧
      (∃ w, continuousWord T w=0) ∧
      (∀ w, w.length ≤ N → continuousWord T w ≠ 0) :=
  @FiniteMonoidMortality.bounded_periodic_mortality_no_uniform_bound

-- Exact source statement under the documented identifier renaming.
theorem exists_minimum_rank_slp_real_of_finite : ∀ {A : Type*} {n : ℕ} (M : A → Matrix (Fin n) (Fin n) ℝ)
    (hf : (Set.range (matrixWord M)).Finite),
  ∃ p : List (WordGate A), wordProgramValid p ∧ 0<p.length ∧
      (∀ v, (matrixWord M (wordProgramRoot p)).rank ≤ (matrixWord M v).rank) ∧
      (wordProgramRoot p).length ≤ minimumRankBound n (matrixWord M (wordProgramRoot p)).rank ∧
      p.length ≤ mortalitySLPGateBound n :=
  @FiniteMonoidMortality.exists_minimum_rank_slp_real_of_finite

-- Exact source statement under the documented identifier renaming.
theorem exists_minimum_rank_slp_rational_of_finite : ∀ {A : Type*} {n : ℕ} (M : A → Matrix (Fin n) (Fin n) ℚ)
    (hf : (Set.range (matrixWord M)).Finite),
  ∃ p : List (WordGate A), wordProgramValid p ∧ 0<p.length ∧
      (∀ v, (matrixWord M (wordProgramRoot p)).rank ≤ (matrixWord M v).rank) ∧
      (wordProgramRoot p).length ≤ minimumRankBound n (matrixWord M (wordProgramRoot p)).rank ∧
      p.length ≤ mortalitySLPGateBound n :=
  @FiniteMonoidMortality.exists_minimum_rank_slp_rational_of_finite

-- Exact source statement under the documented identifier renaming.
theorem wordProgramValue_correct : ∀ {A R : Type*} [Monoid R]
    (M : A → R) (p : List (WordGate A)),
  wordProgramValue M p=((wordProgramRoot p).map M).prod :=
  @FiniteMonoidMortality.wordProgramValue_correct

-- Exact source statement under the documented identifier renaming.
theorem mortalitySLPGateBound_le_cubic : ∀ (n : ℕ),
  mortalitySLPGateBound n ≤ n^3+n^2+3*n+1 :=
  @FiniteMonoidMortality.mortalitySLPGateBound_le_cubic

-- Exact source statement under the documented identifier renaming.
theorem minimumRankBound_full : ∀ (n : ℕ),
  minimumRankBound n n = 0 :=
  @FiniteMonoidMortality.minimumRankBound_full

-- Exact source statement under the documented identifier renaming.
theorem minimumRankBound_zero : ∀ (n : ℕ),
  minimumRankBound n 0 = n * 2 ^ n - n * (n + 1) / 2 :=
  @FiniteMonoidMortality.minimumRankBound_zero

-- Exact source statement under the documented identifier renaming.
theorem mortalityBudget_comparison : ∀ (n : ℕ) (hn : 2 ≤ n),
  2 ^ (n - 1) + (2 ^ (n - 1) - 1) * (n * (n + 1) / 2) =
      mortalityBudget n n + 2 ^ (n - 2) * (n - 1) * (n - 2) :=
  @FiniteMonoidMortality.mortalityBudget_comparison

end ManuscriptSpecification

#print axioms ManuscriptSpecification.exists_minimum_rank_word_real_of_finite
#print axioms ManuscriptSpecification.exists_minimum_rank_word_rational_of_finite
#print axioms ManuscriptSpecification.exists_improved_short_zero_word_of_finite_real_monoid
#print axioms ManuscriptSpecification.exists_improved_short_zero_word_of_finite_rational_monoid
#print axioms ManuscriptSpecification.exists_zero_word_length_le_four_real
#print axioms ManuscriptSpecification.exists_zero_word_length_le_four_rational
#print axioms ManuscriptSpecification.mortalityExample_threshold_four
#print axioms ManuscriptSpecification.exists_zero_word_of_invariant_flag
#print axioms ManuscriptSpecification.exists_zero_word_prescribed_small_factors
#print axioms ManuscriptSpecification.exists_zero_word_linear_bound_of_small_factors
#print axioms ManuscriptSpecification.sharp_small_block_threshold
#print axioms ManuscriptSpecification.mortalityRotation_irreducible
#print axioms ManuscriptSpecification.bounded_periodic_mortality_no_uniform_bound
#print axioms ManuscriptSpecification.exists_minimum_rank_slp_real_of_finite
#print axioms ManuscriptSpecification.exists_minimum_rank_slp_rational_of_finite
#print axioms ManuscriptSpecification.wordProgramValue_correct
#print axioms ManuscriptSpecification.mortalitySLPGateBound_le_cubic
#print axioms ManuscriptSpecification.minimumRankBound_full
#print axioms ManuscriptSpecification.minimumRankBound_zero
#print axioms ManuscriptSpecification.mortalityBudget_comparison
