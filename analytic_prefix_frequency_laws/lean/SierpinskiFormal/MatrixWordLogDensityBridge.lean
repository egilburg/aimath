import SierpinskiFormal.RadixLogDensityTransfer
import SierpinskiFormal.IidCompactWordAverages
import SierpinskiFormal.LinearDigitRepresentation

set_option autoImplicit false

/-!
# From IID word averages to logarithmic density for digit recurrences

The analytic assumption in this file is explicit: the IID word-length
Cesàro average must converge for every seed state.  The arithmetic conclusion
then follows from an exact padded-word enumeration of every radix block.
-/

noncomputable section

namespace IndependentZeroBlocks

open Filter
open scoped Topology BigOperators

section WordEnumeration

variable {A : Type*}

/-- Exact-length tuples split into their first letter and remaining tuple. -/
noncomputable def finSuccTupleEquiv (n : ℕ) :
    (Fin (n + 1) → A) ≃ A × (Fin n → A) where
  toFun x := (x 0, fun i => x i.succ)
  invFun ax := Fin.cons ax.1 ax.2
  left_inv x := by
    funext i
    exact Fin.cases rfl (fun j => rfl) i
  right_inv ax := by
    apply Prod.ext
    · rfl
    · funext i
      rfl

@[simp] theorem finSuccTupleEquiv_fst (n : ℕ) (x : Fin (n + 1) → A) :
    (finSuccTupleEquiv n x).1 = x 0 := rfl

@[simp] theorem finSuccTupleEquiv_snd (n : ℕ) (x : Fin (n + 1) → A)
    (i : Fin n) :
    (finSuccTupleEquiv n x).2 i = x i.succ := rfl

variable [TopologicalSpace A] [Fintype A] [Nonempty A]

/-- The recursive IID expectation is the normalized sum over exact-length
word tuples. -/
theorem uniformWordExtensionAverage_eq_tuple_sum
    (q : BoundedWordFunction A) (n : ℕ) (z : List A) :
    uniformWordExtensionAverage q n z =
      ((Fintype.card A : ℝ) ^ n)⁻¹ *
        ∑ x : Fin n → A, q (z ++ List.ofFn x) := by
  induction n generalizing z with
  | zero => simp [uniformWordExtensionAverage]
  | succ n ih =>
      simp only [uniformWordExtensionAverage]
      simp_rw [ih]
      rw [Fintype.sum_equiv (finSuccTupleEquiv n)
        (fun x : Fin (n + 1) → A => q (z ++ List.ofFn x))
        (fun ax : A × (Fin n → A) => q (z ++ ax.1 :: List.ofFn ax.2))]
      · rw [Fintype.sum_prod_type]
        simp only [smul_eq_mul]
        rw [pow_succ, mul_inv]
        simp_rw [List.append_assoc, List.singleton_append]
        simp only [← Finset.mul_sum]
        ring
      · intro x
        simp [List.ofFn_succ, finSuccTupleEquiv]

/-- Uniform exact-word average as a normalized tuple sum. -/
theorem uniformIidWordAverage_eq_tuple_sum
    (q : BoundedWordFunction A) (n : ℕ) :
    uniformIidWordAverage q n =
      ((Fintype.card A : ℝ) ^ n)⁻¹ *
        ∑ x : Fin n → A, q (List.ofFn x) := by
  simpa [uniformIidWordAverage] using
    uniformWordExtensionAverage_eq_tuple_sum q n ([] : List A)

end WordEnumeration

section RadixWords

/-- Exact padded radix words, represented as tuples, enumerate precisely the
interval below the corresponding radix power. -/
noncomputable def radixTupleEquiv (b : ℕ) (hb : 2 ≤ b) (r : ℕ) :
    (Fin r → Fin b) ≃ Fin (b ^ r) :=
  Equiv.ofBijective
    (fun x => ⟨Nat.ofDigits b ((List.ofFn x).map Fin.val), by
      simpa using Nat.ofDigits_lt_base_pow_length (b := b)
        (l := (List.ofFn x).map Fin.val) (by omega) (by
          intro y hy
          simp only [List.mem_map] at hy
          obtain ⟨a, ha, rfl⟩ := hy
          exact a.isLt)
      ⟩)
    ⟨by
      intro x y hxy
      have hlist : List.ofFn x = List.ofFn y := by
        apply (List.map_injective_iff.mpr Fin.val_injective)
        apply Nat.ofDigits_inj_of_len_eq (b := b) (by omega)
        · simp
        · intro z hz
          simp only [List.mem_map] at hz
          obtain ⟨a, ha, rfl⟩ := hz
          exact a.isLt
        · intro z hz
          simp only [List.mem_map] at hz
          obtain ⟨a, ha, rfl⟩ := hz
          exact a.isLt
        · exact Fin.ext_iff.mp hxy
      exact List.ofFn_injective hlist,
    by
      intro t
      obtain ⟨w, hwlen, hwval⟩ := exists_fin_digit_word_of_lt_pow
        b hb r t.val t.isLt
      let x : Fin r → Fin b := fun i => w.get (Fin.cast hwlen.symm i)
      refine ⟨x, Fin.ext ?_⟩
      dsimp [x]
      rw [← hwval]
      congr 2
      apply List.ext_get (by simp [hwlen])
      intro i hi1 hi2
      simp [x]⟩

end RadixWords

section MatrixRecurrence

variable {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V]

local instance : DecidableEq K := Classical.decEq K

/-- Bounded support indicator of the word action observed from a fixed seed. -/
noncomputable def observedSeedWordSupport
    {b : ℕ} (T : Fin b → Module.End K V) (l : Module.Dual K V) (v : V) :
    BoundedWordFunction (Fin b) := by
  classical
  exact BoundedContinuousFunction.mkOfBound
    ⟨fun w => if l (linearWord T w v) ≠ 0 then (1 : ℝ) else 0,
      continuous_of_discreteTopology⟩ 1 (by
        intro x y
        by_cases hx : l (linearWord T x v) = 0 <;>
          by_cases hy : l (linearWord T y v) = 0 <;>
            simp [hx, hy, Real.dist_eq])

@[simp] theorem observedSeedWordSupport_apply
    {b : ℕ} (T : Fin b → Module.End K V) (l : Module.Dual K V) (v : V)
    (w : List (Fin b)) :
    observedSeedWordSupport T l v w =
      if l (linearWord T w v) ≠ 0 then (1 : ℝ) else 0 := by
  classical
  simp [observedSeedWordSupport]

/-- IID average with the nonemptiness of the digit alphabet supplied by an
explicit positive-radix proof. -/
noncomputable def observedSeedUniformIidWordAverage
    {b : ℕ} (hb : 0 < b) (T : Fin b → Module.End K V)
    (l : Module.Dual K V) (v : V) (r : ℕ) : ℝ :=
  @uniformIidWordAverage (Fin b) inferInstance inferInstance ⟨⟨0, hb⟩⟩
    (observedSeedWordSupport T l v) r

/-- Cesàro means of the preceding exact-word averages. -/
noncomputable def observedSeedUniformIidWordCesaro
    {b : ℕ} (hb : 0 < b) (T : Fin b → Module.End K V)
    (l : Module.Dual K V) (v : V) (N : ℕ) : ℝ :=
  @uniformIidWordCesaro (Fin b) inferInstance inferInstance ⟨⟨0, hb⟩⟩
    (observedSeedWordSupport T l v) N

/-- Explicit analytic input for a recurrence: IID word-length Cesàro
convergence is assumed for the support word function based at every seed. -/
def HasObservedSeedIidCesaroMeans
    {b : ℕ} (hb : 0 < b) (T : Fin b → Module.End K V)
    (l : Module.Dual K V) : Prop :=
  ∀ v : V, ∃ a : ℝ,
    Tendsto (observedSeedUniformIidWordCesaro hb T l v)
      atTop (𝓝 a)

/-- Exact fixed-context identity: a radix block proportion is the uniform
IID support average of padded words acting on the high state `u q`. -/
theorem radixContextProportion_eq_uniformIidWordAverage
    (b : ℕ) (hb : 2 ≤ b) (T : Fin b → Module.End K V) (u : ℕ → V)
    (hrec : ∀ n (a : Fin b), u (b * n + a.val) = T a (u n))
    (l : Module.Dual K V) (q r : ℕ) :
    radixContextProportion (fun n => l (u n) ≠ 0) b q r =
      observedSeedUniformIidWordAverage (by omega) T l (u q) r := by
  letI : Nonempty (Fin b) := ⟨⟨0, by omega⟩⟩
  unfold observedSeedUniformIidWordAverage
  rw [uniformIidWordAverage_eq_tuple_sum]
  rw [show Fintype.card (Fin b) = b by simp]
  have hsum :
      (∑ x : Fin r → Fin b, observedSeedWordSupport T l (u q) (List.ofFn x)) =
        ∑ t : Fin (b ^ r),
          predicateIndicator (fun n => l (u n) ≠ 0) (q * b ^ r + t.val) := by
    apply Fintype.sum_equiv (radixTupleEquiv b hb r)
    intro x
    classical
    rw [observedSeedWordSupport_apply]
    rw [linearWord_apply_digitRecurrence b T u hrec]
    unfold predicateIndicator
    have hindex :
        b ^ (List.ofFn x).length * q +
            Nat.ofDigits b ((List.ofFn x).map Fin.val) =
          q * b ^ r + ((radixTupleEquiv b hb r) x).val := by
      simp [radixTupleEquiv]
      ring
    rw [hindex]
    by_cases hsupport : l (u (q * b ^ r + ((radixTupleEquiv b hb r) x).val)) ≠ 0 <;>
      simp [hsupport]
  rw [hsum]
  have hfinSum :
      (∑ t : Fin (b ^ r),
          predicateIndicator (fun n => l (u n) ≠ 0) (q * b ^ r + t.val)) =
        ∑ t ∈ Finset.range (b ^ r),
          predicateIndicator (fun n => l (u n) ≠ 0) (q * b ^ r + t) := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro t ht
    simp [Finset.mem_range.mp ht]
  rw [hfinSum, ← intervalPredicateCount_cast_eq_sum_indicator]
  unfold radixContextProportion
  rw [Nat.cast_pow]
  rw [div_eq_mul_inv]
  ring

theorem observedSeedIidCesaro_hasAllFixedContextCesaroMeans
    (b : ℕ) (hb : 2 ≤ b) (T : Fin b → Module.End K V) (u : ℕ → V)
    (hrec : ∀ n (a : Fin b), u (b * n + a.val) = T a (u n))
    (l : Module.Dual K V)
    (hiid : HasObservedSeedIidCesaroMeans (by omega) T l) :
    HasAllFixedContextCesaroMeans (fun n => l (u n) ≠ 0) b := by
  intro q hq
  obtain ⟨a, ha⟩ := hiid (u q)
  refine ⟨a, ?_⟩
  letI : Nonempty (Fin b) := ⟨⟨0, by omega⟩⟩
  unfold observedSeedUniformIidWordCesaro at ha
  have heq : realCesaroMean
      (radixContextProportion (fun n => l (u n) ≠ 0) b q) =
      uniformIidWordCesaro (observedSeedWordSupport T l (u q)) := by
    funext N
    unfold realCesaroMean uniformIidWordCesaro
    simp only [smul_eq_mul, inv_mul_eq_div]
    congr 1
    apply Finset.sum_congr rfl
    intro r hr
    rw [radixContextProportion_eq_uniformIidWordAverage b hb T u hrec l q r]
    rfl
  rw [heq]
  exact ha

/-- Conditional standard logarithmic-density existence for a padded linear
digit recurrence over an arbitrary commutative ring. -/
theorem exists_standardLogDensity_of_observedSeedIidCesaro
    (b : ℕ) (hb : 2 ≤ b) (T : Fin b → Module.End K V) (u : ℕ → V)
    (hrec : ∀ n (a : Fin b), u (b * n + a.val) = T a (u n))
    (l : Module.Dual K V)
    (hiid : HasObservedSeedIidCesaroMeans (by omega) T l) :
    ∃ delta : ℝ,
      HasPredicateStandardLogDensity (fun n => l (u n) ≠ 0) delta := by
  exact hasPredicateStandardLogDensity_of_allFixedContextCesaro _ b hb
    (observedSeedIidCesaro_hasAllFixedContextCesaroMeans b hb T u hrec l hiid)

/-- Conditional shifted-harmonic logarithmic-density existence for the same
recurrence. -/
theorem exists_logDensity_of_observedSeedIidCesaro
    (b : ℕ) (hb : 2 ≤ b) (T : Fin b → Module.End K V) (u : ℕ → V)
    (hrec : ∀ n (a : Fin b), u (b * n + a.val) = T a (u n))
    (l : Module.Dual K V)
    (hiid : HasObservedSeedIidCesaroMeans (by omega) T l) :
    ∃ delta : ℝ, HasPredicateLogDensity (fun n => l (u n) ≠ 0) delta := by
  exact hasPredicateLogDensity_of_allFixedContextCesaro _ b hb
    (observedSeedIidCesaro_hasAllFixedContextCesaroMeans b hb T u hrec l hiid)

end MatrixRecurrence

end IndependentZeroBlocks
