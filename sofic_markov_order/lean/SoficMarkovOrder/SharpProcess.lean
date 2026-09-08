import SoficMarkovOrder.RationalSharpness
import SoficMarkovOrder.UniformRealization
import SoficMarkovOrder.CanonicalHankel

set_option autoImplicit false
noncomputable section
namespace SoficMarkovOrder
open MeasureTheory
open scoped BigOperators

/-- Sharpness as an actual stationary probability process, with an explicit
nonnegative rational presentation. The alphabet is allowed to depend on n. -/
theorem exists_rational_sharp_sofic_process (n : ℕ) (hn : 2 ≤ n) :
    ∃ (A : Type) (_ : Fintype A) (_ : MeasurableSpace A)
      (_ : MeasurableSingletonClass A) (μ : Measure (ℕ → A))
      (T : A → Module.End ℝ (Fin n → ℝ)),
      IsProbabilityMeasure μ ∧
      MeasurePreserving sequenceShift μ μ ∧
      (∀ w, μ.real (wordCylinder w) = representedWord T averageRow (fun _ => 1) w) ∧
      (∀ a i j, 0 ≤ endEntry (T a) i j ∧ RationalReal (endEntry (T a) i j)) ∧
      (∑ a, T a) = uniformMean ∧
      WordReduced T averageRow (fun _ => 1) ∧
      Module.finrank ℝ (wordHankelSpan (fun w => μ.real (wordCylinder w))) = n ∧
      ProcessMarkov μ (n.choose 2) ∧
      (∀ k < n.choose 2, ¬ProcessMarkov μ k) := by
  letI : NeZero n := ⟨by omega⟩
  let A := SharpAlphabet (Fin n) (n.choose 2)
  letI : MeasurableSpace A := ⊤
  letI : MeasurableSingletonClass A := ⟨fun _ => trivial⟩
  let e := canonicalPairEnumeration n
  have hD := Nat.choose_pos hn
  let T : A → Module.End ℝ (Fin n → ℝ) := sharpLetter e
  have h0 : ∀ a i j, 0 ≤ endEntry (T a) i j := by
    intro a i j
    apply sharpLetter_nonneg e hD a (Pi.single j 1) _ i
    intro k
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  have hsum : ∑ a, T a = uniformMean := sum_sharpLetter e
  let μ := uniformSoficMeasure T h0 hsum
  have hstat : MeasurePreserving sequenceShift μ μ := uniformSoficMeasure_stationary T h0 hsum
  have hrep : ∀ w, μ.real (wordCylinder w) = representedWord T averageRow (fun _ => 1) w :=
    uniformSoficMeasure_cylinder T h0 hsum
  have hmass : (fun w => μ.real (wordCylinder w)) = (sharpLaw e hD).mass := funext hrep
  have hiff (k : ℕ) : ProcessMarkov μ k ↔ (sharpLaw e hD).ConditionalMarkov k := by
    unfold ProcessMarkov StationaryWordLaw.ConditionalMarkov
    simp only [hrep]
    rfl
  refine ⟨A, inferInstance, inferInstance, inferInstance, μ, T, inferInstance, hstat,
    hrep, fun a i j => ⟨h0 a i j, sharpLetter_entry_rational e a i j⟩,
    hsum, sharp_reduced e hD, ?_, (hiff _).mpr (sharpLaw_exact_order e hD).1, ?_⟩
  · rw [hmass]
    simpa using sharpLaw_hankel_dimension e hD
  · intro k hk hm
    exact (sharpLaw_exact_order e hD).2 k hk ((hiff k).mp hm)

end SoficMarkovOrder
