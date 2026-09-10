import SierpinskiFormal.ZeroCylinderCounting
import SierpinskiFormal.CommRingObservationFamilies

set_option autoImplicit false
namespace IndependentZeroBlocks

/-- No index whose padded radix expansion contains this word belongs to
the support. Contexts and word order are both explicit. -/
def AvoidsDigitWord (b : ℕ) (bad : ℕ → Prop) (w : List (Fin b)) : Prop :=
  ∀ v z : List (Fin b), ¬bad (Nat.ofDigits b ((v ++ w ++ z).map Fin.val))

/-- Some nonempty radix factor is absent from the padded expansions of
every supported index. -/
def HasForbiddenDigitWord (b : ℕ) (bad : ℕ → Prop) : Prop :=
  ∃ w : List (Fin b), 0 < w.length ∧ AvoidsDigitWord b bad w

theorem forbiddenWord_exponent_mem_Ico
    (b : ℕ) (hb : 2 ≤ b) (w : List (Fin b)) (hlen : 0 < w.length) :
    Real.log ((b ^ w.length - 1 : ℕ) : ℝ) / Real.log ((b ^ w.length : ℕ) : ℝ) ∈
      Set.Ico (0 : ℝ) 1 := by
  have hB : 2 ≤ b ^ w.length := hb.trans (Nat.le_self_pow (by omega) b)
  exact radixLogExponent_mem_Ico _ _ hB (by omega) (by omega)

theorem avoidsDigitWord_zeroCylinder
    (b : ℕ) (hb : 2 ≤ b) (bad : ℕ → Prop) (w : List (Fin b))
    (hw : AvoidsDigitWord b bad w) :
    ∀ k q j : ℕ, j < (b ^ w.length) ^ k →
      ¬bad ((b ^ w.length) ^ (k + 1) * q +
        (b ^ w.length) ^ k * Nat.ofDigits b (w.map Fin.val) + j) := by
  intro k q j hj
  obtain ⟨v, hvlen, hvval⟩ := exists_fin_digit_word_of_lt_pow b hb (w.length * k) j
    (by simpa only [pow_mul] using hj)
  obtain ⟨z, _, hzval⟩ := exists_fin_digit_word_of_lt_pow b hb (Nat.log b q + 1) q
    (Nat.lt_pow_succ_log_self (by omega) q)
  have hindex : Nat.ofDigits b ((v ++ w ++ z).map Fin.val) =
      (b ^ w.length) ^ (k + 1) * q +
        (b ^ w.length) ^ k * Nat.ofDigits b (w.map Fin.val) + j := by
    simp only [List.map_append, Nat.ofDigits_append, List.length_map,
      List.length_append, hvlen, hvval, hzval]
    simp only [pow_add, pow_mul, pow_succ]
    ring
  rw [← hindex]
  exact hw v z

theorem fin_word_value_lt_pow (b : ℕ) (hb : 2 ≤ b) (w : List (Fin b)) :
    Nat.ofDigits b (w.map Fin.val) < b ^ w.length := by
  have h := Nat.ofDigits_lt_base_pow_length (by omega : 1 < b)
    (show ∀ r ∈ w.map Fin.val, r < b from by
      intro r hr
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hr
      exact a.isLt)
  simpa using h

/-- A forbidden word of length ell gives the explicit exponent
log(b^ell-1)/log(b^ell), uniformly over all translated intervals. -/
theorem avoidsDigitWord_interval_count
    (b : ℕ) (hb : 2 ≤ b) (bad : ℕ → Prop) (w : List (Fin b))
    (hlen : 0 < w.length) (hw : AvoidsDigitWord b bad w)
    (a L : ℕ) (hL : 1 ≤ L) :
    (intervalPredicateCount bad a L : ℝ) ≤
      ((2 * (b ^ w.length - 1) : ℕ) : ℝ) * (L : ℝ) ^
        (Real.log ((b ^ w.length - 1 : ℕ) : ℝ) / Real.log ((b ^ w.length : ℕ) : ℝ)) := by
  exact intervalPredicateCount_le_of_zeroCylinder bad (b ^ w.length)
    (Nat.ofDigits b (w.map Fin.val))
    (hb.trans (Nat.le_self_pow (by omega) b))
    (fin_word_value_lt_pow b hb w) (avoidsDigitWord_zeroCylinder b hb bad w hw) a L hL

theorem avoidsDigitWord_radix_count
    (b : ℕ) (hb : 2 ≤ b) (bad : ℕ → Prop) (w : List (Fin b))
    (hlen : 0 < w.length) (hw : AvoidsDigitWord b bad w) (k : ℕ) :
    predicateCount bad ((b ^ w.length) ^ k) ≤ (b ^ w.length - 1) ^ k := by
  exact predicateCount_pow_le_of_zeroCylinder bad (b ^ w.length)
    (Nat.ofDigits b (w.map Fin.val))
    (hb.trans (Nat.le_self_pow (by omega) b))
    (fin_word_value_lt_pow b hb w) (avoidsDigitWord_zeroCylinder b hb bad w hw) k

/-- The observed-family certificate depends only on the output support:
it is exactly a forbidden finite factor, with nonempty witnesses available. -/
theorem observedFamilyWordMortal_iff_forbidden_word
    {K V J : Type*} [CommSemiring K] [AddCommMonoid V] [Module K V]
    (b : ℕ) (hb : 2 ≤ b) (T : Fin b → Module.End K V) (u : ℕ → V)
    (hrec : ∀ n (r : Fin b), u (b * n + r.val) = T r (u n))
    (l : J → Module.Dual K V) :
    ObservedFamilyWordMortal T l (u 0) ↔
      ∃ w : List (Fin b), 0 < w.length ∧
        AvoidsDigitWord b (fun n => ∃ i, l i (u n) ≠ 0) w := by
  constructor
  · rintro ⟨w, hw⟩
    let r : Fin b := ⟨0, by omega⟩
    refine ⟨r :: w, by simp, ?_⟩
    intro v z hbad
    obtain ⟨i, hi⟩ := hbad
    apply hi
    rw [← linearWord_apply_digitRecurrence_seed b T u hrec]
    have h := hw i (v ++ [r]) z
    simpa only [List.append_assoc, List.singleton_append] using h
  · rintro ⟨w, _, hw⟩
    refine ⟨w, ?_⟩
    intro i v z
    rw [linearWord_apply_digitRecurrence_seed b T u hrec]
    by_contra hn
    exact hw v z ⟨i, hn⟩

end IndependentZeroBlocks
