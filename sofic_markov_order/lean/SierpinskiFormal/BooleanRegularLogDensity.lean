import SierpinskiFormal.SupportLogDensityExistence
import SierpinskiFormal.PaddedStableLogDensity

set_option autoImplicit false

/-!
# Logarithmic density for finite Boolean combinations of regular supports

The padded support kernel of each intrinsic radix-regular sequence has the
Boolean double-limit property.  Closure under finite Boolean operations and
the padded-language transfer therefore give logarithmic-density existence
without choosing a common matrix representation.
-/

noncomputable section

namespace IndependentZeroBlocks

/-- The natural-number predicate obtained by applying a finite Boolean
operation to nonzero tests of regular sequences. -/
def booleanRegularSupport
    {K : Type*} [CommRing K] {d : ℕ}
    (op : (Fin d → Bool) → Bool) (f : Fin d → ℕ → K) : ℕ → Prop :=
  fun n ↦ op (fun i ↦ nonzeroBool (f i n)) = true

/-- Finite Boolean combinations of intrinsic regular support languages have
a stable padded digit kernel. -/
theorem booleanRegularSupport_hasStablePaddedDigitKernel
    {K : Type*} [CommRing K] {d : ℕ}
    (b : ℕ) (hb : 2 ≤ b) (op : (Fin d → Bool) → Bool)
    (f : Fin d → ℕ → K) (hregular : ∀ i, IsRadixRegular b (f i)) :
    HasStablePaddedDigitKernel (booleanRegularSupport op f) b := by
  classical
  have hcombine := hasBooleanDoubleLimitProperty_booleanCombine op
    (fun (i : Fin d) (x y : List (Fin b)) ↦
      nonzeroBool (f i (Nat.ofDigits b ((x ++ y).map Fin.val))))
    (fun i ↦ radixRegular_paddedSupportKernel_hasBooleanDoubleLimitProperty
      b hb (f i) (hregular i))
  change HasBooleanDoubleLimitProperty (fun x y : List (Fin b) =>
    op (fun i => nonzeroBool (f i (Nat.ofDigits b ((x ++ y).map Fin.val))))) at hcombine
  simpa [HasStablePaddedDigitKernel, paddedPredicateBool,
    booleanRegularSupport, booleanCombine] using hcombine

/-- Every finite Boolean combination of nonzero predicates of radix-regular
sequences has a standard logarithmic density. -/
theorem booleanRegularSupport_standardLogDensity_exists
    {K : Type*} [CommRing K] {d : ℕ}
    (b : ℕ) (hb : 2 ≤ b) (op : (Fin d → Bool) → Bool)
    (f : Fin d → ℕ → K) (hregular : ∀ i, IsRadixRegular b (f i)) :
    ∃ delta : ℝ,
      HasPredicateStandardLogDensity (booleanRegularSupport op f) delta := by
  exact (booleanRegularSupport_hasStablePaddedDigitKernel
    b hb op f hregular).exists_standardLogDensity hb

/-- The same Boolean support predicate has logarithmic density in the
shifted-harmonic convention. -/
theorem booleanRegularSupport_logDensity_exists
    {K : Type*} [CommRing K] {d : ℕ}
    (b : ℕ) (hb : 2 ≤ b) (op : (Fin d → Bool) → Bool)
    (f : Fin d → ℕ → K) (hregular : ∀ i, IsRadixRegular b (f i)) :
    ∃ delta : ℝ, HasPredicateLogDensity (booleanRegularSupport op f) delta := by
  obtain ⟨delta, hdelta⟩ :=
    booleanRegularSupport_standardLogDensity_exists b hb op f hregular
  exact ⟨delta, (hasPredicateLogDensity_iff_standard _ _).mpr hdelta⟩

/-- A finite union of intrinsic radix-regular supports has a standard
logarithmic density. -/
theorem radixRegular_family_support_standardLogDensity_exists
    {K J : Type*} [CommRing K] [Fintype J]
    (b : ℕ) (hb : 2 ≤ b) (f : J → ℕ → K)
    (hregular : ∀ i, IsRadixRegular b (f i)) :
    ∃ delta : ℝ,
      HasPredicateStandardLogDensity (fun n ↦ ∃ i, f i n ≠ 0) delta := by
  classical
  let e : J ≃ Fin (Fintype.card J) := Fintype.equivFin J
  let op : (Fin (Fintype.card J) → Bool) → Bool := fun values ↦
    decide (∃ i, values i = true)
  obtain ⟨delta, hdelta⟩ := booleanRegularSupport_standardLogDensity_exists
    b hb op (fun i ↦ f (e.symm i)) (fun i ↦ hregular (e.symm i))
  refine ⟨delta, ?_⟩
  have hsupp : booleanRegularSupport op (fun i ↦ f (e.symm i)) =
      (fun n ↦ ∃ i, f i n ≠ 0) := by
    funext n
    apply propext
    simp only [booleanRegularSupport, op, decide_eq_true_iff]
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨e.symm i, ?_⟩
      simpa [nonzeroBool] using hi
    · rintro ⟨i, hi⟩
      refine ⟨e i, ?_⟩
      simpa [nonzeroBool] using hi
  rw [hsupp] at hdelta
  exact hdelta

/-- A finite union of intrinsic radix-regular supports also has logarithmic
density in the shifted-harmonic convention. -/
theorem radixRegular_family_support_logDensity_exists
    {K J : Type*} [CommRing K] [Fintype J]
    (b : ℕ) (hb : 2 ≤ b) (f : J → ℕ → K)
    (hregular : ∀ i, IsRadixRegular b (f i)) :
    ∃ delta : ℝ,
      HasPredicateLogDensity (fun n ↦ ∃ i, f i n ≠ 0) delta := by
  obtain ⟨delta, hdelta⟩ :=
    radixRegular_family_support_standardLogDensity_exists b hb f hregular
  exact ⟨delta, (hasPredicateLogDensity_iff_standard _ _).mpr hdelta⟩

/-- Failure of any identity in a finite family of polynomial observations of
radix-regular sequences has a standard logarithmic density. -/
theorem polynomial_observed_regular_support_standardLogDensity_exists
    {K I J : Type*} [CommRing K] [Fintype J]
    (b : ℕ) (hb : 2 ≤ b) (f : I → ℕ → K)
    (hregular : ∀ i, IsRadixRegular b (f i))
    (P : J → MvPolynomial I K) :
    ∃ delta : ℝ, HasPredicateStandardLogDensity
      (fun n ↦ ∃ j,
        MvPolynomial.eval (fun i ↦ f i n) (P j) ≠ 0) delta := by
  exact radixRegular_family_support_standardLogDensity_exists b hb
    (fun j n ↦ MvPolynomial.eval (fun i ↦ f i n) (P j))
    (fun j ↦ IsRadixRegular.polynomial b hb f hregular (P j))

/-- Shifted-harmonic version of finite polynomial-observation support
existence. -/
theorem polynomial_observed_regular_support_logDensity_exists
    {K I J : Type*} [CommRing K] [Fintype J]
    (b : ℕ) (hb : 2 ≤ b) (f : I → ℕ → K)
    (hregular : ∀ i, IsRadixRegular b (f i))
    (P : J → MvPolynomial I K) :
    ∃ delta : ℝ, HasPredicateLogDensity
      (fun n ↦ ∃ j,
        MvPolynomial.eval (fun i ↦ f i n) (P j) ≠ 0) delta := by
  obtain ⟨delta, hdelta⟩ :=
    polynomial_observed_regular_support_standardLogDensity_exists
      b hb f hregular P
  exact ⟨delta, (hasPredicateLogDensity_iff_standard _ _).mpr hdelta⟩

end IndependentZeroBlocks
