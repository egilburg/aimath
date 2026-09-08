import SierpinskiFormal.PoleEvaluation
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.NumberTheory.Cyclotomic.Basic

set_option autoImplicit false

/-!
# A finite auxiliary field for pole evaluations

This file constructs finite splitting-field towers in which every value of a
fixed polynomial has a prescribed power root.  The final construction first
adjoins a primitive root of unity and then all the needed power roots.
-/

namespace IndependentZeroBlocks

open SierpinskiFormal
open scoped BigOperators

universe u

section PowerRootClosure

variable {K E : Type u} [Field K] [Field E] [Fintype E] [Algebra K E]

/-- A polynomial whose splitting field contains a `b`-th root of `A x` for
every `x` in the finite field `E`. -/
noncomputable def powerRootClosurePolynomial (A : Polynomial E) (b : ℕ) :
    Polynomial E :=
  ∏ x : E, (Polynomial.X ^ b - Polynomial.C (A.eval x))

theorem powerRootClosurePolynomial_monic
    (A : Polynomial E) (b : ℕ) (hb : 0 < b) :
    (powerRootClosurePolynomial A b).Monic := by
  classical
  apply Polynomial.monic_prod_of_monic
  intro x hx
  exact Polynomial.monic_X_pow_sub_C _ (Nat.ne_of_gt hb)

/-- The splitting field of `powerRootClosurePolynomial` is a finite extension
of both `E` and its base field `K`, with the canonical scalar tower, and it
simultaneously contains all the requested power roots. -/
theorem exists_finite_powerRoot_tower
    (A : Polynomial E) (b : ℕ) (hb : 0 < b) :
    ∃ (L : Type u) (_ : Field L) (_ : Fintype L)
        (_ : Algebra K L) (_ : Algebra E L) (_ : IsScalarTower K E L),
      ∀ x : E, ∃ y : L, y ^ b = algebraMap E L (A.eval x) := by
  classical
  let H := powerRootClosurePolynomial A b
  let L := H.SplittingField
  letI : Field L := inferInstance
  letI : Algebra E L := inferInstance
  letI : Algebra K L := inferInstance
  letI : IsScalarTower K E L := inferInstance
  letI : Finite L := inferInstance
  letI : Fintype L := Fintype.ofFinite L
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, ?_⟩
  intro x
  let g : Polynomial E := Polynomial.X ^ b - Polynomial.C (A.eval x)
  have hHmonic : H.Monic := powerRootClosurePolynomial_monic A b hb
  have hgdiv : g ∣ H := by
    dsimp only [g, H, powerRootClosurePolynomial]
    exact Finset.dvd_prod_of_mem (fun z : E =>
      Polynomial.X ^ b - Polynomial.C (A.eval z)) (Finset.mem_univ x)
  have hgsplits : (g.map (algebraMap E L)).Splits :=
    (Polynomial.SplittingField.splits H).of_dvd
      (Polynomial.map_ne_zero hHmonic.ne_zero)
      (Polynomial.map_dvd (algebraMap E L) hgdiv)
  have hgdegree : g.degree ≠ 0 := by
    rw [show g.degree = b by
      dsimp only [g]
      exact Polynomial.degree_X_pow_sub_C hb (A.eval x)]
    exact_mod_cast (Nat.ne_of_gt hb)
  obtain ⟨y, hy⟩ := hgsplits.exists_eval_eq_zero (by
    rw [Polynomial.degree_map]
    exact hgdegree)
  refine ⟨y, ?_⟩
  dsimp only [g] at hy
  have hy' : y ^ b - algebraMap E L (A.eval x) = 0 := by
    simpa using hy
  exact sub_eq_zero.mp hy'

omit [Fintype E] in
/-- Evaluation commutes with the two algebra maps in a scalar tower. -/
theorem algebraMap_eval_map
    {L : Type u} [Field L] [Algebra E L] [Algebra K L]
    [IsScalarTower K E L] (A : Polynomial K) (x : E) :
    algebraMap E L ((A.map (algebraMap K E)).eval x) =
      (A.map (algebraMap K L)).eval (algebraMap E L x) := by
  calc
    algebraMap E L ((A.map (algebraMap K E)).eval x) =
        algebraMap E L (A.eval₂ (algebraMap K E) x) := by
          rw [Polynomial.eval_map]
    _ = A.eval₂ ((algebraMap E L).comp (algebraMap K E))
        (algebraMap E L x) := Polynomial.hom_eval₂ _ _ _ _
    _ = A.eval₂ (algebraMap K L) (algebraMap E L x) := by
      rw [← IsScalarTower.algebraMap_eq K E L]
    _ = (A.map (algebraMap K L)).eval (algebraMap E L x) := by
      rw [Polynomial.eval_map]

/-- If `z` has a `b`-th root in a finite field and `b` divides the order of
the multiplicative group, then the quotient power of `z` is one unless `z`
is zero. -/
theorem eq_zero_or_pow_cardSubOne_div_eq_one_of_powerRoot
    {L : Type*} [Field L] [Fintype L]
    (b : ℕ) (hb : b ∣ Fintype.card L - 1) (z y : L)
    (hy : y ^ b = z) :
    z = 0 ∨ z ^ ((Fintype.card L - 1) / b) = 1 := by
  by_cases hz : z = 0
  · exact Or.inl hz
  · right
    have hbne : b ≠ 0 := by
      intro hbzero
      subst b
      simp only [zero_dvd_iff] at hb
      have := Fintype.one_lt_card (α := L)
      omega
    have hyne : y ≠ 0 := by
      intro hyzero
      apply hz
      rw [← hy, hyzero]
      simp [hbne]
    calc
      z ^ ((Fintype.card L - 1) / b) =
          (y ^ b) ^ ((Fintype.card L - 1) / b) := by rw [hy]
      _ = y ^ (b * ((Fintype.card L - 1) / b)) := by rw [pow_mul]
      _ = y ^ (Fintype.card L - 1) := by rw [Nat.mul_div_cancel' hb]
      _ = 1 := FiniteField.pow_card_sub_one_eq_one y hyne

end PowerRootClosure

section AuxiliaryField

variable {K : Type u} [Field K] [Fintype K]

/-- A finite extension containing a primitive `s`-th root `ζ` and a
`(card K - 1)`-st root of every evaluation of `A` at an inverse power of
`ζ`.  The conclusion is stated for every natural exponent, which is stronger
than the range `i < s` needed in pole-evaluation applications. -/
theorem exists_auxiliary_field
    (A : Polynomial K) (s : ℕ) (hs : 0 < s)
    (hchar : ¬ringChar K ∣ s) :
    ∃ (L : Type u) (_ : Field L) (_ : Fintype L) (_ : Algebra K L) (ζ : L),
      IsPrimitiveRoot ζ s ∧
      ∀ i : ℕ, ∃ ρ : L,
        ρ ^ (Fintype.card K - 1) =
          (A.map (algebraMap K L)).eval ((ζ ^ i)⁻¹) := by
  let n : ℕ+ := ⟨s, hs⟩
  have hsK : (s : K) ≠ 0 := by
    intro hs0
    exact hchar ((ringChar.spec K s).mp hs0)
  letI : NeZero ((n : ℕ) : K) := ⟨by simpa [n] using hsK⟩
  letI : Finite K := Finite.of_fintype K
  let E := CyclotomicField n K
  letI : Field E := inferInstance
  letI : Algebra K E := inferInstance
  letI : Finite E := by
    dsimp only [E, CyclotomicField]
    infer_instance
  letI : Fintype E := Fintype.ofFinite E
  obtain ⟨ζE, hζE⟩ :=
    IsCyclotomicExtension.exists_isPrimitiveRoot K E
      (Set.mem_singleton (n : ℕ)) n.ne_zero
  have hb : 0 < Fintype.card K - 1 := by
    have := Fintype.one_lt_card (α := K)
    omega
  obtain ⟨L, hLfield, hLfintype, hKalg, hEalg, htower, hroots⟩ :=
    exists_finite_powerRoot_tower (K := K)
      (A.map (algebraMap K E)) (Fintype.card K - 1) hb
  letI : Field L := hLfield
  letI : Fintype L := hLfintype
  letI : Algebra K L := hKalg
  letI : Algebra E L := hEalg
  letI : IsScalarTower K E L := htower
  let ζ : L := algebraMap E L ζE
  refine ⟨L, inferInstance, inferInstance, inferInstance, ζ, ?_, ?_⟩
  · simpa [ζ, n] using hζE.map_of_injective (algebraMap E L).injective
  · intro i
    obtain ⟨ρ, hρ⟩ := hroots ((ζE ^ i)⁻¹)
    refine ⟨ρ, hρ.trans ?_⟩
    rw [algebraMap_eval_map (K := K) A]
    simp only [map_inv₀, map_pow, ζ]

/-- The quotient-power form of `exists_auxiliary_field`: every relevant
kernel evaluation is either zero or becomes one after raising it to the
extension quotient exponent. -/
theorem exists_auxiliary_field_with_eval_zero_or_one
    (A : Polynomial K) (s : ℕ) (hs : 0 < s)
    (hchar : ¬ringChar K ∣ s) :
    ∃ (L : Type u) (_ : Field L) (_ : Fintype L) (_ : Algebra K L) (ζ : L),
      IsPrimitiveRoot ζ s ∧
      ∀ i : ℕ,
        let z := (A.map (algebraMap K L)).eval ((ζ ^ i)⁻¹)
        z = 0 ∨
          z ^ ((Fintype.card L - 1) / (Fintype.card K - 1)) = 1 := by
  obtain ⟨L, hLfield, hLfintype, hLalg, ζ, hζ, hroots⟩ :=
    exists_auxiliary_field A s hs hchar
  letI : Field L := hLfield
  letI : Fintype L := hLfintype
  letI : Algebra K L := hLalg
  refine ⟨L, inferInstance, inferInstance, inferInstance, ζ, hζ, ?_⟩
  intro i
  dsimp only
  obtain ⟨ρ, hρ⟩ := hroots i
  exact eq_zero_or_pow_cardSubOne_div_eq_one_of_powerRoot
    (Fintype.card K - 1)
    (card_sub_one_dvd_of_finite_extension (K := K) (L := L)
      (Fintype.card K - 1) (dvd_refl _))
    ((A.map (algebraMap K L)).eval ((ζ ^ i)⁻¹)) ρ hρ

end AuxiliaryField

end IndependentZeroBlocks

#print axioms IndependentZeroBlocks.exists_finite_powerRoot_tower
#print axioms IndependentZeroBlocks.eq_zero_or_pow_cardSubOne_div_eq_one_of_powerRoot
#print axioms IndependentZeroBlocks.exists_auxiliary_field
#print axioms IndependentZeroBlocks.exists_auxiliary_field_with_eval_zero_or_one
