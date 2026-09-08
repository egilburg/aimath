import SierpinskiFormal.AuxiliaryField

set_option autoImplicit false

/-!
# A universal finite auxiliary field

The field constructed here depends only on the base field and the order of
the required root of unity.  It works simultaneously for every polynomial
over the base field: after adjoining a primitive root of unity, we adjoin a
`(card K - 1)`-st root of every element of that finite intermediate field.
-/

namespace IndependentZeroBlocks

open SierpinskiFormal

universe u

section UniversalAuxiliaryField

variable {K : Type u} [Field K] [Fintype K]

/-- There is one finite extension, independent of `A`, containing a primitive
`s`-th root `ζ` and a `(card K - 1)`-st root of every evaluation of every
polynomial over `K` at every inverse natural power of `ζ`. -/
theorem exists_universal_auxiliary_field_with_powerRoots
    (s : ℕ) (hs : 0 < s) (hchar : ¬ringChar K ∣ s) :
    ∃ (L : Type u) (_ : Field L) (_ : Fintype L) (_ : Algebra K L) (ζ : L),
      IsPrimitiveRoot ζ s ∧
      ∀ (A : Polynomial K) (i : ℕ), ∃ ρ : L,
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
      (Polynomial.X : Polynomial E) (Fintype.card K - 1) hb
  letI : Field L := hLfield
  letI : Fintype L := hLfintype
  letI : Algebra K L := hKalg
  letI : Algebra E L := hEalg
  letI : IsScalarTower K E L := htower
  let ζ : L := algebraMap E L ζE
  refine ⟨L, inferInstance, inferInstance, inferInstance, ζ, ?_, ?_⟩
  · simpa [ζ, n] using hζE.map_of_injective (algebraMap E L).injective
  · intro A i
    let x : E := (A.map (algebraMap K E)).eval ((ζE ^ i)⁻¹)
    obtain ⟨ρ, hρ⟩ := hroots x
    refine ⟨ρ, ?_⟩
    calc
      ρ ^ (Fintype.card K - 1) = algebraMap E L x := by
        simpa only [Polynomial.eval_X] using hρ
      _ = (A.map (algebraMap K L)).eval
          (algebraMap E L ((ζE ^ i)⁻¹)) := by
        dsimp only [x]
        exact algebraMap_eval_map (K := K) A ((ζE ^ i)⁻¹)
      _ = (A.map (algebraMap K L)).eval ((ζ ^ i)⁻¹) := by
        simp only [map_inv₀, map_pow, ζ]

/-- Quotient-power form of the universal construction.  The witnesses `L`
and `ζ` precede the quantifier over `A`, so the same extension works for all
polynomials simultaneously. -/
theorem exists_universal_auxiliary_field
    (s : ℕ) (hs : 0 < s) (hchar : ¬ringChar K ∣ s) :
    ∃ (L : Type u) (_ : Field L) (_ : Fintype L) (_ : Algebra K L) (ζ : L),
      IsPrimitiveRoot ζ s ∧
      ∀ (A : Polynomial K) (i : ℕ),
        let z := (A.map (algebraMap K L)).eval ((ζ ^ i)⁻¹)
        z = 0 ∨
          z ^ ((Fintype.card L - 1) / (Fintype.card K - 1)) = 1 := by
  obtain ⟨L, hLfield, hLfintype, hLalg, ζ, hζ, hroots⟩ :=
    exists_universal_auxiliary_field_with_powerRoots (K := K) s hs hchar
  letI : Field L := hLfield
  letI : Fintype L := hLfintype
  letI : Algebra K L := hLalg
  refine ⟨L, inferInstance, inferInstance, inferInstance, ζ, hζ, ?_⟩
  intro A i
  dsimp only
  obtain ⟨ρ, hρ⟩ := hroots A i
  exact eq_zero_or_pow_cardSubOne_div_eq_one_of_powerRoot
    (Fintype.card K - 1)
    (card_sub_one_dvd_of_finite_extension (K := K) (L := L)
      (Fintype.card K - 1) (dvd_refl _))
    ((A.map (algebraMap K L)).eval ((ζ ^ i)⁻¹)) ρ hρ

end UniversalAuxiliaryField

end IndependentZeroBlocks

#print axioms IndependentZeroBlocks.exists_universal_auxiliary_field_with_powerRoots
#print axioms IndependentZeroBlocks.exists_universal_auxiliary_field
