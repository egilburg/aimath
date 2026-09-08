import SierpinskiFormal.CommRingObservationGeometry
import SierpinskiFormal.RadixRegularRepresentation

set_option autoImplicit false
namespace IndependentZeroBlocks
open scoped BigOperators

variable {K ι : Type*} [CommRing K] [Fintype ι]

/-- Every scalar output of a finite matrix digit recurrence over an arbitrary
commutative ring is radix-regular.  Finite generation is proved after
descending the finite coefficient data to a Noetherian subring, then cast
back to the ambient ring. -/
theorem matrix_observation_isRadixRegular
    (b : ℕ) (hb : 2 ≤ b) (M : Fin b → Matrix ι ι K) (u : ℕ → ι → K)
    (hrec : ∀ n (r : Fin b),
      u (b * n + r.val) = Matrix.mulVecLin (M r) (u n))
    (l : Module.Dual K (ι → K)) :
    IsRadixRegular b (fun n ↦ l (u n)) := by
  classical
  let f : ℕ → K := fun n ↦ l (u n)
  let a : ι → K := fun i ↦ l (coordinateUnit i)
  obtain ⟨S, hS, M', u', a', _, _, _, hrec', hout⟩ :=
    linearObservation_exists_noetherian_descent b hb M u a hrec
  letI : IsNoetherianRing S := hS
  let T' : Fin b → Module.End S (ι → S) :=
    fun r ↦ Matrix.mulVecLin (M' r)
  let l' : Module.Dual S (ι → S) := coordinateRowDual a'
  have hl (n : ℕ) : ((l' (u' n) : S) : K) = f n := by
    change ((l' (u' n) : S) : K) = l (u n)
    rw [show l' (u' n) = ∑ i, a' i * u' n i by
      exact coordinateRowDual_apply a' (u' n)]
    rw [hout n]
    change ∑ i, l (coordinateUnit i) * u n i = l (u n)
    exact (dual_apply_eq_sum_single l (u n)).symm
  let row : List (Fin b) → Module.Dual S (ι → S) :=
    fun w ↦ l'.comp (linearWord T' w)
  have hrowfg : (Submodule.span S (Set.range row)).FG :=
    isNoetherian_def.mp inferInstance _
  obtain ⟨d, words, hspan⟩ :=
    finite_original_generators_of_fg_span_range row hrowfg
  have hsection (v : List (Fin b)) (n : ℕ) :
      ((row v (u' n) : S) : K) = radixWordSection b f v n := by
    change ((l' (linearWord T' v (u' n)) : S) : K) =
      f (b ^ v.length * n + Nat.ofDigits b (v.map Fin.val))
    rw [linearWord_apply_digitRecurrence b T' u' hrec']
    exact hl _
  have hgenerates : Submodule.span K
      (Set.range fun i ↦ radixWordSection b f (words i)) =
      RadixKernelSpan b f := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro x ⟨i, rfl⟩
      exact Submodule.subset_span ⟨words i, rfl⟩
    · apply Submodule.span_le.mpr
      rintro x ⟨v, rfl⟩
      have hv : row v ∈ Submodule.span S (Set.range fun i ↦ row (words i)) := by
        rw [hspan]
        exact Submodule.subset_span ⟨v, rfl⟩
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun S).mp hv
      have hfun : radixWordSection b f v =
          ∑ i, (c i : K) • radixWordSection b f (words i) := by
        funext n
        have hevaln : ∑ i, c i * row (words i) (u' n) = row v (u' n) := by
          have h := congrArg (fun q : Module.Dual S (ι → S) ↦ q (u' n)) hc
          simpa [smul_eq_mul] using h
        have hevalnK := congrArg (fun x : S ↦ (x : K)) hevaln
        push_cast at hevalnK
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        calc
          radixWordSection b f v n = ((row v (u' n) : S) : K) :=
            (hsection v n).symm
          _ = ∑ i, (c i : K) * ((row (words i) (u' n) : S) : K) :=
            hevalnK.symm
          _ = ∑ i, (c i : K) * radixWordSection b f (words i) n := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hsection]
      rw [hfun]
      apply Submodule.sum_mem
      intro i hi
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  change (RadixKernelSpan b f).FG
  rw [← hgenerates]
  exact Submodule.fg_span (Set.finite_range fun i ↦ radixWordSection b f (words i))

/-- Intrinsic radix-regularity is equivalent to admitting some finite matrix
digit representation with a linear output. -/
theorem isRadixRegular_iff_exists_matrix_representation
    (b : ℕ) (hb : 2 ≤ b) (f : ℕ → K) :
    IsRadixRegular b f ↔
      ∃ (d : ℕ) (M : Fin b → Matrix (Fin d) (Fin d) K)
        (u : ℕ → Fin d → K) (l : Module.Dual K (Fin d → K)),
        (∀ n (r : Fin b),
          u (b * n + r.val) = Matrix.mulVecLin (M r) (u n)) ∧
        (∀ n, l (u n) = f n) := by
  constructor
  · exact radixRegular_exists_matrix_representation b hb f
  · rintro ⟨d, M, u, l, hrec, hout⟩
    have hr := matrix_observation_isRadixRegular b hb M u hrec l
    simpa only [hout] using hr

end IndependentZeroBlocks
