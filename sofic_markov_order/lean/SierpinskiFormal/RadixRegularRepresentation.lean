import SierpinskiFormal.ObservableNoetherian
import Mathlib.LinearAlgebra.Matrix.ToLin

set_option autoImplicit false
namespace IndependentZeroBlocks
open scoped BigOperators

variable {K : Type*} [CommRing K]

/-- The section of a scalar sequence obtained by fixing a padded
little-endian radix word. -/
def radixWordSection (b : ℕ) (f : ℕ → K) (w : List (Fin b)) : ℕ → K :=
  fun n ↦ f (b ^ w.length * n + Nat.ofDigits b (w.map Fin.val))

/-- The linear span of all padded word sections of a scalar sequence. -/
def RadixKernelSpan (b : ℕ) (f : ℕ → K) : Submodule K (ℕ → K) :=
  Submodule.span K (Set.range (radixWordSection b f))

/-- A scalar sequence is radix-regular when its module of radix word
sections is finitely generated. -/
def IsRadixRegular (b : ℕ) (f : ℕ → K) : Prop :=
  (RadixKernelSpan b f).FG

omit [CommRing K] in
@[simp] theorem radixWordSection_nil (b : ℕ) (f : ℕ → K) :
    radixWordSection b f [] = f := by
  funext n
  simp [radixWordSection]

omit [CommRing K] in
/-- Appending one high digit to a section is the same as taking the
corresponding digit child of its argument. -/
theorem radixWordSection_append_singleton
    (b : ℕ) (f : ℕ → K) (w : List (Fin b)) (r : Fin b) (n : ℕ) :
    radixWordSection b f (w ++ [r]) n =
    radixWordSection b f w (b * n + r.val) := by
  simp only [radixWordSection, List.length_append, List.length_singleton,
    List.map_append, List.map_cons, List.map_nil, List.length_map, Nat.ofDigits_append,
    Nat.ofDigits_singleton, pow_succ]
  congr 1
  ring

/-- Finite generation of the radix-kernel span supplies finitely many
actual word sections which reconstruct the original sequence and are closed
under every digit transition. -/
theorem radixRegular_exists_finite_word_model
    (b : ℕ) (f : ℕ → K) (hregular : IsRadixRegular b f) :
    ∃ (d : ℕ) (w : Fin d → List (Fin b)) (a : Fin d → K)
      (C : Fin b → Matrix (Fin d) (Fin d) K),
      (∀ n, f n = ∑ j, a j * radixWordSection b f (w j) n) ∧
      (∀ r i n, radixWordSection b f (w i) (b * n + r.val) =
        ∑ j, C r i j * radixWordSection b f (w j) n) := by
  classical
  obtain ⟨d, w, hwspan⟩ := finite_original_generators_of_fg_span_range
    (radixWordSection b f) hregular
  have hf : f ∈ Submodule.span K
      (Set.range fun i ↦ radixWordSection b f (w i)) := by
    rw [hwspan]
    apply Submodule.subset_span
    exact ⟨[], radixWordSection_nil b f⟩
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hf
  have hr : ∀ r i, radixWordSection b f (w i ++ [r]) ∈
      Submodule.span K (Set.range fun j ↦ radixWordSection b f (w j)) := by
    intro r i
    rw [hwspan]
    exact Submodule.subset_span ⟨w i ++ [r], rfl⟩
  have hc : ∀ r i, ∃ c : Fin d → K,
      ∑ j, c j • radixWordSection b f (w j) =
        radixWordSection b f (w i ++ [r]) := by
    intro r i
    exact (Submodule.mem_span_range_iff_exists_fun K).mp (hr r i)
  choose C hC using hc
  refine ⟨d, w, a, C, ?_, ?_⟩
  · intro n
    have h := congrFun ha n
    simpa using h.symm
  · intro r i n
    rw [← radixWordSection_append_singleton b f (w i) r n]
    have h := congrFun (hC r i) n
    simpa using h.symm

/-- Every radix-regular scalar sequence over a commutative ring admits a
finite matrix digit representation with a linear scalar output. No
representation or observability condition is supplied in advance. -/
theorem radixRegular_exists_matrix_representation
    (b : ℕ) (_hb : 2 ≤ b) (f : ℕ → K) (hregular : IsRadixRegular b f) :
    ∃ (d : ℕ) (M : Fin b → Matrix (Fin d) (Fin d) K)
      (u : ℕ → Fin d → K) (l : Module.Dual K (Fin d → K)),
      (∀ n (r : Fin b), u (b * n + r.val) = Matrix.mulVecLin (M r) (u n)) ∧
      (∀ n, l (u n) = f n) := by
  classical
  obtain ⟨d, w, a, C, hreconstruct, hclosed⟩ :=
    radixRegular_exists_finite_word_model b f hregular
  let u : ℕ → Fin d → K := fun n i ↦ radixWordSection b f (w i) n
  let l : Module.Dual K (Fin d → K) := ∑ i, a i • LinearMap.proj i
  refine ⟨d, C, u, l, ?_, ?_⟩
  · intro n r
    funext i
    simp only [u, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
    exact hclosed r i n
  · intro n
    rw [show l (u n) = ∑ i, a i * radixWordSection b f (w i) n by
      simp [l, u, smul_eq_mul]]
    exact (hreconstruct n).symm

end IndependentZeroBlocks
