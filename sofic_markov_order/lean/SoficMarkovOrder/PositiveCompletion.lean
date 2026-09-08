import SoficMarkovOrder.PairChain
import SoficMarkovOrder.StationaryWordLaw
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Tactic.Positivity

set_option autoImplicit false
noncomputable section

namespace SoficMarkovOrder
open scoped BigOperators

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

def entryMap (i j : Q) : Module.End ℝ (Q → ℝ) :=
  (LinearMap.proj j).smulRight (Pi.single i 1)

@[simp] theorem entryMap_apply (i j : Q) (x : Q → ℝ) (k : Q) :
    entryMap i j x k = x j * (if k = i then 1 else 0) := by
  simp [entryMap, Pi.single_apply, eq_comm]

def averageRow : Module.Dual ℝ (Q → ℝ) :=
  (Fintype.card Q : ℝ)⁻¹ • ∑ i : Q, LinearMap.proj i

@[simp] theorem averageRow_apply (x : Q → ℝ) :
    averageRow x = (Fintype.card Q : ℝ)⁻¹ * ∑ i, x i := by
  simp [averageRow, LinearMap.sum_apply]

def uniformMean : Module.End ℝ (Q → ℝ) := LinearMap.pi fun _ => averageRow

@[simp] theorem uniformMean_apply (x : Q → ℝ) (i : Q) :
    uniformMean x i = averageRow x := rfl

def endEntry (f : Module.End ℝ (Q → ℝ)) (i j : Q) : ℝ := f (Pi.single j 1) i

theorem end_eq_sum_entryMap (f : Module.End ℝ (Q → ℝ)) :
    (∑ i : Q, ∑ j : Q, endEntry f i j • entryMap i j) = f := by
  apply LinearMap.ext
  intro x
  funext k
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, entryMap_apply]
  rw [Finset.sum_comm]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hx : (∑ j : Q, x j • Pi.single j (1 : ℝ)) = x := by
    simpa only [Pi.basisFun_repr, Pi.basisFun_apply] using (Pi.basisFun ℝ Q).sum_repr x
  conv_rhs => rw [← hx]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, endEntry]
  apply Finset.sum_congr rfl
  intro j _
  ring

@[simp] theorem endEntry_uniformMean (i j : Q) :
    endEntry (uniformMean (Q := Q)) i j = (Fintype.card Q : ℝ)⁻¹ := by
  simp [endEntry, averageRow_apply]

theorem averageRow_ones [Nonempty Q] : averageRow (fun _ : Q => 1) = 1 := by
  simp [averageRow_apply, Fintype.card_ne_zero]

theorem uniformMean_ones [Nonempty Q] : uniformMean (fun _ : Q => 1) = (fun _ => 1) := by
  ext i
  exact averageRow_ones

theorem averageRow_uniformMean [Nonempty Q] (x : Q → ℝ) :
    averageRow (uniformMean x) = averageRow x := by
  simp only [averageRow_apply, uniformMean_apply, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), one_mul]

section Chain
variable [LinearOrder Q] {D : ℕ}

theorem pairTransition_pi_apply (s t : Set.powersetCard Q 2) (x : Q → ℝ) (i : Q) :
    pairTransition (Pi.basisFun ℝ Q) s t x i =
      x (Set.powersetCard.ofFinEmbEquiv.symm t 0) *
        (if i = Set.powersetCard.ofFinEmbEquiv.symm s 0 then 1 else 0) +
      x (Set.powersetCard.ofFinEmbEquiv.symm t 1) *
        (if i = Set.powersetCard.ofFinEmbEquiv.symm s 1 then 1 else 0) := by
  simp [pairTransition, twoVectorMap, Module.Basis.coord_apply, Pi.basisFun_repr,
    Pi.basisFun_apply, Pi.single_apply, eq_comm]

theorem pairTransition_nonneg (s t : Set.powersetCard Q 2) (x : Q → ℝ)
    (hx : ∀ i, 0 ≤ x i) (i : Q) :
    0 ≤ pairTransition (Pi.basisFun ℝ Q) s t x i := by
  rw [pairTransition_pi_apply]
  apply add_nonneg <;> apply mul_nonneg
  · exact hx _
  · split_ifs <;> norm_num
  · exact hx _
  · split_ifs <;> norm_num

theorem endEntry_pairTransition_le_one (s t : Set.powersetCard Q 2) (i j : Q) :
    endEntry (pairTransition (Pi.basisFun ℝ Q) s t) i j ≤ 1 := by
  have hne : Set.powersetCard.ofFinEmbEquiv.symm s 0 ≠
      Set.powersetCard.ofFinEmbEquiv.symm s 1 :=
    (Set.powersetCard.ofFinEmbEquiv.symm s).injective.ne (by decide)
  simp only [endEntry, pairTransition_pi_apply, Pi.single_apply]
  split_ifs <;> simp_all

variable [Nonempty Q]

def completionEpsilon (D : ℕ) : ℝ := 1 / (2 * Fintype.card Q * D)

theorem completionEpsilon_pos (hD : 0 < D) : 0 < completionEpsilon (Q := Q) D := by
  unfold completionEpsilon
  have hQ : 0 < Fintype.card Q := Fintype.card_pos
  positivity

def completionResidual (e : Fin D ≃ Set.powersetCard Q 2) : Module.End ℝ (Q → ℝ) :=
  uniformMean - completionEpsilon (Q := Q) D •
    ∑ s : Fin (D - 1), pairChain (Pi.basisFun ℝ Q) e s

theorem completionResidual_entry_pos (e : Fin D ≃ Set.powersetCard Q 2)
    (hD : 0 < D) (i j : Q) : 0 < endEntry (completionResidual e) i j := by
  have hQ : 0 < (Fintype.card Q : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hDreal : 0 < (D : ℝ) := Nat.cast_pos.mpr hD
  have hsum : (∑ s : Fin (D - 1),
      endEntry (pairChain (Pi.basisFun ℝ Q) e s) i j) ≤ (D - 1 : ℕ) := by
    calc
      _ ≤ ∑ _s : Fin (D - 1), (1 : ℝ) := Finset.sum_le_sum fun s _ =>
        endEntry_pairTransition_le_one _ _ i j
      _ = _ := by simp
  have hc := completionEpsilon_pos (Q := Q) hD
  have hbound := mul_le_mul_of_nonneg_left hsum hc.le
  have hsmall : completionEpsilon (Q := Q) D * (D - 1 : ℕ) <
      (Fintype.card Q : ℝ)⁻¹ := by
    unfold completionEpsilon
    have hcast : ((D - 1 : ℕ) : ℝ) = (D : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    rw [hcast]
    field_simp
    nlinarith
  simp only [completionResidual, endEntry, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  rw [show uniformMean (Pi.single j (1 : ℝ)) i = (Fintype.card Q : ℝ)⁻¹ from
    endEntry_uniformMean i j]
  change (Fintype.card Q : ℝ)⁻¹ - completionEpsilon (Q := Q) D *
    (∑ s : Fin (D - 1), endEntry (pairChain (Pi.basisFun ℝ Q) e s) i j) > 0
  linarith

end Chain
end SoficMarkovOrder
