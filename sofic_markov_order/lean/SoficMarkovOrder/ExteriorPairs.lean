import SoficMarkovOrder.ExteriorRank
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module

set_option autoImplicit false

namespace SoficMarkovOrder

open exteriorPower
open scoped Matrix

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def wedgePair (x y : V) : ⋀[K]^2 V := exteriorPower.ιMulti K 2 ![x, y]

theorem wedgePair_add_left (x y z : V) :
    wedgePair (K := K) (x + y) z = wedgePair (K := K) x z + wedgePair (K := K) y z := by
  exact (exteriorPower.ιMulti K 2).map_vecCons_add ![z] x y

theorem wedgePair_smul_left (c : K) (x y : V) :
    wedgePair (K := K) (c • x) y = c • wedgePair (K := K) x y := by
  exact (exteriorPower.ιMulti K 2).map_vecCons_smul ![y] c x

theorem wedgePair_swap (x y : V) : wedgePair (K := K) y x = -wedgePair (K := K) x y := by
  have h := (exteriorPower.ιMulti K 2).map_swap ![x,y] (by decide : (0 : Fin 2) ≠ 1)
  have he : (![x,y] ∘ Equiv.swap 0 1) = ![y,x] := by
    ext i
    fin_cases i <;> simp
  rw [he] at h
  exact h

theorem wedgePair_add_right (x y z : V) :
    wedgePair (K := K) x (y + z) = wedgePair (K := K) x y + wedgePair (K := K) x z := by
  rw [wedgePair_swap (y + z) x, wedgePair_add_left, neg_add,
    wedgePair_swap x y, wedgePair_swap x z, neg_neg, neg_neg]

theorem wedgePair_smul_right (c : K) (x y : V) :
    wedgePair (K := K) x (c • y) = c • wedgePair (K := K) x y := by
  rw [wedgePair_swap (c • y) x, wedgePair_smul_left, wedgePair_swap x y, smul_neg, neg_neg]

@[simp] theorem wedgePair_self (x : V) : wedgePair (K := K) x x = 0 :=
  (exteriorPower.ιMulti K 2).map_eq_zero_of_eq ![x,x]
    (by rfl : (![x,x] : Fin 2 → V) 0 = ![x,x] 1) (by decide : (0 : Fin 2) ≠ 1)

theorem wedgePair_linear_combination (a b c d : K) (x y : V) :
    wedgePair (K := K) (a • x + b • y) (c • x + d • y) =
      (a * d - b * c) • wedgePair (K := K) x y := by
  rw [wedgePair_add_left, wedgePair_add_right, wedgePair_add_right]
  simp only [wedgePair_smul_left, wedgePair_smul_right, wedgePair_self, smul_zero,
    zero_add, add_zero]
  rw [wedgePair_swap x y, smul_neg, smul_neg]
  module

def twoVectorMap (x y : V) (α β : Module.Dual K V) : Module.End K V :=
  α.smulRight x + β.smulRight y

noncomputable def pairFunctional (α β : Module.Dual K V) : Module.Dual K (⋀[K]^2 V) :=
  exteriorPower.alternatingMapToDual K V 2 ![α, β]

theorem pairFunctional_wedgePair (α β : Module.Dual K V) (x y : V) :
    pairFunctional α β (wedgePair (K := K) x y) = α x * β y - β x * α y := by
  simp [pairFunctional, wedgePair, Matrix.det_fin_two]

/-- A two-coordinate partial map induces a single rank-one exterior operator. -/
theorem exterior_twoVectorMap (x y : V) (α β : Module.Dual K V) :
    exteriorPower.map 2 (twoVectorMap x y α β) =
      (pairFunctional α β).smulRight (wedgePair (K := K) x y) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
  rw [hv]
  simp only [LinearMap.compAlternatingMap_apply, exteriorPower.map_apply_ιMulti,
    LinearMap.smulRight_apply]
  change wedgePair (K := K) (α (v 0) • x + β (v 0) • y)
    (α (v 1) • x + β (v 1) • y) =
      pairFunctional α β (wedgePair (K := K) (v 0) (v 1)) • wedgePair (K := K) x y
  rw [wedgePair_linear_combination, pairFunctional_wedgePair]

noncomputable def pairTransition {I : Type*} [LinearOrder I] (b : Module.Basis I K V)
    (s t : Set.powersetCard I 2) : Module.End K V :=
  twoVectorMap (b (Set.powersetCard.ofFinEmbEquiv.symm s 0))
    (b (Set.powersetCard.ofFinEmbEquiv.symm s 1))
    (b.coord (Set.powersetCard.ofFinEmbEquiv.symm t 0))
    (b.coord (Set.powersetCard.ofFinEmbEquiv.symm t 1))

/-- The pair-chain maps are exactly matrix units in the exterior basis. -/
theorem exterior_pairTransition {I : Type*} [LinearOrder I] (b : Module.Basis I K V)
    (s t : Set.powersetCard I 2) :
    exteriorPower.map 2 (pairTransition b s t) =
      ((b.exteriorPower 2).coord t).smulRight ((b.exteriorPower 2) s) := by
  rw [pairTransition, exterior_twoVectorMap, exteriorPower.basis_coord,
    exteriorPower.basis_apply]
  congr 1
  · simp only [exteriorPower.ιMultiDual, exteriorPower.ιMulti_family,
      exteriorPower.pairingDual, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
      pairFunctional]
    congr 1
    ext i
    fin_cases i <;> rfl
end SoficMarkovOrder
