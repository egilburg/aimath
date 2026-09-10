import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace FiniteMonoidMortality

def rankTriangle : ℕ → ℕ
  | 0 => 0
  | r + 1 => rankTriangle r + r + 1

theorem rankTriangle_twice (r : ℕ) : 2 * rankTriangle r = r * (r + 1) := by
  induction r with
  | zero => simp [rankTriangle]
  | succ r ih => simp only [rankTriangle]; nlinarith

theorem rankTriangle_eq (r : ℕ) : rankTriangle r = r * (r + 1) / 2 := by
  have := rankTriangle_twice r
  omega

theorem rankTriangle_mono : Monotone rankTriangle := by
  apply monotone_nat_of_le_succ
  intro r
  simp only [rankTriangle]
  omega

def mortalityBudget (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | d + 1 => 2 * mortalityBudget n d + (1 + rankTriangle n - rankTriangle (n - d))

theorem mortalityBudget_mono (n : ℕ) : Monotone (mortalityBudget n) := by
  apply monotone_nat_of_le_succ
  intro d
  simp only [mortalityBudget]
  omega

theorem mortalityBudget_identity (n d : ℕ) (hd : d ≤ n) :
    mortalityBudget n d + rankTriangle n + (n - d) =
      n * 2 ^ d + rankTriangle (n - d) := by
  induction d with
  | zero => simp [mortalityBudget, Nat.add_comm]
  | succ d ih =>
    have hi := ih (by omega)
    have ht := rankTriangle_mono (show n - d ≤ n by omega)
    have hs : n - d = (n - (d + 1)) + 1 := by omega
    have htri : rankTriangle (n - d) =
        rankTriangle (n - (d + 1)) + (n - (d + 1)) + 1 := by
      rw [hs, rankTriangle]
    have hsub : 1 + rankTriangle n - rankTriangle (n - d) +
        rankTriangle (n - d) = 1 + rankTriangle n := by omega
    simp only [mortalityBudget, pow_succ]
    nlinarith

theorem mortalityBudget_full (n : ℕ) :
    mortalityBudget n n = n * 2 ^ n - n * (n + 1) / 2 := by
  have hi := mortalityBudget_identity n n le_rfl
  simp only [Nat.sub_self, rankTriangle, Nat.add_zero] at hi
  rw [← rankTriangle_eq]
  omega

theorem mortalityBudget_comparison (n : ℕ) (hn : 2 ≤ n) :
    2 ^ (n - 1) + (2 ^ (n - 1) - 1) * (n * (n + 1) / 2) =
      mortalityBudget n n + 2 ^ (n - 2) * (n - 1) * (n - 2) := by
  have hp : 1 ≤ 2 ^ (n - 2) := Nat.one_le_pow _ _ (by omega)
  have hpow1 : 2 ^ (n - 1) = 2 ^ (n - 2) * 2 := by
    rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]
  have hpow2 : 2 ^ n = 2 ^ (n - 2) * 4 := by
    rw [show n = (n - 2) + 2 by omega, pow_add]
    norm_num
  have hb := mortalityBudget_identity n n le_rfl
  simp only [Nat.sub_self, rankTriangle, Nat.add_zero] at hb
  rw [hpow2] at hb
  have ht := rankTriangle_twice n
  have htm := congrArg (fun x : ℕ => 2 ^ (n - 2) * x) ht
  rw [← rankTriangle_eq, hpow1]
  have hs : 2 ^ (n - 2) * 2 - 1 + 1 = 2 ^ (n - 2) * 2 := by omega
  have hn1 : n - 1 + 1 = n := by omega
  have hn2 : n - 2 + 2 = n := by omega
  have hpoly : (n - 1) * (n - 2) + 4 * n = 2 * rankTriangle n + 2 := by
    nlinarith
  have hpm := congrArg (fun x : ℕ => 2 ^ (n - 2) * x) hpoly
  have hsm := congrArg (fun x : ℕ => x * rankTriangle n) hs
  nlinarith

end FiniteMonoidMortality
