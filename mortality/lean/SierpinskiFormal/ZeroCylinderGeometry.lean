import SierpinskiFormal.UniformRelativeHoles
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

/-!
# Uniform relative holes from radix zero cylinders

This file isolates the arithmetic behind missing-digit arguments.  If an
arbitrary predicate is false on one fixed child in every aligned radix block,
then its support has uniform relative holes.  No algebraic structure on the
values producing the predicate is needed.
-/

namespace IndependentZeroBlocks

/-- A fixed zero child in every aligned radix block gives uniform relative
holes.  The explicit witnesses are `c = B⁻³` and `L0 = B²`.

The cylinder indexed by `k` has length `B^k`, fixes the next radix digit to
`w`, and lies in the parent block indexed by `q`. -/
theorem hasUniformRelativeHoles_of_radix_zeroCylinder
    {bad : ℕ → Prop} (B w : ℕ) (hB : 2 ≤ B) (hw : w < B)
    (hcylinder : ∀ k q j : ℕ, j < B ^ k →
      ¬bad (B ^ (k + 1) * q + B ^ k * w + j)) :
    HasUniformRelativeHoles bad := by
  refine ⟨1 / (B : ℝ) ^ 3, by positivity, B ^ 2, ?_⟩
  intro a L hL
  have hLpos : L ≠ 0 := by
    have : 0 < B ^ 2 := by positivity
    omega
  let t := Nat.log B L
  have ht2 : 2 ≤ t := by
    apply Nat.le_log_of_pow_le (by omega)
    simpa [t] using hL
  let k := t - 2
  have htk : t = k + 2 := by
    dsimp [k]
    omega
  let M := B ^ k
  let parent := B ^ (k + 1)
  let q := a / parent + 1
  let p := parent * q
  let n := p + w * M
  have hMpos : 0 < M := by positivity
  have hparentpos : 0 < parent := by positivity
  have hpowLower : B ^ (k + 2) ≤ L := by
    rw [← htk]
    simpa [t] using Nat.pow_log_le_self B hLpos
  have htwoParent : 2 * parent ≤ L := by
    calc
      2 * parent ≤ B * parent := Nat.mul_le_mul_right parent hB
      _ = B ^ (k + 2) := by
        simp [parent, pow_succ, Nat.mul_comm]
      _ ≤ L := hpowLower
  have hap : a ≤ p := by
    have h := (Nat.lt_mul_div_succ a hparentpos).le
    simpa [p, q] using h
  have hpaParent : p ≤ a + parent := by
    calc
      p = a / parent * parent + parent := by
        simp [p, q]
        ring
      _ ≤ a + parent :=
        Nat.add_le_add_right (Nat.div_mul_le_self a parent) parent
  have hchild : w * M + M ≤ parent := by
    calc
      w * M + M = (w + 1) * M := by ring
      _ ≤ B * M :=
        Nat.mul_le_mul_right M (Nat.succ_le_iff.mpr hw)
      _ = parent := by
        simp [parent, M, pow_succ, Nat.mul_comm]
  have hnstart : a ≤ n := hap.trans (Nat.le_add_right p (w * M))
  have hnend : n + M ≤ a + L := by
    calc
      n + M = p + (w * M + M) := by simp [n]; ring
      _ ≤ p + parent := Nat.add_le_add_left hchild p
      _ ≤ a + parent + parent := Nat.add_le_add_right hpaParent parent
      _ = a + 2 * parent := by ring
      _ ≤ a + L := Nat.add_le_add_left htwoParent a
  have hpowUpper : L ≤ B ^ 3 * M := by
    have hlt := Nat.lt_pow_succ_log_self (by omega : 1 < B) L
    have htSucc : t + 1 = k + 3 := by omega
    have hlt' : L < B ^ (k + 3) := by
      simpa [t, htSucc] using hlt
    have hlt'' : L < B ^ 3 * M := by
      simpa [M, pow_add, Nat.mul_comm] using hlt'
    exact Nat.le_of_lt hlt''
  have hrelative :
      (1 / (B : ℝ) ^ 3) * (L : ℝ) ≤ (M : ℝ) := by
    rw [one_div_mul_eq_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (B : ℝ) ^ 3)).2
    have hpowUpper' : L ≤ M * B ^ 3 := by
      simpa [Nat.mul_comm] using hpowUpper
    exact_mod_cast hpowUpper'
  refine ⟨n, M, hnstart, hnend, hrelative, ?_⟩
  intro j hj
  simpa [n, p, parent, M, add_assoc, Nat.mul_comm] using
    hcylinder k q j hj

end IndependentZeroBlocks

#print axioms IndependentZeroBlocks.hasUniformRelativeHoles_of_radix_zeroCylinder
