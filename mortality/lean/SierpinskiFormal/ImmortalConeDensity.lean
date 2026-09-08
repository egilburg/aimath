import SierpinskiFormal.PorousSupportBounds
import SierpinskiFormal.SupportDensityBounds
import SierpinskiFormal.FiniteExceptionalGaps

set_option autoImplicit false

namespace IndependentZeroBlocks

open Filter
open scoped Topology

/-- An explicit positive eventual lower density for an arbitrary predicate. -/
def HasPositiveLowerPredicateDensity (bad : ℕ → Prop) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    c * (N : ℝ) ≤ (predicateCount bad N : ℝ)

/-- Predicate counts are monotone in their cutoff. -/
theorem predicateCount_mono (bad : ℕ → Prop) {M N : ℕ} (hMN : M ≤ N) :
    predicateCount bad M ≤ predicateCount bad N := by
  classical
  unfold predicateCount
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
  exact ⟨hn.1.trans_le hMN, hn.2⟩

/-- A full radix cone contributes its entire width below the cone endpoint. -/
theorem radixCone_pow_le_predicateCount
    (bad : ℕ → Prop) (b nstar k : ℕ)
    (hcone : ∀ j : ℕ, j < b ^ k → bad (b ^ k * nstar + j)) :
    b ^ k ≤ predicateCount bad (b ^ k * (nstar + 1)) := by
  have hlocal : intervalPredicateCount bad (b ^ k * nstar) (b ^ k) = b ^ k := by
    classical
    unfold intervalPredicateCount
    rw [show (Finset.range (b ^ k)).filter
        (fun j => bad (b ^ k * nstar + j)) = Finset.range (b ^ k) by
      apply Finset.filter_eq_self.mpr
      intro j hj
      exact hcone j (Finset.mem_range.mp hj)]
    simp
  have hglobal := intervalPredicateCount_le_predicateCount
    bad (b ^ k * nstar) (b ^ k)
  rw [hlocal] at hglobal
  simpa [Nat.mul_add] using hglobal

/-- A predicate containing all descendants of one radix state has positive
lower density.  The explicit constant is `1 / (b * (nstar + 1))`. -/
theorem positiveLowerPredicateDensity_of_full_radixCone
    (bad : ℕ → Prop) (b : ℕ) (hb : 2 ≤ b) (nstar : ℕ)
    (hcone : ∀ k j : ℕ, j < b ^ k → bad (b ^ k * nstar + j)) :
    HasPositiveLowerPredicateDensity bad := by
  let d := nstar + 1
  let c : ℝ := 1 / ((b * d : ℕ) : ℝ)
  have hd : 0 < d := by dsimp [d]; omega
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, d, ?_⟩
  intro N hN
  let x := N / d
  have hx : 0 < x := by
    dsimp [x]
    exact Nat.div_pos hN hd
  let k := Nat.log b x
  have hpowx : b ^ k ≤ x := by
    dsimp [k]
    exact Nat.pow_log_le_self b (Nat.ne_of_gt hx)
  have hendpoint : b ^ k * d ≤ N := by
    apply (Nat.le_div_iff_mul_le hd).mp
    simpa [x] using hpowx
  have hcount : b ^ k ≤ predicateCount bad N :=
    (radixCone_pow_le_predicateCount bad b nstar k (hcone k)).trans
      (predicateCount_mono bad (by simpa [d] using hendpoint))
  have hxnext : x < b ^ (k + 1) := by
    dsimp [k]
    simpa [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self (by omega) x
  have hNdiv : N < (x + 1) * d := by
    exact (Nat.div_lt_iff_lt_mul hd).mp (by simpa [x] using Nat.lt_succ_self x)
  have hNupper : N ≤ b * b ^ k * d := by
    have hxle : x + 1 ≤ b ^ (k + 1) := Nat.succ_le_iff.mpr hxnext
    calc
      N ≤ (x + 1) * d := hNdiv.le
      _ ≤ b ^ (k + 1) * d := Nat.mul_le_mul_right d hxle
      _ = b * b ^ k * d := by rw [pow_succ]; ring
  have hreal : c * (N : ℝ) ≤ (b ^ k : ℕ) := by
    dsimp [c, d] at ⊢
    have hden : (0 : ℝ) < ((b * (nstar + 1) : ℕ) : ℝ) := by positivity
    rw [one_div, inv_mul_eq_div]
    apply (div_le_iff₀ hden).mpr
    calc
      (N : ℝ) ≤ ((b * b ^ k * (nstar + 1) : ℕ) : ℝ) := by
        exact_mod_cast hNupper
      _ = (b ^ k : ℕ) * ((b * (nstar + 1) : ℕ) : ℝ) := by
        push_cast
        ring
  exact hreal.trans (by exact_mod_cast hcount)

/-- Positive lower predicate density is incompatible with density zero. -/
theorem HasPositiveLowerPredicateDensity.not_zeroDensity
    {bad : ℕ → Prop} (h : HasPositiveLowerPredicateDensity bad) :
    ¬HasZeroPredicateDensity bad := by
  obtain ⟨c, hc, N₀, hN₀⟩ := h
  intro hz
  have he : ∀ᶠ N : ℕ in atTop,
      (predicateCount bad N : ℝ) / (N : ℝ) < c :=
    hz.eventually (gt_mem_nhds hc)
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 he
  let N := max (max N₀ N₁) 1
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 0 < N by dsimp [N]; omega)
  have hlow := hN₀ N (by dsimp [N]; omega)
  have hhigh := hN₁ N (by dsimp [N]; omega)
  have hlow' : c ≤ (predicateCount bad N : ℝ) / (N : ℝ) :=
    (le_div_iff₀ hNpos).mpr hlow
  linarith

/-- Positive lower predicate density excludes uniform relative holes. -/
theorem HasPositiveLowerPredicateDensity.not_uniformRelativeHoles
    {bad : ℕ → Prop} (h : HasPositiveLowerPredicateDensity bad) :
    ¬HasUniformRelativeHoles bad := by
  intro hholes
  exact h.not_zeroDensity hholes.toZeroPredicateDensity

/-- Density zero forbids an immortal full cone rooted at any fixed radix
state. -/
theorem HasZeroPredicateDensity.not_full_radixCone
    {bad : ℕ → Prop} (hz : HasZeroPredicateDensity bad)
    (b : ℕ) (hb : 2 ≤ b) (nstar : ℕ) :
    ¬(∀ k j : ℕ, j < b ^ k → bad (b ^ k * nstar + j)) := by
  intro hcone
  exact (positiveLowerPredicateDensity_of_full_radixCone
    bad b hb nstar hcone).not_zeroDensity hz

/-- Density zero gives a missing descendant at some depth from every radix
state. -/
theorem HasZeroPredicateDensity.exists_missing_radixDescendant
    {bad : ℕ → Prop} (hz : HasZeroPredicateDensity bad)
    (b : ℕ) (hb : 2 ≤ b) (nstar : ℕ) :
    ∃ k j : ℕ, j < b ^ k ∧ ¬bad (b ^ k * nstar + j) := by
  by_contra hnone
  push_neg at hnone
  exact hz.not_full_radixCone b hb nstar hnone

/-- Predicate and series positive-lower-density formulations coincide on a
coefficient support. -/
theorem positiveLowerPredicateDensity_support_iff
    {K : Type*} [Semiring K] (F : PowerSeries K) :
    HasPositiveLowerPredicateDensity
      (fun n => PowerSeries.coeff n F ≠ 0) ↔
      HasPositiveLowerSupportDensity F := by
  classical
  have heq (N : ℕ) :
      predicateCount (fun n => PowerSeries.coeff n F ≠ 0) N =
        supportCount F N := by
    unfold predicateCount supportCount
    congr
  simp only [HasPositiveLowerPredicateDensity,
    HasPositiveLowerSupportDensity, heq]

/-- A full cone in coefficient support forces positive lower support density. -/
theorem positiveLowerSupportDensity_of_full_radixCone
    {K : Type*} [Semiring K] (F : PowerSeries K)
    (b : ℕ) (hb : 2 ≤ b) (nstar : ℕ)
    (hcone : ∀ k j : ℕ, j < b ^ k →
      PowerSeries.coeff (b ^ k * nstar + j) F ≠ 0) :
    HasPositiveLowerSupportDensity F := by
  exact (positiveLowerPredicateDensity_support_iff F).mp
    (positiveLowerPredicateDensity_of_full_radixCone _ b hb nstar hcone)

end IndependentZeroBlocks
