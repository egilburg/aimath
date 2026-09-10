import SierpinskiFormal.DigitState
import SierpinskiFormal.Convolution
import SierpinskiFormal.ZeroBlocks

/-!
# The assembled modular convolution theorem

The hypotheses below are scalar Lucas identities and concrete digit sums. The
prefix-state recurrence is derived from those identities in `Convolution`.
The conclusion has the original unbounded block quantifiers. This is a proved
conditional modular component, not the full rational-generating-function theorem.
-/

namespace SierpinskiFormal

open scoped BigOperators

def prefixState {K : Type*} [CommRing K] (v : ℕ → K) (n : ℕ) : K × K :=
  (∑ j ∈ Finset.range (n + 1), v j, v n)

theorem prefixState_transition {K : Type*} [CommRing K]
    (v : ℕ → K) (q : ℕ) (hq : (q : K) = 0)
    (hlucas : ∀ m d, d < q → v (q * m + d) = v m * v d)
    (m d : ℕ) (hd : d < q) :
    prefixState v (q * m + d) =
      DigitState.transition (∑ j ∈ Finset.range q, v j)
        (∑ j ∈ Finset.range (d + 1), v j) (v d) (prefixState v m) := by
  apply Prod.ext
  · exact Convolution.prefix_digit v q m d hq hd hlucas
  · simp only [prefixState, DigitState.transition, Prod.snd]
    rw [hlucas m d hd, mul_comm]

/-- Preserve the actual common seed and its complete descendant intervals.
Unlike a separate existence statement for each convolution, this can be used
to combine any finite number of pole contributions on the same intervals. -/
theorem weighted_zero_on_seed_descendants
    {K : Type*} [CommRing K] (q seed : ℕ) (hq : 2 ≤ q)
    (hqzero : (q : K) = 0) (v : ℕ → K) (P : Polynomial K)
    (hlucas : ∀ m d, d < q → v (q * m + d) = v m * v d)
    (hseed : prefixState v seed = (0, 0)) :
    ∀ E, 1 ≤ E → ∀ j, j < q ^ E →
      Convolution.weighted P v (seed * q ^ E + j) = 0 := by
  apply zero_on_positive_depth_descendants_of_parent
    (Z := fun n => prefixState v n = (0, 0)) hq hseed
  · intro n d hd hn
    rw [prefixState_transition v q hqzero hlucas n d hd, hn,
      DigitState.transition_zero]
  · intro n d hd hn
    have hv : v n = 0 := congrArg Prod.snd hn
    have hf : (∑ j ∈ Finset.range (n + 1), v j) = 0 := congrArg Prod.fst hn
    exact Convolution.weighted_zero_of_state P v q n d hqzero hd hlucas hv hf

/-- A single digit word gives arbitrarily long zero blocks for a polynomially
weighted Lucas convolution. All arithmetic and state hypotheses are explicit.
The field characteristic p and the digit base q are deliberately separate. -/
theorem weighted_zeroBlocks_of_lucas
    {K : Type*} [Field K] (p q d e : ℕ) [CharP K p]
    (hp : 0 < p) (hq : 2 ≤ q) (hqzero : (q : K) = 0)
    (v : ℕ → K) (P : Polynomial K)
    (hv0 : v 0 = 1)
    (hlucas : ∀ m a, a < q → v (q * m + a) = v m * v a)
    (hd : d < q) (he : e < q) (hepos : 0 < e)
    (hH : (∑ j ∈ Finset.range q, v j) = 0 ∨
      (∑ j ∈ Finset.range q, v j) = 1)
    (hpow : (∑ j ∈ Finset.range q, v j) = 1 → v d ^ (q - 1) = 1)
    (hlow : (∑ j ∈ Finset.range (d + 1), v j) = 1 + v d)
    (hhigh : (∑ j ∈ Finset.range (e + 1), v j) =
      ∑ j ∈ Finset.range q, v j)
    (hve : v e = 0) :
    HasArbitrarilyLongZeroBlocks (Convolution.weighted P v) := by
  let H := ∑ j ∈ Finset.range q, v j
  let F := fun a => ∑ j ∈ Finset.range (a + 1), v j
  let state := prefixState v
  let seed := q * DigitState.lowIndex q d (DigitState.extensionLength p q) + e
  have hrec : ∀ m a, a < q →
      state (q * m + a) = DigitState.transition H (F a) (v a) (state m) := by
    intro m a ha
    exact prefixState_transition v q hqzero hlucas m a ha
  have hs0 : state 0 = (1, 1) := by simp [state, prefixState, hv0]
  have hseed : state seed = (0, 0) :=
    DigitState.sequence_extension_seed p q d e hp (by omega) H (v d) F v state
      hd he hs0 hrec hH hpow hlow rfl hhigh hve
  have hseedpos : 1 ≤ seed := by dsimp [seed]; omega
  apply hasArbitrarilyLongZeroBlocks_of_parent (Z := fun n => state n = (0, 0))
    hq hseedpos hseed
  · intro n a ha hn
    rw [hrec n a ha, hn, DigitState.transition_zero]
  · intro n a ha hn
    have hv : v n = 0 := congrArg Prod.snd hn
    have hf : (∑ j ∈ Finset.range (n + 1), v j) = 0 := congrArg Prod.fst hn
    exact Convolution.weighted_zero_of_state P v q n a hqzero ha hlucas hv hf

end SierpinskiFormal

#print axioms SierpinskiFormal.weighted_zeroBlocks_of_lucas
