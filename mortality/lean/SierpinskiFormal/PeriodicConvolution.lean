import SierpinskiFormal.Assembly
import SierpinskiFormal.SeedBlocks
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Nat.Periodic
import Mathlib.RingTheory.PowerSeries.WellKnown

set_option autoImplicit false

/-!
# Periodically weighted Lucas convolutions

In positive characteristic, the binomial coefficient sequence belonging to a
repeated pole is periodic with a sufficiently large prime-power period.  This
file proves the block calculation for an arbitrary periodic weight, and then
supplies that binomial coefficient sequence as an instance.
-/

namespace SierpinskiFormal.PeriodicConvolution

open scoped BigOperators

variable {K : Type*} [CommRing K]

/-- A convolution whose coefficient at distance `r` is the periodic weight
`w r`. -/
def weighted (w v : ℕ → K) (n : ℕ) : K :=
  ∑ j ∈ Finset.range (n + 1), w (n - j) * v j

/-- Contribution of one complete base-`q` block.  The extra `q` in the
argument of `w` makes the formula uniform on both sides of the borrow at
`d = e`. -/
def fullWeight (w v : ℕ → K) (q e : ℕ) : K :=
  ∑ d ∈ Finset.range q, w (q + e - d) * v d

/-- Contribution of the final partial block. -/
def partialWeight (w v : ℕ → K) (e : ℕ) : K :=
  ∑ d ∈ Finset.range (e + 1), w (e - d) * v d

omit [CommRing K] in
/-- Every multiple of a period is again a period. -/
theorem periodic_of_dvd {w : ℕ → K} {H q : ℕ}
    (hw : Function.Periodic w H) (hHq : H ∣ q) :
    Function.Periodic w q := by
  obtain ⟨a, rfl⟩ := hHq
  simpa [Nat.mul_comm] using hw.nsmul a

omit [CommRing K] in
/-- On every complete block, a `q`-periodic coefficient only sees the low
digit of the distance. -/
private theorem weight_eq_low (w : ℕ → K) (q M e m d : ℕ)
    (hw : Function.Periodic w q) (hm : m < M) (hd : d < q) :
    w ((q * M + e) - (q * m + d)) = w (q + e - d) := by
  have hmle : m ≤ M := Nat.le_of_lt hm
  have hM : m + (M - m) = M := Nat.add_sub_of_le hmle
  have hdiff : M - m = (M - m - 1) + 1 := by omega
  have hdle : d ≤ q + e := by omega
  have hqM : q * m + q * (M - m) = q * M := by
    rw [← Nat.mul_add, hM]
  have hmul : q * (M - m) + e = (M - m - 1) * q + (q + e) := by
    calc
      q * (M - m) + e = q * ((M - m - 1) + 1) + e :=
        congrArg (fun x => q * x + e) hdiff
      _ = (M - m - 1) * q + (q + e) := by ring
  have harith :
      (q * M + e) - (q * m + d) =
        (q + e - d) + (M - m - 1) * q := by
    calc
      (q * M + e) - (q * m + d) =
          (q * m + (q * (M - m) + e)) - (q * m + d) := by
            rw [← hqM, Nat.add_assoc]
      _ = q * (M - m) + e - d := Nat.add_sub_add_left _ _ _
      _ = ((M - m - 1) * q + (q + e)) - d := by
            rw [hmul]
      _ = (M - m - 1) * q + (q + e - d) :=
            Nat.add_sub_assoc hdle _
      _ = (q + e - d) + (M - m - 1) * q := Nat.add_comm _ _
  rw [harith]
  simpa [Nat.nsmul_eq_mul] using hw.nsmul (M - m - 1) (q + e - d)

/-- Split a periodically weighted convolution into complete Lucas blocks and
the final partial block. -/
theorem weighted_block (w v : ℕ → K) (q M e : ℕ)
    (he : e < q) (hw : Function.Periodic w q)
    (hlucas : ∀ m d, d < q → v (q * m + d) = v m * v d) :
    weighted w v (q * M + e) =
      fullWeight w v q e * (∑ m ∈ Finset.range M, v m) +
        partialWeight w v e * v M := by
  unfold weighted
  rw [Convolution.sum_range_blocks_partial]
  congr 1
  · calc
      (∑ m ∈ Finset.range M, ∑ d ∈ Finset.range q,
          w ((q * M + e) - (q * m + d)) * v (q * m + d)) =
          ∑ m ∈ Finset.range M, fullWeight w v q e * v m := by
        apply Finset.sum_congr rfl
        intro m hm
        unfold fullWeight
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro d hd
        rw [weight_eq_low w q M e m d hw (Finset.mem_range.mp hm)
          (Finset.mem_range.mp hd), hlucas m d (Finset.mem_range.mp hd)]
        ring
      _ = fullWeight w v q e * ∑ m ∈ Finset.range M, v m := by
        rw [Finset.mul_sum]
  · unfold partialWeight
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    have hdle : d ≤ e := Nat.le_of_lt_succ (Finset.mem_range.mp hd)
    have hdq : d < q := lt_of_le_of_lt hdle he
    rw [hlucas M d hdq]
    rw [Nat.add_sub_add_left]
    ring

/-- Vanishing of the coefficient and of its inclusive prefix sum kills every
periodic coefficient weight. -/
theorem weighted_zero_of_state (w v : ℕ → K) (q M e : ℕ)
    (he : e < q) (hw : Function.Periodic w q)
    (hlucas : ∀ m d, d < q → v (q * m + d) = v m * v d)
    (hv : v M = 0) (hf : (∑ m ∈ Finset.range (M + 1), v m) = 0) :
    weighted w v (q * M + e) = 0 := by
  have hpref : (∑ m ∈ Finset.range M, v m) = 0 := by
    simpa [Finset.sum_range_succ, hv] using hf
  rw [weighted_block w v q M e he hw hlucas, hpref, hv]
  simp

/-- A Lucas rule in base `q` iterates to the grouped base `q^e`. -/
theorem lucas_pow (v : ℕ → K) (q : ℕ) (hq : 1 ≤ q) (hv0 : v 0 = 1)
    (hlucas : ∀ m d, d < q → v (q * m + d) = v m * v d) :
    ∀ e m d, d < q ^ e → v (q ^ e * m + d) = v m * v d := by
  intro e
  induction e with
  | zero =>
      intro m d hd
      have hd0 : d = 0 := by simpa using hd
      subst d
      simp [hv0]
  | succ e ih =>
      intro m d hd
      have hQ : 0 < q ^ e := pow_pos (by omega) e
      have ha : d / q ^ e < q := by
        apply (Nat.div_lt_iff_lt_mul hQ).2
        rw [Nat.mul_comm, ← pow_succ]
        exact hd
      have hb : d % q ^ e < q ^ e := Nat.mod_lt d hQ
      have hddecomp : q ^ e * (d / q ^ e) + d % q ^ e = d := by
        exact Nat.div_add_mod d (q ^ e)
      have hn :
          q ^ (e + 1) * m + d =
            q ^ e * (q * m + d / q ^ e) + d % q ^ e := by
        calc
          q ^ (e + 1) * m + d = q ^ e * q * m + d := by rw [pow_succ]
          _ = q ^ e * (q * m) + d := by ring
          _ = q ^ e * (q * m) +
              (q ^ e * (d / q ^ e) + d % q ^ e) :=
                congrArg (fun x => q ^ e * (q * m) + x) hddecomp.symm
          _ = q ^ e * (q * m + d / q ^ e) + d % q ^ e := by ring
      rw [hn, ih (q * m + d / q ^ e) (d % q ^ e) hb,
        hlucas m (d / q ^ e) ha]
      have hvd := ih (d / q ^ e) (d % q ^ e) hb
      calc
        v m * v (d / q ^ e) * v (d % q ^ e) =
            v m * (v (d / q ^ e) * v (d % q ^ e)) := by ring
        _ = v m * v (q ^ e * (d / q ^ e) + d % q ^ e) := by rw [← hvd]
        _ = v m * v d := by rw [hddecomp]

/-- A zero prefix state kills the periodically weighted convolution on every
positive-depth descendant interval of the same seed. -/
theorem weighted_zero_on_seed_descendants
    (q seed : ℕ) (hq : 2 ≤ q) (hqzero : (q : K) = 0) (v w : ℕ → K)
    (hw : Function.Periodic w q)
    (hlucas : ∀ m d, d < q → v (q * m + d) = v m * v d)
    (hseed : prefixState v seed = (0, 0)) :
    ∀ E, 1 ≤ E → ∀ j, j < q ^ E →
      weighted w v (seed * q ^ E + j) = 0 := by
  apply zero_on_positive_depth_descendants_of_parent
    (Z := fun n => prefixState v n = (0, 0)) hq hseed
  · intro n d hd hn
    rw [prefixState_transition v q hqzero hlucas n d hd, hn,
      DigitState.transition_zero]
  · intro n d hd hn
    have hv : v n = 0 := congrArg Prod.snd hn
    have hf : (∑ j ∈ Finset.range (n + 1), v j) = 0 := congrArg Prod.fst hn
    exact weighted_zero_of_state w v q n d hd hw hlucas hv hf

/-- If the weight has grouped period `q^r`, the same seed kills every
original base-`q` descendant interval from depth `r` onward. -/
theorem weighted_zero_on_seed_descendants_pow
    (q seed r : ℕ) (hq : 2 ≤ q) (hqzero : (q : K) = 0) (v w : ℕ → K)
    (hv0 : v 0 = 1) (hw : Function.Periodic w (q ^ r))
    (hlucas : ∀ m d, d < q → v (q * m + d) = v m * v d)
    (hseed : prefixState v seed = (0, 0)) :
    ∀ E, r ≤ E → ∀ j, j < q ^ E →
      weighted w v (seed * q ^ E + j) = 0 := by
  have happend : ∀ n d, d < q →
      prefixState v n = (0, 0) → prefixState v (q * n + d) = (0, 0) := by
    intro n d hd hn
    rw [prefixState_transition v q hqzero hlucas n d hd, hn,
      DigitState.transition_zero]
  intro E hrE j hj
  let F := E - r
  let Q := q ^ r
  let M := seed * q ^ F + j / Q
  let d := j % Q
  have hqpos : 0 < q := by omega
  have hQpos : 0 < Q := by simp [Q, hqpos]
  have hEr : F + r = E := by
    dsimp [F]
    omega
  have hjdiv : j / Q < q ^ F := by
    apply (Nat.div_lt_iff_lt_mul hQpos).2
    rw [← pow_add, hEr]
    exact hj
  have hM : prefixState v M = (0, 0) := by
    exact descendants_of_append hq hseed happend F (j / Q) hjdiv
  have hd : d < Q := by
    exact Nat.mod_lt j hQpos
  have hv : v M = 0 := congrArg Prod.snd hM
  have hf : (∑ a ∈ Finset.range (M + 1), v a) = 0 := congrArg Prod.fst hM
  have hzero : weighted w v (Q * M + d) = 0 :=
    weighted_zero_of_state w v Q M d hd hw
      (lucas_pow v q (by omega) hv0 hlucas r) hv hf
  have hjdecomp : Q * (j / Q) + d = j := by
    exact Nat.div_add_mod j Q
  have hindex : Q * M + d = seed * q ^ E + j := by
    calc
      Q * M + d = Q * (seed * q ^ F) + (Q * (j / Q) + d) := by
        dsimp [M]
        rw [Nat.mul_add]
        ac_rfl
      _ = Q * (seed * q ^ F) + j := by rw [hjdecomp]
      _ = seed * (q ^ F * q ^ r) + j := by
        dsimp [Q]
        ring
      _ = seed * q ^ (F + r) + j := by rw [pow_add]
      _ = seed * q ^ E + j := by rw [hEr]
  rw [← hindex]
  exact hzero

/-- The coefficient weight for a pole of order `s`. -/
def poleWeight (s n : ℕ) : K :=
  (Nat.choose (s - 1 + n) (s - 1) : K)

/-- The power series whose degree-`n` coefficient is `w n * beta^n`. -/
def weightedSeries (w : ℕ → K) (beta : K) : PowerSeries K :=
  PowerSeries.mk fun n => w n * beta ^ n

@[simp] theorem coeff_weightedSeries (w : ℕ → K) (beta : K) (n : ℕ) :
    PowerSeries.coeff n (weightedSeries w beta) = w n * beta ^ n := by
  simp [weightedSeries]

/-- Multiplication by a weighted geometric series is the corresponding
periodically weighted convolution after twisting the other factor by
`beta⁻¹`. -/
theorem coeff_weightedSeries_mul_eq_weighted
    {F : Type*} [Field F] (w : ℕ → F) (beta : F) (hbeta : beta ≠ 0)
    (T : PowerSeries F) (n : ℕ) :
    PowerSeries.coeff n (weightedSeries w beta * T) =
      beta ^ n * weighted w
        (fun r => PowerSeries.coeff r T * (beta⁻¹) ^ r) n := by
  rw [mul_comm, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_weightedSeries, weighted, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hrle : r ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
  have hpow : beta ^ n * (beta⁻¹) ^ r = beta ^ (n - r) := by
    rw [← Nat.sub_add_cancel hrle, pow_add, mul_assoc, ← mul_pow]
    simp [hbeta]
  rw [← hpow]
  ring

/-- A grouped periodic weight applied to a Lucas series has the common
descendant seed blocks as soon as the twisted coefficient prefix state is
zero at the seed. -/
theorem weightedSeries_mul_hasSeedBlocks_of_prefix
    {F : Type*} [Field F] (q seed r : ℕ) (hq : 2 ≤ q)
    (hqzero : (q : F) = 0) (w : ℕ → F)
    (hw : Function.Periodic w (q ^ r)) (beta : F) (hbeta : beta ≠ 0)
    (T : PowerSeries F)
    (hv0 : PowerSeries.coeff 0 T * (beta⁻¹) ^ 0 = 1)
    (hlucas : ∀ m d, d < q →
      PowerSeries.coeff (q * m + d) T * (beta⁻¹) ^ (q * m + d) =
        (PowerSeries.coeff m T * (beta⁻¹) ^ m) *
          (PowerSeries.coeff d T * (beta⁻¹) ^ d))
    (hseed : prefixState
      (fun n => PowerSeries.coeff n T * (beta⁻¹) ^ n) seed = (0, 0)) :
    IndependentZeroBlocks.HasSeedBlocks q seed (weightedSeries w beta * T) := by
  refine ⟨0, r, ?_⟩
  intro E hrE j _ hj
  rw [coeff_weightedSeries_mul_eq_weighted w beta hbeta T]
  rw [weighted_zero_on_seed_descendants_pow q seed r hq hqzero
    (fun n => PowerSeries.coeff n T * (beta⁻¹) ^ n) w hv0 hw hlucas hseed
    E hrE j hj]
  simp

/-- The power series `(1 - beta X)⁻ˢ`, obtained by rescaling the standard
inverse power. -/
noncomputable def repeatedPoleSeries (beta : K) (s : ℕ) : PowerSeries K :=
  PowerSeries.rescale beta (PowerSeries.invOneSubPow K s).val

/-- The coefficients of `(1 - beta X)⁻ˢ` are the pole weight times
`beta^n`. -/
@[simp] theorem coeff_repeatedPoleSeries (beta : K) (s n : ℕ) (hs : 0 < s) :
    PowerSeries.coeff n (repeatedPoleSeries beta s) =
      beta ^ n * poleWeight s n := by
  rw [repeatedPoleSeries, PowerSeries.coeff_rescale,
    PowerSeries.invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos K s hs,
    PowerSeries.coeff_mk]
  rfl

/-- Multiplication by a repeated-pole series is the periodically weighted
convolution after twisting the other factor by `beta⁻¹`. -/
theorem coeff_repeatedPoleSeries_mul_eq_weighted
    {F : Type*} [Field F] (beta : F) (hbeta : beta ≠ 0) (s : ℕ) (hs : 0 < s)
    (T : PowerSeries F) (n : ℕ) :
    PowerSeries.coeff n (repeatedPoleSeries beta s * T) =
      beta ^ n * weighted (poleWeight s)
        (fun r => PowerSeries.coeff r T * (beta⁻¹) ^ r) n := by
  rw [mul_comm, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_repeatedPoleSeries beta s _ hs, weighted, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hrle : r ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
  have hpow : beta ^ n * (beta⁻¹) ^ r = beta ^ (n - r) := by
    rw [← Nat.sub_add_cancel hrle, pow_add, mul_assoc, ← mul_pow]
    simp [hbeta]
  rw [← hpow]
  ring

/-- Below a prime power `p^e`, adding that prime power to the upper argument
of a binomial coefficient does not change its value in characteristic `p`. -/
theorem cast_choose_add_prime_pow (p e N k : ℕ) [Fact p.Prime] [CharP K p]
    (hk : k < p ^ e) :
    ((Nat.choose (p ^ e + N) k : ℕ) : K) = (Nat.choose N k : K) := by
  let X : Polynomial K := Polynomial.X
  have hfresh : (X + 1) ^ p ^ e = X ^ p ^ e + 1 := by
    simpa [X] using add_pow_char_pow (Polynomial.X : Polynomial K) 1 p e
  calc
    ((Nat.choose (p ^ e + N) k : ℕ) : K) =
        ((X + 1) ^ (p ^ e + N)).coeff k := by
          simp [X, Polynomial.coeff_X_add_one_pow]
    _ = (((X + 1) ^ p ^ e) * ((X + 1) ^ N)).coeff k := by
          rw [pow_add]
    _ = ((X ^ p ^ e + 1) * ((X + 1) ^ N)).coeff k := by rw [hfresh]
    _ = ((X + 1) ^ N).coeff k := by
          rw [add_mul, one_mul, Polynomial.coeff_add]
          rw [Polynomial.coeff_X_pow_mul']
          simp [Nat.not_le.mpr hk]
    _ = (Nat.choose N k : K) := by
          simp [X, Polynomial.coeff_X_add_one_pow]

/-- In characteristic `p`, the order-`s` pole weight has period `p^e` as
soon as `s ≤ p^e`. -/
theorem poleWeight_periodic_prime_pow (p e s : ℕ) [Fact p.Prime] [CharP K p]
    (hs : 0 < s) (hsp : s ≤ p ^ e) :
    Function.Periodic (poleWeight (K := K) s) (p ^ e) := by
  intro n
  unfold poleWeight
  rw [show s - 1 + (n + p ^ e) = p ^ e + (s - 1 + n) by omega]
  exact cast_choose_add_prime_pow p e (s - 1 + n) (s - 1) (by omega)

end SierpinskiFormal.PeriodicConvolution

#print axioms SierpinskiFormal.PeriodicConvolution.weighted_block
#print axioms SierpinskiFormal.PeriodicConvolution.weighted_zero_of_state
#print axioms SierpinskiFormal.PeriodicConvolution.lucas_pow
#print axioms SierpinskiFormal.PeriodicConvolution.weighted_zero_on_seed_descendants_pow
#print axioms SierpinskiFormal.PeriodicConvolution.poleWeight_periodic_prime_pow
#print axioms SierpinskiFormal.PeriodicConvolution.coeff_repeatedPoleSeries_mul_eq_weighted
#print axioms SierpinskiFormal.PeriodicConvolution.coeff_weightedSeries_mul_eq_weighted
#print axioms SierpinskiFormal.PeriodicConvolution.weightedSeries_mul_hasSeedBlocks_of_prefix
