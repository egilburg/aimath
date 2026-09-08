import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Matrix.Trace
import SierpinskiFormal.MinimalRankCompression

set_option autoImplicit false

/-!
# An invariant quadratic form for a finite matrix semigroup

The invertible members of a finite multiplicatively closed set form a finite
group (provided there is at least one of them).  Averaging `g * gᵀ` over this
group gives a nonzero-trace symmetric form invariant under every invertible
member of the original set.
-/

noncomputable section

open scoped BigOperators

namespace IndependentZeroBlocks

private theorem pow_mem_of_mem_of_mul_mem {M : Type*} [Monoid M]
    (R : Set M) (hmul : ∀ ⦃x y : M⦄, x ∈ R → y ∈ R → x * y ∈ R)
    {x : M} (hx : x ∈ R) {m : ℕ} (hm : 0 < m) : x ^ m ∈ R := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  have haux : ∀ e : ℕ, x ^ (e + 1) ∈ R := by
    intro e
    induction e with
    | zero => simpa using hx
    | succ e ih =>
        rw [pow_succ]
        exact hmul ih hx
  simpa [Nat.succ_eq_add_one] using haux d

private theorem isOfFinOrder_unit_of_finite_mul_mem {M : Type*} [Monoid M]
    (R : Set M) (hfinite : R.Finite)
    (hmul : ∀ ⦃x y : M⦄, x ∈ R → y ∈ R → x * y ∈ R)
    {x : M} (hx : x ∈ R) (hunit : IsUnit x) :
    IsOfFinOrder hunit.unit := by
  rw [← finite_powers]
  apply Set.Finite.of_finite_image (f := fun u : Mˣ => (u : M))
  · apply (Set.finite_singleton (1 : M) |>.union hfinite).subset
    rintro y ⟨u, hu, rfl⟩
    change u ∈ (Submonoid.powers hunit.unit : Set Mˣ) at hu
    obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff u hunit.unit).mp hu
    subst u
    cases m with
    | zero => simp
    | succ m =>
        right
        simpa [hunit.unit_spec] using
          pow_mem_of_mem_of_mul_mem R hmul hx (Nat.succ_pos m)
  · exact Units.val_injective.injOn

private theorem one_mem_of_finite_mul_mem_of_isUnit {M : Type*} [Monoid M]
    (R : Set M) (hfinite : R.Finite)
    (hmul : ∀ ⦃x y : M⦄, x ∈ R → y ∈ R → x * y ∈ R)
    {x : M} (hx : x ∈ R) (hunit : IsUnit x) : (1 : M) ∈ R := by
  have horder := isOfFinOrder_unit_of_finite_mul_mem R hfinite hmul hx hunit
  have hmem := pow_mem_of_mem_of_mul_mem R hmul hx horder.orderOf_pos
  have heq : x ^ orderOf hunit.unit = 1 := by
    calc
      x ^ orderOf hunit.unit = (hunit.unit : M) ^ orderOf hunit.unit := by
        rw [hunit.unit_spec]
      _ = (↑(hunit.unit ^ orderOf hunit.unit) : M) := by
        rw [Units.val_pow_eq_pow_val]
      _ = 1 := by rw [pow_orderOf_eq_one]; rfl
  rw [heq] at hmem
  exact hmem

private theorem unit_inv_mem_of_finite_mul_mem {M : Type*} [Monoid M]
    (R : Set M) (hfinite : R.Finite)
    (hmul : ∀ ⦃x y : M⦄, x ∈ R → y ∈ R → x * y ∈ R)
    (u : Mˣ) (hu : (u : M) ∈ R) : (↑u⁻¹ : M) ∈ R := by
  have horder : IsOfFinOrder u := by
    simpa only [IsUnit.unit_of_val_units] using
      isOfFinOrder_unit_of_finite_mul_mem R hfinite hmul hu u.isUnit
  have hone : (1 : M) ∈ R :=
    one_mem_of_finite_mul_mem_of_isUnit R hfinite hmul hu u.isUnit
  have hp : (u : M) ^ (orderOf u - 1) ∈ R := by
    by_cases ho : orderOf u = 1
    · simpa [ho] using hone
    · apply pow_mem_of_mem_of_mul_mem R hmul hu
      exact Nat.zero_lt_sub_of_lt
        (Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨horder.orderOf_pos.ne', ho⟩)
  have heq : u ^ (orderOf u - 1) = u⁻¹ := by
    apply (mul_right_cancel_iff (a := u)).mp
    rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
      horder.orderOf_pos.ne'), pow_orderOf_eq_one]
    simp
  rw [← Units.val_pow_eq_pow_val, heq] at hp
  exact hp

/-- The invertible members of a finite multiplicatively closed subset of a
monoid form a finite subgroup of the unit group, as soon as one such member
exists. -/
private def invertibleSubgroup {M : Type*} [Monoid M]
    (R : Set M) (hfinite : R.Finite)
    (hmul : ∀ ⦃x y : M⦄, x ∈ R → y ∈ R → x * y ∈ R)
    (x : M) (hx : x ∈ R) (hunit : IsUnit x) : Subgroup Mˣ where
  carrier := {u | (u : M) ∈ R}
  one_mem' := one_mem_of_finite_mul_mem_of_isUnit R hfinite hmul hx hunit
  mul_mem' := fun hu hv => hmul hu hv
  inv_mem' := fun hu => unit_inv_mem_of_finite_mul_mem R hfinite hmul _ hu

private theorem invertibleSubgroup_finite {M : Type*} [Monoid M]
    (R : Set M) (hfinite : R.Finite)
    (hmul : ∀ ⦃x y : M⦄, x ∈ R → y ∈ R → x * y ∈ R)
    (x : M) (hx : x ∈ R) (hunit : IsUnit x) :
    Finite (invertibleSubgroup R hfinite hmul x hx hunit) := by
  let _ : Fintype R := hfinite.fintype
  let G := invertibleSubgroup R hfinite hmul x hx hunit
  let f : G → R := fun g => ⟨(g.1 : M), g.2⟩
  exact Finite.of_injective f (fun a b hab => Subtype.ext (Units.ext (congrArg Subtype.val hab)))

private theorem trace_mul_transpose_nonneg {n : Type*} [Fintype n]
    (A : Matrix n n ℝ) : 0 ≤ Matrix.trace (A * A.transpose) := by
  classical
  simp only [Matrix.trace]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_self_nonneg (A i j)

/-- A finite multiplicatively closed set of real square matrices admits a
symmetric form of positive trace which is invariant under all its invertible
members.  The positive dimension hypothesis is used only to make the trace
strictly positive. -/
theorem exists_invariant_quadraticForm_of_finite_mul_mem
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (R : Set (Matrix n n ℝ)) (hfinite : R.Finite)
    (hmul : ∀ ⦃x y : Matrix n n ℝ⦄, x ∈ R → y ∈ R → x * y ∈ R) :
    ∃ Q : Matrix n n ℝ,
      Q.transpose = Q ∧ 0 < Matrix.trace Q ∧
        ∀ k ∈ R, IsUnit k → k * Q * k.transpose = Q := by
  classical
  by_cases hex : ∃ k ∈ R, IsUnit k
  · obtain ⟨k₀, hk₀R, hk₀unit⟩ := hex
    let G := invertibleSubgroup R hfinite hmul k₀ hk₀R hk₀unit
    let _ : Finite G := invertibleSubgroup_finite R hfinite hmul k₀ hk₀R hk₀unit
    let _ : Fintype G := Fintype.ofFinite G
    let Q : Matrix n n ℝ := ∑ g : G, (g.1 : Matrix n n ℝ) * (g.1 : Matrix n n ℝ).transpose
    refine ⟨Q, ?_, ?_, ?_⟩
    · ext i j
      rw [Matrix.transpose_apply]
      simp only [Q, Matrix.sum_apply, Matrix.mul_apply, Matrix.transpose_apply]
      apply Finset.sum_congr rfl
      intro g _
      apply Finset.sum_congr rfl
      intro a _
      exact mul_comm _ _
    · have hle : Matrix.trace ((1 : Matrix n n ℝ) * (1 : Matrix n n ℝ).transpose) ≤
          Matrix.trace Q := by
        calc
          Matrix.trace ((1 : Matrix n n ℝ) * (1 : Matrix n n ℝ).transpose) ≤
              ∑ g : G, Matrix.trace ((g.1 : Matrix n n ℝ) *
                (g.1 : Matrix n n ℝ).transpose) := by
                  have hs := Finset.single_le_sum
                    (s := Finset.univ)
                    (f := fun g : G => Matrix.trace ((g.1 : Matrix n n ℝ) *
                      (g.1 : Matrix n n ℝ).transpose))
                    (fun g _ => trace_mul_transpose_nonneg
                      (g.1 : Matrix n n ℝ))
                    (Finset.mem_univ (1 : G))
                  simpa only [Subgroup.coe_one, Units.val_one] using hs
          _ = Matrix.trace Q := by
            simp only [Q, Matrix.trace_sum]
      have hcard : (0 : ℝ) < Fintype.card n := by exact_mod_cast Fintype.card_pos
      have honeTrace : Matrix.trace ((1 : Matrix n n ℝ) *
          (1 : Matrix n n ℝ).transpose) = Fintype.card n := by
        rw [Matrix.transpose_one, mul_one, Matrix.trace_one]
      rw [honeTrace] at hle
      exact hcard.trans_le hle
    · intro k hkR hkunit
      let kg : G := ⟨hkunit.unit, by
        change (hkunit.unit : Matrix n n ℝ) ∈ R
        simpa only [hkunit.unit_spec] using hkR⟩
      have hkcoe : (kg.1 : Matrix n n ℝ) = k := hkunit.unit_spec
      rw [← hkcoe]
      have hterm (g : G) :
          (kg.1 : Matrix n n ℝ) *
              ((g.1 : Matrix n n ℝ) * (g.1 : Matrix n n ℝ).transpose) *
                (kg.1 : Matrix n n ℝ).transpose =
            ((kg * g).1 : Matrix n n ℝ) *
              ((kg * g).1 : Matrix n n ℝ).transpose := by
        simp only [Subgroup.coe_mul, Units.val_mul, Matrix.transpose_mul]
        noncomm_ring
      calc
        (kg.1 : Matrix n n ℝ) * Q * (kg.1 : Matrix n n ℝ).transpose =
            ∑ g : G, (kg.1 : Matrix n n ℝ) *
              ((g.1 : Matrix n n ℝ) * (g.1 : Matrix n n ℝ).transpose) *
                (kg.1 : Matrix n n ℝ).transpose := by
                  simp only [Q, Matrix.mul_sum, Matrix.sum_mul]
        _ =
            ∑ g : G, (((kg * g).1 : Matrix n n ℝ) *
              (((kg * g).1 : Matrix n n ℝ).transpose)) := by
                apply Finset.sum_congr rfl
                intro g _
                exact hterm g
        _ = ∑ g : G, ((g.1 : Matrix n n ℝ) * (g.1 : Matrix n n ℝ).transpose) :=
          Equiv.sum_comp (Equiv.mulLeft kg)
            (fun g : G => (g.1 : Matrix n n ℝ) * (g.1 : Matrix n n ℝ).transpose)
  · refine ⟨1, by simp, ?_, ?_⟩
    · simpa using (show (0 : ℝ) < Fintype.card n by exact_mod_cast Fintype.card_pos)
    · intro k hkR hkunit
      exact (hex ⟨k, hkR, hkunit⟩).elim

/-- The compressed returns associated to a factorization `matrixWord M h = U V`
form a finite multiplicative semigroup whenever the whole word monoid is
finite.  Consequently they admit one common invariant form of positive trace.
-/
theorem exists_invariant_quadraticForm_returnMatrix_of_finite
    {A ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (hr : 0 < r)
    (M : A → Matrix ι ι ℝ) (h : List A)
    (U : Matrix ι (Fin r) ℝ) (V : Matrix (Fin r) ι ℝ)
    (hfac : matrixWord M h = U * V)
    (hfinite : (Set.range (matrixWord M)).Finite) :
    ∃ Q : Matrix (Fin r) (Fin r) ℝ,
      Q.transpose = Q ∧ 0 < Matrix.trace Q ∧
        ∀ y : List A, IsUnit (returnMatrix M U V y) →
          returnMatrix M U V y * Q * (returnMatrix M U V y).transpose = Q := by
  let _ : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr
  let compress : Matrix ι ι ℝ → Matrix (Fin r) (Fin r) ℝ := fun X => V * X * U
  let R : Set (Matrix (Fin r) (Fin r) ℝ) := Set.range (returnMatrix M U V)
  have hRfinite : R.Finite := by
    have hrange : R = compress '' Set.range (matrixWord M) := by
      rw [← Set.range_comp]
      rfl
    rw [hrange]
    exact hfinite.image compress
  have hRmul : ∀ ⦃K L : Matrix (Fin r) (Fin r) ℝ⦄,
      K ∈ R → L ∈ R → K * L ∈ R := by
    rintro K L ⟨y, rfl⟩ ⟨z, rfl⟩
    exact ⟨y ++ h ++ z, (returnMatrix_mul M h U V hfac y z).symm⟩
  obtain ⟨Q, hQsymm, hQtrace, hQinv⟩ :=
    exists_invariant_quadraticForm_of_finite_mul_mem R hRfinite hRmul
  exact ⟨Q, hQsymm, hQtrace, fun y hy => hQinv _ ⟨y, rfl⟩ hy⟩

/-- The scalar quadratic defect attached to an invariant form.  This version
uses no inverse of `Q`: it is enough that it vanish on invertible compressed
returns and be nonzero at the zero return. -/
def invariantTraceDefect {n : Type*} [Fintype n]
    (Q K : Matrix n n ℝ) : ℝ :=
  Matrix.trace Q - Matrix.trace (K * Q * K.transpose)

@[simp] theorem invariantTraceDefect_zero {n : Type*} [Fintype n]
    (Q : Matrix n n ℝ) : invariantTraceDefect Q 0 = Matrix.trace Q := by
  simp [invariantTraceDefect]

theorem invariantTraceDefect_eq_zero_of_invariant
    {n : Type*} [Fintype n]
    {Q K : Matrix n n ℝ} (hinvariant : K * Q * K.transpose = Q) :
    invariantTraceDefect Q K = 0 := by
  simp [invariantTraceDefect, hinvariant]

/-- A nonzero invariant-trace defect certifies a strict rank drop in a
sandwich.  This is the contrapositive use of the full-rank compressed-return
lemma and avoids any separate injectivity/surjectivity proof for `U` and `V`.
-/
theorem rank_sandwich_lt_of_invariantTraceDefect_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (U : Matrix ι (Fin r) ℝ) (V : Matrix (Fin r) ι ℝ)
    (H Y : Matrix ι ι ℝ) (hfac : H = U * V)
    (Q : Matrix (Fin r) (Fin r) ℝ)
    (hinvariant : IsUnit (V * Y * U) →
      (V * Y * U) * Q * (V * Y * U).transpose = Q)
    (hdefect : invariantTraceDefect Q (V * Y * U) ≠ 0) :
    (H * Y * H).rank < r := by
  apply Nat.lt_of_not_ge
  intro hlower
  have hunit : IsUnit (V * Y * U) :=
    sandwich_isUnit_of_rank_lower_bound U V H Y hfac hlower
  exact hdefect (invariantTraceDefect_eq_zero_of_invariant (hinvariant hunit))

/-- Word-level specialization of the preceding strict rank-drop certificate. -/
theorem rank_resetSandwich_lt_of_invariantTraceDefect_ne_zero
    {A ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (M : A → Matrix ι ι ℝ) (h y : List A)
    (U : Matrix ι (Fin r) ℝ) (V : Matrix (Fin r) ι ℝ)
    (hfac : matrixWord M h = U * V)
    (Q : Matrix (Fin r) (Fin r) ℝ)
    (hinvariant : IsUnit (returnMatrix M U V y) →
      returnMatrix M U V y * Q * (returnMatrix M U V y).transpose = Q)
    (hdefect : invariantTraceDefect Q (returnMatrix M U V y) ≠ 0) :
    (matrixWord M (h ++ y ++ h)).rank < r := by
  simpa only [matrixWord_append, returnMatrix] using
    rank_sandwich_lt_of_invariantTraceDefect_ne_zero U V
      (matrixWord M h) (matrixWord M y) hfac Q hinvariant hdefect

end IndependentZeroBlocks
