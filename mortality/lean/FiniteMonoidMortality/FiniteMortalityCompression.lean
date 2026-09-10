import FiniteMonoidMortality.MinimalRankCompression
import Mathlib.Algebra.Order.Star.Real
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.NoncommRing

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace FiniteMonoidMortality

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

theorem exists_invariant_posDef_of_finite_mul_mem
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (R : Set (Matrix n n ℝ)) (hfinite : R.Finite)
    (hmul : ∀ ⦃x y : Matrix n n ℝ⦄, x ∈ R → y ∈ R → x * y ∈ R) :
    ∃ Q : Matrix n n ℝ,
      Q.transpose = Q ∧ Q.PosDef ∧
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
    · apply Matrix.posDef_sum Finset.univ_nonempty
      intro g _
      have hp := (Matrix.IsUnit.posDef_star_right_conjugate_iff
        (x := (1 : Matrix n n ℝ)) (Units.isUnit g.1)).2 Matrix.PosDef.one
      simpa only [mul_one, Matrix.star_eq_conjTranspose,
        Matrix.conjTranspose_eq_transpose_of_trivial] using hp
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
  · refine ⟨1, by simp, Matrix.PosDef.one, ?_⟩
    intro k hkR hkunit
    exact (hex ⟨k, hkR, hkunit⟩).elim

theorem exists_invariant_quadraticForm_of_finite_mul_mem
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (R : Set (Matrix n n ℝ)) (hfinite : R.Finite)
    (hmul : ∀ ⦃x y : Matrix n n ℝ⦄, x ∈ R → y ∈ R → x * y ∈ R) :
    ∃ Q : Matrix n n ℝ,
      Q.transpose = Q ∧ 0 < Matrix.trace Q ∧
        ∀ k ∈ R, IsUnit k → k * Q * k.transpose = Q := by
  obtain ⟨Q, hs, hp, hi⟩ := exists_invariant_posDef_of_finite_mul_mem R hfinite hmul
  exact ⟨Q, hs, hp.trace_pos, hi⟩

theorem exists_invariant_quadraticForm_compressedReturn_of_finite
    {A ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (hr : 0 < r)
    (M : A → Matrix ι ι ℝ) (h : List A)
    (U : Matrix ι (Fin r) ℝ) (V : Matrix (Fin r) ι ℝ)
    (hfac : matrixWord M h = U * V)
    (hfinite : (Set.range (matrixWord M)).Finite) :
    ∃ Q : Matrix (Fin r) (Fin r) ℝ,
      Q.transpose = Q ∧ 0 < Matrix.trace Q ∧
        ∀ y : List A, IsUnit (compressedReturn M U V y) →
          compressedReturn M U V y * Q * (compressedReturn M U V y).transpose = Q := by
  let _ : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr
  let compress : Matrix ι ι ℝ → Matrix (Fin r) (Fin r) ℝ := fun X => V * X * U
  let R : Set (Matrix (Fin r) (Fin r) ℝ) := Set.range (compressedReturn M U V)
  have hRfinite : R.Finite := by
    have hrange : R = compress '' Set.range (matrixWord M) := by
      rw [← Set.range_comp]
      rfl
    rw [hrange]
    exact hfinite.image compress
  have hRmul : ∀ ⦃K L : Matrix (Fin r) (Fin r) ℝ⦄,
      K ∈ R → L ∈ R → K * L ∈ R := by
    rintro K L ⟨y, rfl⟩ ⟨z, rfl⟩
    exact ⟨y ++ h ++ z, (compressedReturn_mul M h U V hfac y z).symm⟩
  obtain ⟨Q, hQsymm, hQtrace, hQinv⟩ :=
    exists_invariant_quadraticForm_of_finite_mul_mem R hRfinite hRmul
  exact ⟨Q, hQsymm, hQtrace, fun y hy => hQinv _ ⟨y, rfl⟩ hy⟩

theorem exists_invariant_posDef_compressedReturn_of_finite
    {A ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (hr : 0 < r)
    (M : A → Matrix ι ι ℝ) (h : List A)
    (U : Matrix ι (Fin r) ℝ) (V : Matrix (Fin r) ι ℝ)
    (hfac : matrixWord M h = U * V)
    (hfinite : (Set.range (matrixWord M)).Finite) :
    ∃ Q : Matrix (Fin r) (Fin r) ℝ,
      Q.transpose = Q ∧ Q.PosDef ∧
        ∀ y : List A, IsUnit (compressedReturn M U V y) →
          compressedReturn M U V y * Q * (compressedReturn M U V y).transpose = Q := by
  let _ : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr
  let compress : Matrix ι ι ℝ → Matrix (Fin r) (Fin r) ℝ := fun X => V * X * U
  let R : Set (Matrix (Fin r) (Fin r) ℝ) := Set.range (compressedReturn M U V)
  have hRfinite : R.Finite := by
    have hrange : R = compress '' Set.range (matrixWord M) := by
      rw [← Set.range_comp]
      rfl
    rw [hrange]
    exact hfinite.image compress
  have hRmul : ∀ ⦃K L : Matrix (Fin r) (Fin r) ℝ⦄,
      K ∈ R → L ∈ R → K * L ∈ R := by
    rintro K L ⟨y, rfl⟩ ⟨z, rfl⟩
    exact ⟨y ++ h ++ z, (compressedReturn_mul M h U V hfac y z).symm⟩
  obtain ⟨Q, hQsymm, hQtrace, hQinv⟩ :=
    exists_invariant_posDef_of_finite_mul_mem R hRfinite hRmul
  exact ⟨Q, hQsymm, hQtrace, fun y hy => hQinv _ ⟨y, rfl⟩ hy⟩

end FiniteMonoidMortality
