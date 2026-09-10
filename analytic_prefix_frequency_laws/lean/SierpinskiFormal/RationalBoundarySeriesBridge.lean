import SierpinskiFormal.CommRingBoundaryDensity
import SierpinskiFormal.BoundarySeriesHolomorphic

/-!
# Rational boundary densities as complex boundary series

This file reindexes marker-free block gaps by ordinary words over the
nonmarker block alphabet.  It then packages the rational density formula as
a complex boundary-series expression, ready for the holomorphy results.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open Filter Set
open scoped BigOperators Topology

namespace IndependentZeroBlocks

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Blocks other than the distinguished reset block. -/
abbrev NonMarkerBlock (h : List A) :=
  {c : Fin h.length → A // c ≠ endoMarkerBlock h}

/-- A word over the nonmarker subtype, viewed as a marker-free block word. -/
def gapOfSubtypeList (h : List A) (x : List (NonMarkerBlock h)) :
    GapWords (endoMarkerBlock h) :=
  ⟨x.map Subtype.val, by simp⟩

@[simp] theorem gapOfSubtypeList_val (h : List A)
    (x : List (NonMarkerBlock h)) :
    (gapOfSubtypeList h x).1 = x.map Subtype.val :=
  rfl

/-- A marker-free block word, with the nonmarker proof attached letterwise. -/
def subtypeListOfGap (h : List A) (g : GapWords (endoMarkerBlock h)) :
    List (NonMarkerBlock h) :=
  g.1.attach.map (fun c ↦ ⟨c.1, fun he ↦ g.2 (by simpa [he] using c.2)⟩)

@[simp] theorem map_subtypeListOfGap (h : List A)
    (g : GapWords (endoMarkerBlock h)) :
    (subtypeListOfGap h g).map Subtype.val = g.1 := by
  simp [subtypeListOfGap]

/-- Words on the nonmarker block alphabet are exactly marker-free block
words. -/
def nonMarkerListEquivGap (h : List A) :
    List (NonMarkerBlock h) ≃ GapWords (endoMarkerBlock h) where
  toFun := gapOfSubtypeList h
  invFun := subtypeListOfGap h
  left_inv x := by
    apply (List.map_injective_iff.mpr (fun a b hab ↦ Subtype.ext hab))
    simp [subtypeListOfGap, gapOfSubtypeList]
  right_inv g := by
    apply Subtype.ext
    exact map_subtypeListOfGap h g

/-- Product of complex letter weights along a list. -/
def complexWordWeight {D : Type*} (q : D → ℂ) (w : List D) : ℂ :=
  (w.map q).prod

@[simp] theorem complexWordWeight_nil {D : Type*} (q : D → ℂ) :
    complexWordWeight q [] = 1 := by
  simp [complexWordWeight]

@[simp] theorem complexWordWeight_ofFn {D : Type*} (q : D → ℂ)
    {n : ℕ} (x : Fin n → D) :
    complexWordWeight q (List.ofFn x) = Sierpinski.finWordMonomial q x := by
  simp [complexWordWeight, Sierpinski.finWordMonomial, List.prod_ofFn]

@[simp] theorem complexWordWeight_ofReal {D : Type*} (p : D → ℝ)
    (w : List D) :
    complexWordWeight (fun d ↦ (p d : ℂ)) w =
      (wordWeight (R := ℝ) p w : ℂ) := by
  unfold complexWordWeight wordWeight
  change (w.map (fun d ↦ (p d : ℂ))).prod =
    Complex.ofRealHom ((w.map p).prod)
  rw [map_list_prod]
  simp only [List.map_map, Function.comp_apply]
  congr 1

/-- Absolute complex word weights are summable when the finite `ℓ1` mass is
strictly below one. -/
theorem summable_norm_complexWordWeight {D : Type*} [Fintype D]
    (q : D → ℂ) (hq : Sierpinski.finiteL1Norm q < 1) :
    Summable (fun w : List D ↦ ‖complexWordWeight q w‖) := by
  let term : (Σ n : ℕ, Fin n → D) → ℝ := fun x ↦ ∏ k, ‖q (x.2 k)‖
  have hterm0 : ∀ x, 0 ≤ term x := by
    intro x
    exact Finset.prod_nonneg fun _ _ ↦ norm_nonneg _
  have hfiber (n : ℕ) :
      (∑' x : Fin n → D, term ⟨n, x⟩) =
        Sierpinski.finiteL1Norm q ^ n := by
    rw [tsum_fintype]
    exact Sierpinski.sum_finWordMonomial_norm q n
  have houter : Summable (fun n : ℕ ↦ ∑' x : Fin n → D, term ⟨n, x⟩) := by
    simp_rw [hfiber]
    exact summable_geometric_of_lt_one (Sierpinski.finiteL1Norm_nonneg q) hq
  have hsigma : Summable term :=
    (summable_sigma_of_nonneg hterm0).2
      ⟨fun n ↦ (hasSum_fintype _).summable, houter⟩
  have hcomp :
      (term ∘ (List.equivSigmaTuple (α := D))) =
        fun w : List D ↦ ‖complexWordWeight q w‖ := by
    funext w
    simp only [term, Function.comp_apply, List.equivSigmaTuple,
      Equiv.coe_fn_mk, complexWordWeight, List.norm_prod, List.map_map,
      Function.comp_apply]
    rw [← List.prod_ofFn]
    conv_rhs => rw [← List.ofFn_get w]
    rw [List.map_ofFn]
    congr 2
  rw [← hcomp]
  exact ((List.equivSigmaTuple (α := D)).summable_iff).2 hsigma

/-- The bidegree definition of `boundarySeries` is the direct absolutely
convergent sum over pairs of finite words. -/
theorem boundarySeries_eq_tsum_listPair {D : Type*} [Fintype D]
    (c : List D → List D → ℂ) (hc : ∀ x z, ‖c x z‖ ≤ 1)
    (q : D → ℂ) (hq : Sierpinski.finiteL1Norm q < 1) :
    Sierpinski.boundarySeries c q =
      ∑' xz : List D × List D,
        c xz.1 xz.2 * complexWordWeight q xz.1 * complexWordWeight q xz.2 := by
  classical
  let listTerm : List D × List D → ℂ := fun xz ↦
    c xz.1 xz.2 * complexWordWeight q xz.1 * complexWordWeight q xz.2
  let listMajor : List D × List D → ℝ := fun xz ↦
    ‖complexWordWeight q xz.1‖ * ‖complexWordWeight q xz.2‖
  have hw : Summable (fun w : List D ↦ ‖complexWordWeight q w‖) :=
    summable_norm_complexWordWeight q hq
  have hmajor : Summable listMajor := by
    change Summable (fun xz : List D × List D ↦
      ‖complexWordWeight q xz.1‖ * ‖complexWordWeight q xz.2‖)
    exact hw.mul_of_nonneg hw (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_nonneg _)
  have hlist : Summable listTerm := by
    apply Summable.of_norm_bounded hmajor
    intro xz
    simp only [listTerm, listMajor, norm_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_left (norm_nonneg _) (hc xz.1 xz.2))
      (norm_nonneg _)
  let E : List D × List D ≃
      ((Σ i : ℕ, Fin i → D) × (Σ j : ℕ, Fin j → D)) :=
    Equiv.prodCongr List.equivSigmaTuple List.equivSigmaTuple
  let sigmaTerm : ((Σ i : ℕ, Fin i → D) ×
      (Σ j : ℕ, Fin j → D)) → ℂ := fun xz ↦
    c (List.ofFn xz.1.2) (List.ofFn xz.2.2) *
      Sierpinski.finWordMonomial q xz.1.2 *
      Sierpinski.finWordMonomial q xz.2.2
  have hcomp : sigmaTerm ∘ E = listTerm := by
    funext xz
    change c (List.ofFn xz.1.get) (List.ofFn xz.2.get) *
        Sierpinski.finWordMonomial q xz.1.get *
          Sierpinski.finWordMonomial q xz.2.get =
      c xz.1 xz.2 * complexWordWeight q xz.1 * complexWordWeight q xz.2
    rw [List.ofFn_get, List.ofFn_get]
    rw [← complexWordWeight_ofFn q xz.1.get,
      ← complexWordWeight_ofFn q xz.2.get]
    rw [List.ofFn_get, List.ofFn_get]
  have hsigmaPair : Summable sigmaTerm := by
    apply (E.summable_iff).1
    rw [hcomp]
    exact hlist
  let F : ((Σ i : ℕ, Fin i → D) × (Σ j : ℕ, Fin j → D)) ≃
      (Σ ij : ℕ × ℕ, (Fin ij.1 → D) × (Fin ij.2 → D)) := {
    toFun xz := ⟨(xz.1.1, xz.2.1), (xz.1.2, xz.2.2)⟩
    invFun t := (⟨t.1.1, t.2.1⟩, ⟨t.1.2, t.2.2⟩)
    left_inv _ := rfl
    right_inv _ := rfl }
  let fiberTerm : (Σ ij : ℕ × ℕ,
      (Fin ij.1 → D) × (Fin ij.2 → D)) → ℂ := fun t ↦
    c (List.ofFn t.2.1) (List.ofFn t.2.2) *
      Sierpinski.finWordMonomial q t.2.1 *
      Sierpinski.finWordMonomial q t.2.2
  have hF : fiberTerm ∘ F = sigmaTerm := by
    rfl
  have hfiber : Summable fiberTerm := by
    apply (F.summable_iff).1
    rw [hF]
    exact hsigmaPair
  calc
    Sierpinski.boundarySeries c q =
        ∑' ij : ℕ × ℕ, ∑' xz : (Fin ij.1 → D) × (Fin ij.2 → D),
          fiberTerm ⟨ij, xz⟩ := by
      apply tsum_congr
      intro ij
      rw [tsum_fintype]
      simp only [Sierpinski.boundarySeries, Sierpinski.boundaryBidegree]
      rw [Fintype.sum_prod_type]
    _ = ∑' t, fiberTerm t := hfiber.tsum_sigma.symm
    _ = ∑' xz, sigmaTerm xz := F.tsum_eq fiberTerm |>.symm
    _ = ∑' xz, listTerm xz := E.tsum_eq sigmaTerm |>.symm.trans (by
      apply tsum_congr
      intro xz
      exact congrFun hcomp xz)
    _ = ∑' xz : List D × List D,
        c xz.1 xz.2 * complexWordWeight q xz.1 * complexWordWeight q xz.2 := rfl

/-- The complex monomial weight of one fixed-length block. -/
def complexBlockWeight (z : A → ℂ) (h : List A) (c : Fin h.length → A) : ℂ :=
  Sierpinski.finWordMonomial z c

@[simp] theorem finWordMonomial_ofReal (p : A → ℝ) {n : ℕ}
    (x : Fin n → A) :
    Sierpinski.finWordMonomial (fun a ↦ (p a : ℂ)) x =
      (wordWeight (R := ℝ) p (List.ofFn x) : ℂ) := by
  rw [show Sierpinski.finWordMonomial (fun a ↦ (p a : ℂ)) x =
      ∏ k, (p (x k) : ℂ) by rfl, ← Complex.ofReal_prod]
  congr 1
  simp [wordWeight, List.prod_ofFn]

@[simp] theorem complexBlockWeight_ofReal (p : A → ℝ) (h : List A)
    (c : Fin h.length → A) :
    complexBlockWeight (fun a ↦ (p a : ℂ)) h c =
      (blockWeight p h.length c : ℂ) := by
  exact finWordMonomial_ofReal p c

@[simp] theorem complexWordWeight_gapOfSubtypeList
    {h : List A} (q : (Fin h.length → A) → ℂ)
    (x : List (NonMarkerBlock h)) :
    complexWordWeight q (gapOfSubtypeList h x).1 =
      complexWordWeight (fun c : NonMarkerBlock h ↦ q c.1) x := by
  simp [complexWordWeight, gapOfSubtypeList, List.map_map]

/-- On a real nonnegative normalized block law, the finite `ℓ1` mass of
the nonmarker block alphabet is one minus the marker mass. -/
theorem finiteL1Norm_nonMarkerBlock_ofReal
    (p : A → ℝ) (hp : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1)
    (h : List A) :
    Sierpinski.finiteL1Norm
        (fun c : NonMarkerBlock h ↦
          complexBlockWeight (fun a ↦ (p a : ℂ)) h c.1) =
      1 - blockWeight p h.length (endoMarkerBlock h) := by
  classical
  have hpBlock : ∀ c : Fin h.length → A, 0 ≤ blockWeight p h.length c :=
    blockWeight_nonneg p hp h.length
  have hsub :
      (∑ c : NonMarkerBlock h, blockWeight p h.length c.1) =
        ∑ c ∈ (Finset.univ.erase (endoMarkerBlock h)),
          blockWeight p h.length c := by
    exact (Finset.sum_subtype
      (p := fun c : Fin h.length → A ↦ c ≠ endoMarkerBlock h)
      (Finset.univ.erase (endoMarkerBlock h)) (fun c ↦ by simp)
      (fun c ↦ blockWeight p h.length c)).symm
  rw [Sierpinski.finiteL1Norm]
  simp only [complexBlockWeight_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hpBlock _)]
  rw [hsub]
  have herase := Finset.sum_erase_add Finset.univ
    (fun c : Fin h.length → A ↦ blockWeight p h.length c)
    (Finset.mem_univ (endoMarkerBlock h))
  rw [sum_blockWeight_eq_one p hp1 h.length] at herase
  linarith

/-- Strict positivity of the original normalized law puts the induced
nonmarker block vector strictly inside the complex `ℓ1` unit ball. -/
theorem finiteL1Norm_nonMarkerBlock_ofReal_lt_one
    (p : A → ℝ) (hp : ∀ a, 0 < p a) (hp1 : ∑ a, p a = 1)
    (h : List A) :
    Sierpinski.finiteL1Norm
        (fun c : NonMarkerBlock h ↦
          complexBlockWeight (fun a ↦ (p a : ℂ)) h c.1) < 1 := by
  rw [finiteL1Norm_nonMarkerBlock_ofReal p (fun a ↦ (hp a).le) hp1 h]
  have hmarker : 0 < blockWeight p h.length (endoMarkerBlock h) := by
    simp only [blockWeight, wordWeight]
    induction List.ofFn (endoMarkerBlock h) with
    | nil => simp
    | cons a w ih =>
        simp only [List.map_cons, List.prod_cons]
        exact mul_pos (hp a) ih
  linarith

/-- Boundary coefficient attached to two words on the nonmarker block
alphabet. -/
def rationalBoundarySeriesCoefficient (h : List A)
    (m : (s : Fin h.length) → (Fin (s : ℕ) → A) →
      GapWords (endoMarkerBlock h) × GapWords (endoMarkerBlock h) → ℚ)
    (s : Fin h.length) (xi : Fin (s : ℕ) → A)
    (x y : List (NonMarkerBlock h)) : ℂ :=
  (m s xi (gapOfSubtypeList h x, gapOfSubtypeList h y) : ℂ)

/-- Reindexing the analytic boundary series by actual marker-free block
gaps. -/
theorem rationalBoundarySeries_eq_gapPair_tsum (h : List A)
    (m : (s : Fin h.length) → (Fin (s : ℕ) → A) →
      GapWords (endoMarkerBlock h) × GapWords (endoMarkerBlock h) → ℚ)
    (hm : ∀ s xi i, (m s xi i : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (s : Fin h.length) (xi : Fin (s : ℕ) → A)
    (q : (Fin h.length → A) → ℂ)
    (hq : Sierpinski.finiteL1Norm
      (fun c : NonMarkerBlock h ↦ q c.1) < 1) :
    Sierpinski.boundarySeries (rationalBoundarySeriesCoefficient h m s xi)
        (fun c : NonMarkerBlock h ↦ q c.1) =
      ∑' i : GapWords (endoMarkerBlock h) × GapWords (endoMarkerBlock h),
        (m s xi i : ℂ) * complexWordWeight q i.1.1 *
          complexWordWeight q i.2.1 := by
  classical
  have hc : ∀ x z, ‖rationalBoundarySeriesCoefficient h m s xi x z‖ ≤ 1 := by
    intro x z
    have hb := hm s xi (gapOfSubtypeList h x, gapOfSubtypeList h z)
    change ‖(m s xi (gapOfSubtypeList h x, gapOfSubtypeList h z) : ℂ)‖ ≤ 1
    rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hb.1]
    exact hb.2
  rw [boundarySeries_eq_tsum_listPair _ hc _ hq]
  let E : List (NonMarkerBlock h) × List (NonMarkerBlock h) ≃
      GapWords (endoMarkerBlock h) × GapWords (endoMarkerBlock h) :=
    Equiv.prodCongr (nonMarkerListEquivGap h) (nonMarkerListEquivGap h)
  rw [← E.tsum_eq (fun i : GapWords (endoMarkerBlock h) ×
      GapWords (endoMarkerBlock h) ↦
    (m s xi i : ℂ) * complexWordWeight q i.1.1 * complexWordWeight q i.2.1)]
  apply tsum_congr
  intro xz
  change (m s xi (gapOfSubtypeList h xz.1, gapOfSubtypeList h xz.2) : ℂ) *
      complexWordWeight (fun c : NonMarkerBlock h ↦ q c.1) xz.1 *
        complexWordWeight (fun c : NonMarkerBlock h ↦ q c.1) xz.2 =
    (m s xi (gapOfSubtypeList h xz.1, gapOfSubtypeList h xz.2) : ℂ) *
      complexWordWeight q (gapOfSubtypeList h xz.1).1 *
        complexWordWeight q (gapOfSubtypeList h xz.2).1
  rw [complexWordWeight_gapOfSubtypeList,
    complexWordWeight_gapOfSubtypeList]

/-- At a positive real law, the marker-square times the analytic boundary
series is exactly the complexification of the corresponding boundary-weight
mixture. -/
theorem marker_sq_mul_rationalBoundarySeries_ofReal (h : List A)
    (m : (s : Fin h.length) → (Fin (s : ℕ) → A) →
      GapWords (endoMarkerBlock h) × GapWords (endoMarkerBlock h) → ℚ)
    (hm : ∀ s xi i, (m s xi i : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (s : Fin h.length) (xi : Fin (s : ℕ) → A)
    (p : A → ℝ) (hp : ∀ a, 0 < p a) (hp1 : ∑ a, p a = 1) :
    complexBlockWeight (fun a ↦ (p a : ℂ)) h (endoMarkerBlock h) ^ 2 *
        Sierpinski.boundarySeries (rationalBoundarySeriesCoefficient h m s xi)
          (fun c : NonMarkerBlock h ↦
            complexBlockWeight (fun a ↦ (p a : ℂ)) h c.1) =
      ((∑' i : GapWords (endoMarkerBlock h) × GapWords (endoMarkerBlock h),
        moduleBoundaryWeight (blockWeight p h.length) (endoMarkerBlock h) i *
          (m s xi i : ℝ)) : ℂ) := by
  let q : (Fin h.length → A) → ℂ := fun c ↦
    complexBlockWeight (fun a ↦ (p a : ℂ)) h c
  have hq : Sierpinski.finiteL1Norm
      (fun c : NonMarkerBlock h ↦ q c.1) < 1 :=
    finiteL1Norm_nonMarkerBlock_ofReal_lt_one p hp hp1 h
  rw [rationalBoundarySeries_eq_gapPair_tsum h m hm s xi q hq]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro i
  simp only [q, complexBlockWeight_ofReal]
  rw [show complexWordWeight
      (fun c ↦ (blockWeight p h.length c : ℂ)) i.1.1 =
      (wordWeight (R := ℝ) (blockWeight p h.length) i.1.1 : ℂ) by
        exact complexWordWeight_ofReal (blockWeight p h.length) i.1.1,
    show complexWordWeight
      (fun c ↦ (blockWeight p h.length c : ℂ)) i.2.1 =
      (wordWeight (R := ℝ) (blockWeight p h.length) i.2.1 : ℂ) by
        exact complexWordWeight_ofReal (blockWeight p h.length) i.2.1]
  simp only [moduleBoundaryWeight, Complex.ofReal_ratCast]
  push_cast
  ring

/-- Complex extension of the rational boundary-density formula. -/
def rationalBoundaryComplexExpression (h : List A)
    (m : (s : Fin h.length) → (Fin (s : ℕ) → A) →
      GapWords (endoMarkerBlock h) × GapWords (endoMarkerBlock h) → ℚ)
    (z : A → ℂ) : ℂ :=
  (∑ s : Fin h.length, ∑ xi : Fin (s : ℕ) → A,
    Sierpinski.finWordMonomial z xi *
      (complexBlockWeight z h (endoMarkerBlock h) ^ 2 *
        Sierpinski.boundarySeries (rationalBoundarySeriesCoefficient h m s xi)
          (fun c : NonMarkerBlock h ↦ complexBlockWeight z h c.1))) /
    (h.length : ℂ)

/-- The complex boundary expression restricts to the actual rational word
boundary density on every positive normalized real law. -/
theorem rationalBoundaryComplexExpression_ofReal (h : List A) (hh : h ≠ [])
    (m : (s : Fin h.length) → (Fin (s : ℕ) → A) →
      GapWords (endoMarkerBlock h) × GapWords (endoMarkerBlock h) → ℚ)
    (hm : ∀ s xi i, (m s xi i : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (p : A → ℝ) (hp : ∀ a, 0 < p a) (hp1 : ∑ a, p a = 1) :
    rationalBoundaryComplexExpression h m (fun a ↦ (p a : ℂ)) =
      (rationalWordBoundaryDensity h m p : ℂ) := by
  classical
  unfold rationalBoundaryComplexExpression rationalWordBoundaryDensity
  simp_rw [finWordMonomial_ofReal]
  simp_rw [marker_sq_mul_rationalBoundarySeries_ofReal h m hm _ _ p hp hp1]
  push_cast
  simp only [Complex.ofReal_ratCast]

end IndependentZeroBlocks
