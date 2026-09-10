import FiniteMonoidMortality.MinimalRankCompression
import FiniteMonoidMortality.PlaneEllipse
import FiniteMonoidMortality.RankOneTrace

set_option autoImplicit false

noncomputable section

namespace FiniteMonoidMortality

theorem exists_outer_of_two_nonunit
    (K : Matrix (Fin 2) (Fin 2) ℝ) (hK : K ≠ 0) (hu : ¬ IsUnit K) :
    ∃ u v : Fin 2 → ℝ, u ≠ 0 ∧ v ≠ 0 ∧ K=Matrix.vecMulVec u v := by
  have hr : K.rank=1 := by
    have hp := rank_pos_of_ne_zero K hK
    have hl := Matrix.rank_le_card_width K
    simp only [Fintype.card_fin] at hl
    have hn : K.rank ≠ 2 := fun he => hu (isUnit_of_rank_eq_card K (by simpa using he))
    omega
  have hh := exists_rankFactorization K
  rw [hr] at hh
  obtain ⟨U,V,hfac⟩ := hh
  have he : K=Matrix.vecMulVec (fun i => U i 0) (fun j => V 0 j) := by
    rw [hfac]
    ext i j
    simp [Matrix.mul_apply, Fin.sum_univ_one, Matrix.vecMulVec]
  refine ⟨_,_,?_,?_,he⟩
  · intro hz; apply hK; rw [he,hz]; simp
  · intro hz; apply hK; rw [he,hz]; simp

theorem two_nonunit_sandwich_zero
    (A K B : Matrix (Fin 2) (Fin 2) ℝ) (hK : K ≠ 0) (hu : ¬ IsUnit K)
    (hz : A*K*B=0) : A*K=0 ∨ K*B=0 := by
  obtain ⟨u,v,_,_,he⟩ := exists_outer_of_two_nonunit K hK hu
  rw [he, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMulVec_eq_zero] at hz
  rcases hz with h | h
  · left; rw [he, Matrix.mul_vecMulVec,h]; simp
  · right; rw [he, Matrix.vecMulVec_mul,h]; simp

theorem planeDet_zero_iff_smul (x y : Fin 2 → ℝ) (hx : x ≠ 0) :
    planeDet x y=0 ↔ ∃ s : ℝ, y=s • x := by
  constructor
  · intro hd
    by_cases h0 : x 0 ≠ 0
    · refine ⟨y 0/x 0, ?_⟩
      ext i; fin_cases i
      · simp [div_mul_cancel₀ _ h0]
      · dsimp [planeDet] at hd
        simp only [Pi.smul_apply, smul_eq_mul]
        apply (mul_left_cancel₀ h0)
        field_simp
        exact (sub_eq_zero.mp hd).trans (mul_comm _ _)
    · have h1 : x 1 ≠ 0 := by
        intro he; apply hx; ext i; fin_cases i <;> simp_all
      refine ⟨y 1/x 1, ?_⟩
      have hy0 : y 0=0 := by dsimp [planeDet] at hd; simp only [not_ne_iff.mp h0,zero_mul,zero_sub,neg_eq_zero] at hd; exact (mul_eq_zero.mp hd).resolve_left h1
      ext i; fin_cases i
      · simp [not_ne_iff.mp h0,hy0]
      · simp [div_mul_cancel₀ _ h1]
  · rintro ⟨s,rfl⟩
    simp [planeDet]; ring

theorem mulVec_zero_of_planeDet_zero
    (A : Matrix (Fin 2) (Fin 2) ℝ) (x y : Fin 2 → ℝ)
    (hx : x ≠ 0) (hxy : planeDet x y=0) (hz : A.mulVec x=0) : A.mulVec y=0 := by
  obtain ⟨s,rfl⟩ := (planeDet_zero_iff_smul x y hx).mp hxy
  simp [Matrix.mulVec_smul,hz]

end FiniteMonoidMortality
