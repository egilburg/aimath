import FiniteMonoidMortality.FiniteMortalityCompression

set_option autoImplicit false

namespace FiniteMonoidMortality

theorem quadratic_three_roots {a b c x y z : ℝ} (ha : a ≠ 0)
    (hx : a*x^2+b*x+c=0) (hy : a*y^2+b*y+c=0) (hz : a*z^2+b*z+c=0) :
    x=y ∨ x=z ∨ y=z := by
  by_cases hxy : x=y
  · exact Or.inl hxy
  by_cases hxz : x=z
  · exact Or.inr (Or.inl hxz)
  have h1 : a*(x+y)+b=0 := by
    have hp : (x-y)*(a*(x+y)+b)=0 := by nlinarith
    exact (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr hxy)
  have h2 : a*(x+z)+b=0 := by
    have hp : (x-z)*(a*(x+z)+b)=0 := by nlinarith
    exact (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr hxz)
  right; right
  have hp : a*(y-z)=0 := by nlinarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left ha)

def planeQuad (a b c : ℝ) (x : Fin 2 → ℝ) : ℝ :=
  a*(x 0)^2+b*x 0*x 1+c*(x 1)^2

theorem planeQuad_line_three_of_first_ne_zero
    (a b c p q level : ℝ) (hp : p ≠ 0)
    (hpos : ∀ x : Fin 2 → ℝ, x ≠ 0 → 0 < planeQuad a b c x)
    (x y z : Fin 2 → ℝ)
    (hx : p*x 0+q*x 1=1) (hy : p*y 0+q*y 1=1) (hz : p*z 0+q*z 1=1)
    (hqx : planeQuad a b c x=level) (hqy : planeQuad a b c y=level)
    (hqz : planeQuad a b c z=level) : x=y ∨ x=z ∨ y=z := by
  let d : Fin 2 → ℝ := ![-q,p]
  have hd : d ≠ 0 := by
    intro he
    have := congrFun he 1
    exact hp (by simpa [d] using this)
  have hlead : 0 < a*q^2-b*p*q+c*p^2 := by
    have hh := hpos d hd
    dsimp [planeQuad,d] at hh
    nlinarith
  have hroot (w : Fin 2 → ℝ) (hw : p*w 0+q*w 1=1)
      (hqw : planeQuad a b c w=level) :
      (a*q^2-b*p*q+c*p^2)*(w 1)^2+(b*p-2*a*q)*w 1+(a-level*p^2)=0 := by
    have h0 : p*w 0=1-q*w 1 := by linarith
    have hi : p^2 * planeQuad a b c w =
        a*(1-q*w 1)^2+b*p*(1-q*w 1)*w 1+c*p^2*(w 1)^2 := by
      calc
        _ = a*(p*w 0)^2+b*p*(p*w 0)*w 1+c*p^2*(w 1)^2 := by unfold planeQuad; ring
        _ = _ := by rw [h0]
    rw [hqw] at hi
    nlinarith [hi]
  have heq (u v : Fin 2 → ℝ) (hu : p*u 0+q*u 1=1) (hv : p*v 0+q*v 1=1)
      (he : u 1=v 1) : u=v := by
    have h0 : u 0=v 0 := (mul_left_cancel₀ hp) (by rw [he] at hu; linarith)
    ext i; fin_cases i <;> assumption
  rcases quadratic_three_roots (ne_of_gt hlead) (hroot x hx hqx)
    (hroot y hy hqy) (hroot z hz hqz) with h | h | h
  · exact Or.inl (heq x y hx hy h)
  · exact Or.inr (Or.inl (heq x z hx hz h))
  · exact Or.inr (Or.inr (heq y z hy hz h))

theorem planeQuad_line_three
    (a b c p q level : ℝ) (hv : p ≠ 0 ∨ q ≠ 0)
    (hpos : ∀ x : Fin 2 → ℝ, x ≠ 0 → 0 < planeQuad a b c x)
    (x y z : Fin 2 → ℝ)
    (hx : p*x 0+q*x 1=1) (hy : p*y 0+q*y 1=1) (hz : p*z 0+q*z 1=1)
    (hqx : planeQuad a b c x=level) (hqy : planeQuad a b c y=level)
    (hqz : planeQuad a b c z=level) : x=y ∨ x=z ∨ y=z := by
  by_cases hp : p ≠ 0
  · exact planeQuad_line_three_of_first_ne_zero a b c p q level hp hpos x y z hx hy hz hqx hqy hqz
  have hp0 : p=0 := not_ne_iff.mp hp
  have hq : q ≠ 0 := hv.resolve_left hp
  have hxy1 : x 1=y 1 := (mul_left_cancel₀ hq) (by simp [hp0] at hx hy; linarith)
  have hxz1 : x 1=z 1 := (mul_left_cancel₀ hq) (by simp [hp0] at hx hz; linarith)
  have ha : a ≠ 0 := by
    have hh := hpos ![1,0] (by intro he; have := congrFun he 0; norm_num at this)
    simpa [planeQuad] using ne_of_gt hh
  have rx : a*(x 0)^2+(b*x 1)*x 0+(c*(x 1)^2-level)=0 := by dsimp [planeQuad] at hqx; nlinarith
  have ry : a*(y 0)^2+(b*x 1)*y 0+(c*(x 1)^2-level)=0 := by dsimp [planeQuad] at hqy; rw [← hxy1] at hqy; nlinarith
  have rz : a*(z 0)^2+(b*x 1)*z 0+(c*(x 1)^2-level)=0 := by dsimp [planeQuad] at hqz; rw [← hxz1] at hqz; nlinarith
  rcases quadratic_three_roots ha rx ry rz with h | h | h
  · left; ext i; fin_cases i <;> assumption
  · right; left; ext i; fin_cases i <;> assumption
  · right; right; ext i; fin_cases i
    · exact h
    · exact hxy1.symm.trans hxz1

def planeDet (x y : Fin 2 → ℝ) := x 0*y 1-x 1*y 0

theorem planeDet_smul (s t : ℝ) (x y : Fin 2 → ℝ) :
    planeDet (s • x) (t • y)=s*t*planeDet x y := by simp [planeDet]; ring

theorem planeQuad_smul (a b c s : ℝ) (x : Fin 2 → ℝ) :
    planeQuad a b c (s • x)=s^2*planeQuad a b c x := by simp [planeQuad]; ring

theorem planeDet_zero_of_same_zero_line (p q : ℝ) (hv : p ≠ 0 ∨ q ≠ 0)
    (x y : Fin 2 → ℝ) (hx : p*x 0+q*x 1=0) (hy : p*y 0+q*y 1=0) : planeDet x y=0 := by
  rcases hv with hp | hq
  · have he : p*planeDet x y=0 := by dsimp [planeDet]; nlinarith [congrArg (fun r : ℝ => r*y 1) hx, congrArg (fun r : ℝ => r*x 1) hy]
    exact (mul_eq_zero.mp he).resolve_left hp
  · have he : q*planeDet x y=0 := by dsimp [planeDet]; nlinarith [congrArg (fun r : ℝ => r*y 0) hx, congrArg (fun r : ℝ => r*x 0) hy]
    exact (mul_eq_zero.mp he).resolve_left hq

def planeLine (p q : ℝ) (x : Fin 2 → ℝ) : ℝ := p*x 0+q*x 1

theorem planeQuad_signed_line_three
    (a b c p q level : ℝ) (hv : p ≠ 0 ∨ q ≠ 0)
    (hpos : ∀ x : Fin 2 → ℝ, x ≠ 0 → 0 < planeQuad a b c x)
    (x y z : Fin 2 → ℝ)
    (hx : planeLine p q x=1 ∨ planeLine p q x= -1)
    (hy : planeLine p q y=1 ∨ planeLine p q y= -1)
    (hz : planeLine p q z=1 ∨ planeLine p q z= -1)
    (hqx : planeQuad a b c x=level) (hqy : planeQuad a b c y=level)
    (hqz : planeQuad a b c z=level) :
    planeDet x y=0 ∨ planeDet x z=0 ∨ planeDet y z=0 := by
  let norm (w : Fin 2 → ℝ) := (planeLine p q w) • w
  have hn (w : Fin 2 → ℝ) (hw : planeLine p q w=1 ∨ planeLine p q w= -1) :
      planeLine p q (norm w)=1 ∧ planeQuad a b c (norm w)=planeQuad a b c w := by
    have hl : planeLine p q (norm w)=(planeLine p q w)^2 := by dsimp [norm,planeLine]; ring
    constructor
    · rw [hl]; rcases hw with hw | hw <;> simp [hw]
    · dsimp [norm]
      rw [planeQuad_smul]
      rcases hw with hw | hw <;> simp [hw]
  have hnxy (u v : Fin 2 → ℝ)
      (hu : planeLine p q u=1 ∨ planeLine p q u= -1)
      (hv : planeLine p q v=1 ∨ planeLine p q v= -1)
      (he : norm u=norm v) : planeDet u v=0 := by
    have hh : planeDet (norm u) (norm v)=0 := by rw [he]; simp only [planeDet]; ring
    dsimp [norm] at hh
    rw [planeDet_smul] at hh
    rcases hu with hu | hu <;> rcases hv with hv | hv <;> simpa [hu,hv] using hh
  obtain ⟨hx1,hxq⟩ := hn x hx
  obtain ⟨hy1,hyq⟩ := hn y hy
  obtain ⟨hz1,hzq⟩ := hn z hz
  rcases planeQuad_line_three a b c p q level hv hpos (norm x) (norm y) (norm z)
    hx1 hy1 hz1 (hxq.trans hqx) (hyq.trans hqy) (hzq.trans hqz) with h | h | h
  · exact Or.inl (hnxy x y hx hy h)
  · exact Or.inr (Or.inl (hnxy x z hx hz h))
  · exact Or.inr (Or.inr (hnxy y z hy hz h))

theorem planeQuad_quantized_four
    (a b c p q level : ℝ) (hv : p ≠ 0 ∨ q ≠ 0)
    (hpos : ∀ x : Fin 2 → ℝ, x ≠ 0 → 0 < planeQuad a b c x)
    (x y z t : Fin 2 → ℝ)
    (hx : planeLine p q x=0 ∨ planeLine p q x=1 ∨ planeLine p q x= -1)
    (hy : planeLine p q y=0 ∨ planeLine p q y=1 ∨ planeLine p q y= -1)
    (hz : planeLine p q z=0 ∨ planeLine p q z=1 ∨ planeLine p q z= -1)
    (ht : planeLine p q t=0 ∨ planeLine p q t=1 ∨ planeLine p q t= -1)
    (hqx : planeQuad a b c x=level) (hqy : planeQuad a b c y=level)
    (hqz : planeQuad a b c z=level) (hqt : planeQuad a b c t=level) :
    planeDet x y=0 ∨ planeDet x z=0 ∨ planeDet x t=0 ∨
      planeDet y z=0 ∨ planeDet y t=0 ∨ planeDet z t=0 := by
  by_contra h
  push Not at h
  obtain ⟨hxy,hxz,hxt,hyz,hyt,hzt⟩ := h
  have zeroPair := planeDet_zero_of_same_zero_line p q hv
  have triple := planeQuad_signed_line_three a b c p q level hv hpos
  by_cases hx0 : planeLine p q x=0
  · have hy0 : planeLine p q y ≠ 0 := fun hy0 => hxy (zeroPair x y hx0 hy0)
    have hz0 : planeLine p q z ≠ 0 := fun hz0 => hxz (zeroPair x z hx0 hz0)
    have ht0 : planeLine p q t ≠ 0 := fun ht0 => hxt (zeroPair x t hx0 ht0)
    rcases triple y z t (hy.resolve_left hy0) (hz.resolve_left hz0) (ht.resolve_left ht0) hqy hqz hqt with h | h | h
    · exact hyz h
    · exact hyt h
    · exact hzt h
  by_cases hy0 : planeLine p q y=0
  · have hz0 : planeLine p q z ≠ 0 := fun hz0 => hyz (zeroPair y z hy0 hz0)
    have ht0 : planeLine p q t ≠ 0 := fun ht0 => hyt (zeroPair y t hy0 ht0)
    rcases triple x z t (hx.resolve_left hx0) (hz.resolve_left hz0) (ht.resolve_left ht0) hqx hqz hqt with h | h | h
    · exact hxz h
    · exact hxt h
    · exact hzt h
  by_cases hz0 : planeLine p q z=0
  · have ht0 : planeLine p q t ≠ 0 := fun ht0 => hzt (zeroPair z t hz0 ht0)
    rcases triple x y t (hx.resolve_left hx0) (hy.resolve_left hy0) (ht.resolve_left ht0) hqx hqy hqt with h | h | h
    · exact hxy h
    · exact hxt h
    · exact hyt h
  rcases triple x y z (hx.resolve_left hx0) (hy.resolve_left hy0) (hz.resolve_left hz0) hqx hqy hqz with h | h | h
  · exact hxy h
  · exact hxz h
  · exact hyz h

end FiniteMonoidMortality
