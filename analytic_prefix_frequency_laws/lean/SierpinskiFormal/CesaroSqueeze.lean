import Mathlib.Topology.UniformSpace.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false

namespace SierpinskiFormal

open Filter Topology

/-- A real sequence converges if, at every positive scale, it is eventually
trapped between two convergent sequences whose limits are closer than that
scale.  The bounding sequences and their limits may depend on the scale. -/
theorem exists_tendsto_of_arbitrarily_tight_eventual_bounds
    (f : ℕ → ℝ)
    (hbound : ∀ ε > 0, ∃ (g h : ℕ → ℝ) (l u : ℝ),
      Tendsto g atTop (𝓝 l) ∧
      Tendsto h atTop (𝓝 u) ∧
      u - l < ε ∧
      ∀ᶠ n in atTop, g n ≤ f n ∧ f n ≤ h n) :
    ∃ a : ℝ, Tendsto f atTop (𝓝 a) := by
  apply cauchySeq_tendsto_of_complete
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨g, h, l, u, hg, hh, hlu, hgf⟩ := hbound (ε / 3) (by positivity)
  obtain ⟨Ng, hNg⟩ := (Metric.tendsto_atTop.mp hg) (ε / 3) (by positivity)
  obtain ⟨Nh, hNh⟩ := (Metric.tendsto_atTop.mp hh) (ε / 3) (by positivity)
  obtain ⟨Nb, hNb⟩ := eventually_atTop.mp hgf
  refine ⟨max Ng (max Nh Nb), fun m hm n hn ↦ ?_⟩
  have hmg := hNg m (le_trans (le_max_left _ _) hm)
  have hmh := hNh m ((le_max_left Nh Nb).trans ((le_max_right Ng _).trans hm))
  have hmb := hNb m ((le_max_right Nh Nb).trans ((le_max_right Ng _).trans hm))
  have hng := hNg n (le_trans (le_max_left _ _) hn)
  have hnh := hNh n ((le_max_left Nh Nb).trans ((le_max_right Ng _).trans hn))
  have hnb := hNb n ((le_max_right Nh Nb).trans ((le_max_right Ng _).trans hn))
  rw [Real.dist_eq]
  rw [abs_lt]
  constructor <;> linarith [abs_lt.mp (by simpa [Real.dist_eq] using hmg),
    abs_lt.mp (by simpa [Real.dist_eq] using hmh),
    abs_lt.mp (by simpa [Real.dist_eq] using hng),
    abs_lt.mp (by simpa [Real.dist_eq] using hnh)]

end SierpinskiFormal
