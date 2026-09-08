import SierpinskiFormal.BooleanDoubleLimit
import Mathlib.Topology.Sequences

set_option autoImplicit false

namespace IndependentZeroBlocks

open Filter Topology

/-- The usual embedding of a Boolean truth value as a real support
indicator. -/
def boolIndicator (b : Bool) : ℝ := if b then 1 else 0

theorem boolIndicator_injective : Function.Injective boolIndicator := by
  intro a b h
  cases a <;> cases b <;> simp [boolIndicator] at h ⊢

/-- The sequential real double-limit property for a Boolean kernel. -/
def HasBooleanDoubleLimitProperty {X Y : Type*} (f : X → Y → Bool) : Prop :=
  ∀ (x : ℕ → X) (y : ℕ → Y) (rowLimit columnLimit : ℕ → ℝ)
      (rowOuter columnOuter : ℝ),
    (∀ i, Tendsto (fun j ↦ boolIndicator (f (x i) (y j)))
      atTop (nhds (rowLimit i))) →
    (∀ j, Tendsto (fun i ↦ boolIndicator (f (x i) (y j)))
      atTop (nhds (columnLimit j))) →
    Tendsto rowLimit atTop (nhds rowOuter) →
    Tendsto columnLimit atTop (nhds columnOuter) →
    rowOuter = columnOuter

/-- A finite Boolean combination of Boolean kernels. -/
def booleanCombine {X Y : Type*} {d : ℕ} (op : (Fin d → Bool) → Bool)
    (f : Fin d → X → Y → Bool) : X → Y → Bool :=
  fun i j ↦ op (fun k ↦ f k i j)

/-- Finite Boolean combinations preserve the actual sequential double-limit
property. No component limits are assumed: a common compact subsequence of
all row and column profiles constructs them simultaneously. -/
theorem hasBooleanDoubleLimitProperty_booleanCombine
    {X Y : Type*} {d : ℕ} (op : (Fin d → Bool) → Bool)
    (f : Fin d → X → Y → Bool)
    (hf : ∀ k, HasBooleanDoubleLimitProperty (f k)) :
    HasBooleanDoubleLimitProperty (booleanCombine op f) := by
  classical
  intro x y rowLimit columnLimit rowOuter columnOuter
    hrow hcolumn hrowOuter hcolumnOuter
  let F : Fin d → ℕ → ℕ → Bool := fun k i j ↦ f k (x i) (y j)
  have hrowF : ∀ i, Tendsto
      (fun j ↦ boolIndicator (op (fun k ↦ F k i j))) atTop
      (nhds (rowLimit i)) := by
    simpa [F, booleanCombine] using hrow
  have hcolumnF : ∀ j, Tendsto
      (fun i ↦ boolIndicator (op (fun k ↦ F k i j))) atTop
      (nhds (columnLimit j)) := by
    simpa [F, booleanCombine] using hcolumn
  let Profile := (ℕ × Fin d) → Bool × Bool
  let profile : ℕ → Profile := fun m z ↦
    (F z.2 z.1 m, F z.2 m z.1)
  obtain ⟨profileLimit, p, hp, hprofile⟩ :=
    CompactSpace.tendsto_subseq profile
  let colors : ℕ → (Fin d → Bool × Bool) := fun r k ↦
    profileLimit (p r, k)
  obtain ⟨outerColors, q, hq, hcolors⟩ :=
    CompactSpace.tendsto_subseq colors
  let s : ℕ → ℕ := p ∘ q
  have hs : StrictMono s := hp.comp hq
  have hsTop : Tendsto s atTop atTop := hs.tendsto_atTop
  have hprofileAt (m : ℕ) (k : Fin d) :
      Tendsto (fun n ↦ (F k m (p n), F k (p n) m)) atTop
        (nhds (profileLimit (m, k))) := by
    simpa [profile, Profile, Function.comp_def] using
      ((continuous_apply (m, k)).tendsto profileLimit).comp hprofile
  have hcolorsAt (k : Fin d) :
      Tendsto (fun r ↦ colors (q r) k) atTop (nhds (outerColors k)) := by
    simpa [Function.comp_def] using
      ((continuous_apply k).tendsto outerColors).comp hcolors
  have hcomponentOuter (k : Fin d) :
      boolIndicator (outerColors k).1 = boolIndicator (outerColors k).2 := by
    apply hf k (x ∘ s) (y ∘ s)
      (fun r ↦ boolIndicator (colors (q r) k).1)
      (fun r ↦ boolIndicator (colors (q r) k).2)
      (boolIndicator (outerColors k).1)
      (boolIndicator (outerColors k).2)
    · intro r
      have hpq := (hprofileAt (s r) k).comp hq.tendsto_atTop
      have hfst : Tendsto (fun n ↦ F k (s r) (s n)) atTop
          (nhds (colors (q r) k).1) := by
        simpa [s, colors, Function.comp_def] using
          ((continuous_fst.tendsto (profileLimit (s r, k))).comp hpq)
      exact (continuous_of_discreteTopology (f := boolIndicator)).tendsto
        (colors (q r) k).1 |>.comp hfst
    · intro r
      have hpq := (hprofileAt (s r) k).comp hq.tendsto_atTop
      have hsnd : Tendsto (fun n ↦ F k (s n) (s r)) atTop
          (nhds (colors (q r) k).2) := by
        simpa [s, colors, Function.comp_def] using
          ((continuous_snd.tendsto (profileLimit (s r, k))).comp hpq)
      exact (continuous_of_discreteTopology (f := boolIndicator)).tendsto
        (colors (q r) k).2 |>.comp hsnd
    · exact (continuous_of_discreteTopology (f := fun z : Bool × Bool ↦
        boolIndicator z.1)).tendsto (outerColors k) |>.comp (hcolorsAt k)
    · exact (continuous_of_discreteTopology (f := fun z : Bool × Bool ↦
        boolIndicator z.2)).tendsto (outerColors k) |>.comp (hcolorsAt k)
  have houterColors : (fun k ↦ (outerColors k).1) =
      (fun k ↦ (outerColors k).2) := by
    funext k
    exact boolIndicator_injective (hcomponentOuter k)
  have hrowInnerVector (r : ℕ) :
      Tendsto (fun n k ↦ F k (s r) (s n)) atTop
        (nhds (fun k ↦ (colors (q r) k).1)) := by
    rw [tendsto_pi_nhds]
    intro k
    have hpq := (hprofileAt (s r) k).comp hq.tendsto_atTop
    simpa [s, colors, Function.comp_def] using
      ((continuous_fst.tendsto (profileLimit (s r, k))).comp hpq)
  have hcolumnInnerVector (r : ℕ) :
      Tendsto (fun n k ↦ F k (s n) (s r)) atTop
        (nhds (fun k ↦ (colors (q r) k).2)) := by
    rw [tendsto_pi_nhds]
    intro k
    have hpq := (hprofileAt (s r) k).comp hq.tendsto_atTop
    simpa [s, colors, Function.comp_def] using
      ((continuous_snd.tendsto (profileLimit (s r, k))).comp hpq)
  have hrowRestricted (r : ℕ) :
      Tendsto (fun n ↦ boolIndicator (op (fun k ↦ F k (s r) (s n))))
        atTop (nhds (boolIndicator (op (fun k ↦ (colors (q r) k).1)))) := by
    exact (continuous_of_discreteTopology
      (f := fun v : Fin d → Bool ↦ boolIndicator (op v))).tendsto _ |>.comp
        (hrowInnerVector r)
  have hcolumnRestricted (r : ℕ) :
      Tendsto (fun n ↦ boolIndicator (op (fun k ↦ F k (s n) (s r))))
        atTop (nhds (boolIndicator (op (fun k ↦ (colors (q r) k).2)))) := by
    exact (continuous_of_discreteTopology
      (f := fun v : Fin d → Bool ↦ boolIndicator (op v))).tendsto _ |>.comp
        (hcolumnInnerVector r)
  have hrowIdentify (r : ℕ) : rowLimit (s r) =
      boolIndicator (op (fun k ↦ (colors (q r) k).1)) := by
    apply tendsto_nhds_unique ((hrowF (s r)).comp hsTop) (hrowRestricted r)
  have hcolumnIdentify (r : ℕ) : columnLimit (s r) =
      boolIndicator (op (fun k ↦ (colors (q r) k).2)) := by
    apply tendsto_nhds_unique ((hcolumnF (s r)).comp hsTop) (hcolumnRestricted r)
  have hrowColorsOuter :
      Tendsto (fun r ↦ boolIndicator (op (fun k ↦ (colors (q r) k).1)))
        atTop (nhds (boolIndicator (op (fun k ↦ (outerColors k).1)))) := by
    have hv : Tendsto (fun r k ↦ (colors (q r) k).1) atTop
        (nhds (fun k ↦ (outerColors k).1)) := by
      rw [tendsto_pi_nhds]
      intro k
      exact (continuous_fst.tendsto (outerColors k)).comp (hcolorsAt k)
    exact (continuous_of_discreteTopology
      (f := fun v : Fin d → Bool ↦ boolIndicator (op v))).tendsto _ |>.comp hv
  have hcolumnColorsOuter :
      Tendsto (fun r ↦ boolIndicator (op (fun k ↦ (colors (q r) k).2)))
        atTop (nhds (boolIndicator (op (fun k ↦ (outerColors k).2)))) := by
    have hv : Tendsto (fun r k ↦ (colors (q r) k).2) atTop
        (nhds (fun k ↦ (outerColors k).2)) := by
      rw [tendsto_pi_nhds]
      intro k
      exact (continuous_snd.tendsto (outerColors k)).comp (hcolorsAt k)
    exact (continuous_of_discreteTopology
      (f := fun v : Fin d → Bool ↦ boolIndicator (op v))).tendsto _ |>.comp hv
  have hrowOuterValue : rowOuter =
      boolIndicator (op (fun k ↦ (outerColors k).1)) := by
    apply tendsto_nhds_unique (hrowOuter.comp hsTop)
    exact hrowColorsOuter.congr' (Filter.Eventually.of_forall fun r ↦
      (hrowIdentify r).symm)
  have hcolumnOuterValue : columnOuter =
      boolIndicator (op (fun k ↦ (outerColors k).2)) := by
    apply tendsto_nhds_unique (hcolumnOuter.comp hsTop)
    exact hcolumnColorsOuter.congr' (Filter.Eventually.of_forall fun r ↦
      (hcolumnIdentify r).symm)
  rw [hrowOuterValue, hcolumnOuterValue, houterColors]

/-- The Boolean test that a scalar is nonzero. -/
noncomputable def nonzeroBool {K : Type*} [Zero K] (z : K) : Bool := by
  classical
  exact if z = 0 then false else true

@[simp] theorem boolIndicator_nonzeroBool
    {K : Type*} [Zero K] (z : K) :
    boolIndicator (nonzeroBool z) = nonzeroIndicator z := by
  classical
  by_cases hz : z = 0 <;>
    simp [nonzeroBool, nonzeroIndicator, boolIndicator, hz]

/-- Boolean support kernel of a finite matrix-word coefficient. -/
noncomputable def matrixWordsNonzeroBool
    {K ι : Type*} [CommRing K] [Fintype ι]
    {b : ℕ} (M : Fin b → Matrix ι ι K) (u a : ι → K) :
    List (Fin b) → List (Fin b) → Bool :=
  fun x y ↦ nonzeroBool
    (coordinateRowDual a
      (linearWord (fun r ↦ Matrix.mulVecLin (M r)) (x ++ y) u))

/-- Every finite matrix-word support kernel over an arbitrary commutative
ring has the hereditary Boolean double-limit property used by the closure
theorem. -/
theorem matrixWordsNonzeroBool_hasBooleanDoubleLimitProperty
    {K ι : Type*} [CommRing K] [Fintype ι]
    {b : ℕ} (M : Fin b → Matrix ι ι K) (u a : ι → K) :
    HasBooleanDoubleLimitProperty (matrixWordsNonzeroBool M u a) := by
  intro x y rowLimit columnLimit rowOuter columnOuter
    hrow hcolumn hrowOuter hcolumnOuter
  apply commRing_matrixWords_nonzeroIndicator_double_limit M u a x y
    rowLimit columnLimit rowOuter columnOuter
  · simpa [matrixWordsNonzeroBool] using hrow
  · simpa [matrixWordsNonzeroBool] using hcolumn
  · exact hrowOuter
  · exact hcolumnOuter

/-- Any finite Boolean combination of finite matrix-word supports (with a
common alphabet, coefficient ring, and coordinate type) has the sequential
double-limit property. -/
theorem matrixWordsNonzeroBool_booleanCombine_hasBooleanDoubleLimitProperty
    {K ι : Type*} [CommRing K] [Fintype ι]
    {b d : ℕ} (op : (Fin d → Bool) → Bool)
    (M : Fin d → Fin b → Matrix ι ι K)
    (u a : Fin d → ι → K) :
    HasBooleanDoubleLimitProperty
      (booleanCombine op (fun k ↦ matrixWordsNonzeroBool (M k) (u k) (a k))) := by
  apply hasBooleanDoubleLimitProperty_booleanCombine
  intro k
  exact matrixWordsNonzeroBool_hasBooleanDoubleLimitProperty (M k) (u k) (a k)

end IndependentZeroBlocks
