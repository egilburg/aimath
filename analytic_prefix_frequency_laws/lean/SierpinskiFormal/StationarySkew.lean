import SierpinskiFormal.BooleanWordCesaro
import Mathlib.Dynamics.BirkhoffSum.Average

/-!
# The stationary word skew cocycle

This file isolates the pointwise algebra in the stationary-source argument.
It defines the chronological prefix read along an arbitrary transformation,
the associated skew action by right translations, and proves that its iterates
are exactly right translations by those prefixes.  No probability or
compactness hypothesis is needed for these identities.
-/

noncomputable section

open Filter Finset Function
open scoped Topology BigOperators BoundedContinuousFunction

namespace IndependentZeroBlocks

section Prefix

variable {Ω A : Type*}

/-- The first `n` letters seen along the forward orbit of `x`. -/
def stationaryPrefix (letter : Ω → A) (T : Ω → Ω) : ℕ → Ω → List A
  | 0, _ => []
  | n + 1, x => letter x :: stationaryPrefix letter T n (T x)

@[simp] theorem stationaryPrefix_zero (letter : Ω → A) (T : Ω → Ω) (x : Ω) :
    stationaryPrefix letter T 0 x = [] := rfl

@[simp] theorem stationaryPrefix_succ (letter : Ω → A) (T : Ω → Ω)
    (n : ℕ) (x : Ω) :
    stationaryPrefix letter T (n + 1) x =
      [letter x] ++ stationaryPrefix letter T n (T x) := rfl

theorem stationaryPrefix_length (letter : Ω → A) (T : Ω → Ω)
    (n : ℕ) (x : Ω) :
    (stationaryPrefix letter T n x).length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [stationaryPrefix, ih]

end Prefix

section AbstractSkew

variable {Ω A E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A finite-letter cocycle acting on `E`-valued functions. -/
def stationarySkewApply (R : A → E →L[ℝ] E) (letter : Ω → A)
    (T : Ω → Ω) (g : Ω → E) (x : Ω) : E :=
  R (letter x) (g (T x))

theorem stationarySkewApply_add (R : A → E →L[ℝ] E) (letter : Ω → A)
    (T : Ω → Ω) (g h : Ω → E) :
    stationarySkewApply R letter T (g + h) =
      stationarySkewApply R letter T g + stationarySkewApply R letter T h := by
  funext x
  exact map_add (R (letter x)) _ _

theorem stationarySkewApply_smul (R : A → E →L[ℝ] E) (letter : Ω → A)
    (T : Ω → Ω) (c : ℝ) (g : Ω → E) :
    stationarySkewApply R letter T (c • g) =
      c • stationarySkewApply R letter T g := by
  funext x
  exact map_smul (R (letter x)) c _

theorem norm_stationarySkewApply_le (R : A → E →L[ℝ] E)
    (hR : ∀ a, ‖R a‖ ≤ 1) (letter : Ω → A) (T : Ω → Ω)
    (g : Ω → E) (x : Ω) :
    ‖stationarySkewApply R letter T g x‖ ≤ ‖g (T x)‖ := by
  simpa [stationarySkewApply] using
    (R (letter x)).le_of_opNorm_le (hR (letter x)) (g (T x))

/-- Iterated pointwise domination by the scalar orbit of the norm. -/
theorem norm_iterate_stationarySkewApply_le
    (R : A → E →L[ℝ] E) (hR : ∀ a, ‖R a‖ ≤ 1)
    (letter : Ω → A) (T : Ω → Ω) (g : Ω → E) (n : ℕ) (x : Ω) :
    ‖((stationarySkewApply R letter T)^[n] g) x‖ ≤ ‖g (T^[n] x)‖ := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (norm_stationarySkewApply_le R hR letter T _ x).trans (by
        simpa only [Function.iterate_succ_apply] using ih (T x))

/-- Vector-valued skew averages are pointwise dominated by the scalar
ergodic averages of the norm. -/
theorem norm_birkhoffAverage_stationarySkewApply_le
    (R : A → E →L[ℝ] E) (hR : ∀ a, ‖R a‖ ≤ 1)
    (letter : Ω → A) (T : Ω → Ω) (g : Ω → E) (N : ℕ) (x : Ω) :
    ‖birkhoffAverage ℝ (stationarySkewApply R letter T) id N g x‖ ≤
      birkhoffAverage ℝ T (fun y => ‖g y‖) N x := by
  simp only [birkhoffAverage, birkhoffSum, id_eq, Pi.smul_apply,
    Finset.sum_apply]
  rw [norm_smul]
  rw [Real.norm_eq_abs, abs_inv, abs_of_nonneg (Nat.cast_nonneg N)]
  calc
    (N : ℝ)⁻¹ * ‖∑ n ∈ Finset.range N,
        ((stationarySkewApply R letter T)^[n] g) x‖
        ≤ (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
          ‖((stationarySkewApply R letter T)^[n] g) x‖ := by
            gcongr
            exact norm_sum_le _ _
    _ ≤ (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ‖g (T^[n] x)‖ := by
          gcongr with n hn
          exact norm_iterate_stationarySkewApply_le R hR letter T g n x
    _ = (N : ℝ)⁻¹ • ∑ n ∈ Finset.range N, ‖g (T^[n] x)‖ := by
          rw [smul_eq_mul]

end AbstractSkew

section WordSkew

variable {Ω A : Type*} [TopologicalSpace A] [DiscreteTopology A]

/-- The stationary skew action on bounded word functions. -/
def stationaryWordSkew (letter : Ω → A) (T : Ω → Ω)
    (g : Ω → BoundedWordFunction A) : Ω → BoundedWordFunction A :=
  stationarySkewApply (fun a => wordRightTranslateCLM (A := A) [a]) letter T g

@[simp] theorem stationaryWordSkew_apply (letter : Ω → A) (T : Ω → Ω)
    (g : Ω → BoundedWordFunction A) (x : Ω) :
    stationaryWordSkew letter T g x =
      wordRightTranslate [letter x] (g (T x)) := rfl

/-- Iterating the skew action on a constant word function reads chronological
prefixes.  This is the orientation-sensitive identity needed by the
stationary theorem. -/
theorem iterate_stationaryWordSkew_const (letter : Ω → A) (T : Ω → Ω)
    (q : BoundedWordFunction A) (n : ℕ) (x : Ω) :
    ((stationaryWordSkew letter T)^[n] (fun _ => q)) x =
      wordRightTranslate (stationaryPrefix letter T n x) q := by
  induction n generalizing x with
  | zero =>
      ext z
      simp [stationaryWordSkew, wordRightTranslate_apply]
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      simp only [stationaryWordSkew_apply, ih, stationaryPrefix_succ]
      exact wordRightTranslate_append [letter x]
        (stationaryPrefix letter T n (T x)) q

theorem iterate_stationaryWordSkew_const_apply
    (letter : Ω → A) (T : Ω → Ω) (q : BoundedWordFunction A)
    (n : ℕ) (x : Ω) (z : List A) :
    (((stationaryWordSkew letter T)^[n] (fun _ => q)) x) z =
      q (z ++ stationaryPrefix letter T n x) := by
  rw [iterate_stationaryWordSkew_const, wordRightTranslate_apply]

/-- The norm of every skew iterate of a constant word function is bounded by
the norm of that word function. -/
theorem norm_iterate_stationaryWordSkew_const_le
    (letter : Ω → A) (T : Ω → Ω) (q : BoundedWordFunction A)
    (n : ℕ) (x : Ω) :
    ‖((stationaryWordSkew letter T)^[n] (fun _ => q)) x‖ ≤ ‖q‖ := by
  rw [iterate_stationaryWordSkew_const]
  simpa using (wordRightTranslateCLM
    (A := A) (stationaryPrefix letter T n x)).le_of_opNorm_le
      (wordRightTranslateCLM_norm_le
        (A := A) (stationaryPrefix letter T n x)) q

/-- Evaluation of the skew Cesaro average is the empirical prefix frequency
at a fixed left context. -/
theorem birkhoffAverage_stationaryWordSkew_const_apply
    (letter : Ω → A) (T : Ω → Ω) (q : BoundedWordFunction A)
    (N : ℕ) (x : Ω) (z : List A) :
    (birkhoffAverage ℝ (stationaryWordSkew letter T) id N (fun _ => q) x) z =
      (N : ℝ)⁻¹ • ∑ n ∈ Finset.range N,
        q (z ++ stationaryPrefix letter T n x) := by
  simp only [birkhoffAverage, birkhoffSum, id_eq,
    Pi.smul_apply, Finset.sum_apply,
    BoundedContinuousFunction.smul_apply, BoundedContinuousFunction.sum_apply,
    iterate_stationaryWordSkew_const_apply]

/-- The bounded word-function valued empirical Cesaro average along one
sample path. -/
def stationaryWordCesaro (letter : Ω → A) (T : Ω → Ω)
    (q : BoundedWordFunction A) (N : ℕ) (x : Ω) : BoundedWordFunction A :=
  (N : ℝ)⁻¹ • ∑ n ∈ Finset.range N,
    wordRightTranslate (stationaryPrefix letter T n x) q

theorem stationaryWordCesaro_apply (letter : Ω → A) (T : Ω → Ω)
    (q : BoundedWordFunction A) (N : ℕ) (x : Ω) (z : List A) :
    stationaryWordCesaro letter T q N x z =
      (N : ℝ)⁻¹ • ∑ n ∈ Finset.range N,
        q (z ++ stationaryPrefix letter T n x) := by
  simp [stationaryWordCesaro, wordRightTranslate_apply]

theorem mapsTo_wordRightTranslate_of_mapsTo_letters
    (C : Set (BoundedWordFunction A))
    (hletter : ∀ (a : A) {f}, f ∈ C → wordRightTranslate [a] f ∈ C)
    (w : List A) : Set.MapsTo (wordRightTranslate w) C C := by
  intro f hf
  induction w with
  | nil =>
      convert hf using 1
      ext z
      simp [wordRightTranslate_apply]
  | cons a w ih =>
      rw [show a :: w = [a] ++ w by rfl,
        ← wordRightTranslate_append [a] w]
      exact hletter a ih

/-- If `C` is convex, contains `q`, and is invariant under one-letter right
translations, every positive stationary prefix average belongs to `C`. -/
theorem stationaryWordCesaro_mem
    (letter : Ω → A) (T : Ω → Ω) (q : BoundedWordFunction A)
    (C : Set (BoundedWordFunction A)) (hCconvex : Convex ℝ C) (hq : q ∈ C)
    (htranslate : ∀ (a : A) {f}, f ∈ C → wordRightTranslate [a] f ∈ C)
    {N : ℕ} (hN : N ≠ 0) (x : Ω) :
    stationaryWordCesaro letter T q N x ∈ C := by
  rw [stationaryWordCesaro, Finset.smul_sum]
  apply hCconvex.sum_mem
  · intro n hn
    positivity
  · simp [hN]
  · intro n hn
    exact mapsTo_wordRightTranslate_of_mapsTo_letters C htranslate
      (stationaryPrefix letter T n x) hq

/-- Norm convergence of the skew averages is exactly uniform convergence over
all fixed left contexts. -/
theorem tendsto_uniform_left_context_of_tendsto_skew_average
    (letter : Ω → A) (T : Ω → Ω) (q : BoundedWordFunction A)
    (x : Ω) (h : BoundedWordFunction A)
    (hconv : Tendsto
      (fun N => birkhoffAverage ℝ (stationaryWordSkew letter T) id N
        (fun _ => q) x) atTop (𝓝 h)) :
    Tendsto (fun N => ‖birkhoffAverage ℝ (stationaryWordSkew letter T) id N
      (fun _ => q) x - h‖) atTop (𝓝 0) := by
  have hs := hconv.sub_const h
  apply tendsto_zero_iff_norm_tendsto_zero.mp
  simpa using hs

end WordSkew

end IndependentZeroBlocks
