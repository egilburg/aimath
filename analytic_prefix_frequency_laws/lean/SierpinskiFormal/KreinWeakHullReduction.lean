import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.WeakSpace

/-!
# Reduction of weak compactness for closed convex hulls

This file isolates the precise form of Krein's theorem needed by the density
argument.  Mathlib already identifies norm closure and weak closure for convex
sets, so the weak image of a norm-closed convex hull is exactly the weak
closure of the convex hull of the weak image.

The file does not assert that this last closure is compact.  That compactness
statement is the missing Krein theorem.
-/

noncomputable section

open Set
open scoped Topology

namespace IndependentZeroBlocks

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The weak image of a norm-closed convex hull is the weak closure of the
convex hull of the weak image.  Thus all of the remaining compactness content
is concentrated in the right-hand side. -/
theorem toWeakSpace_image_closedConvexHull (K : Set E) :
    toWeakSpace ℝ E '' closedConvexHull ℝ K =
      closure (convexHull ℝ (toWeakSpace ℝ E '' K)) := by
  rw [closedConvexHull_eq_closure_convexHull,
    (convex_convexHull ℝ K).toWeakSpace_closure ℝ]
  exact congrArg closure ((toWeakSpace ℝ E).toLinearMap.image_convexHull K)

/-- The exact compactness primitive needed after the preceding reduction. -/
def KreinCompactHullProperty (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] : Prop :=
  ∀ K : Set (WeakSpace ℝ E), IsCompact K →
    IsCompact (closure (convexHull ℝ K))

/-- Krein compactness, if supplied for the ambient space, turns a weakly
compact set into a weakly compact norm-closed convex hull. -/
theorem isCompact_toWeakSpace_image_closedConvexHull
    (hKrein : KreinCompactHullProperty E) (K : Set E)
    (hK : IsCompact (toWeakSpace ℝ E '' K)) :
    IsCompact (toWeakSpace ℝ E '' closedConvexHull ℝ K) := by
  rw [toWeakSpace_image_closedConvexHull]
  exact hKrein _ hK

end IndependentZeroBlocks
