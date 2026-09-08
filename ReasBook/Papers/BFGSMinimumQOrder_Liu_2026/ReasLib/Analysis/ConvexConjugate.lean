module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

public section

open scoped InnerProductSpace

universe u

namespace ConvexAnalysis

/-- The real convex conjugate, expressed by the supremum of the inner-product pairing minus
the original function. -/
noncomputable def conjugate {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (x : E) : ℝ :=
  sSup (Set.range (fun z ↦ ⟪x, z⟫_ℝ - f z))

/-- Evaluation of the real convex conjugate as its defining supremum. -/
theorem conjugate_apply {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → ℝ) (x : E) :
    conjugate f x = sSup (Set.range (fun z ↦ ⟪x, z⟫_ℝ - f z)) := by
  -- Unfolding `conjugate` exposes the identical supremum expression.
  rfl

end ConvexAnalysis
