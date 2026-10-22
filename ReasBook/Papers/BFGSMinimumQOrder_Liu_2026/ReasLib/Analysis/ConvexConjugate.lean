/-
Authors: Chenyi Li
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/BFGSMinimumQOrder_Liu_2026/README.md (formalization contributor).
-/

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
