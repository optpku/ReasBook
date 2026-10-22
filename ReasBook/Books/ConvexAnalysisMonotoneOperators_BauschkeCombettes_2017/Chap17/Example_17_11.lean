/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Definition_2_23
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap17.Proposition_17_10

-- Declarations for this item will be appended below by the statement pipeline.

open ContinuousLinearMap
open ERealFunction
open InnerProductSpace
open scoped InnerProductSpace

universe u

namespace ContinuousLinearMap

-- Proof sketch: on `Set.univ`, strict monotonicity of the linear derivative field
-- `x ↦ toDual ℝ H (A x)` depends only on the difference vector `x - y`, so it reduces exactly to
-- the Chapter 2 owner predicate on the underlying linear map.
/-- For a linear derivative field on the whole space, strict Gâteaux monotonicity is exactly strict
monotonicity of the underlying linear operator in the sense of Definition 2.23. -/
theorem strictGateauxDerivativeMonotoneOn_univ_iff_isStrictlyMonotone
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →L[ℝ] H) :
    StrictGateauxDerivativeMonotoneOn (fun x ↦ toDual ℝ H (A x)) Set.univ ↔
      A.toLinearMap.IsStrictlyMonotone := by
  constructor
  · intro hA z hz
    simpa [InnerProductSpace.toDual_apply_apply] using hA z (by simp) 0 (by simp) hz
  · intro hA x _ y _ hxy
    have hz : x - y ≠ 0 := sub_ne_zero.mpr hxy
    have hpair :
        (toDual ℝ H (A x) - toDual ℝ H (A y)) (x - y) = ⟪A (x - y), x - y⟫_ℝ := by
      simp only [sub_apply, InnerProductSpace.toDual_apply_apply, map_sub, inner_sub_left,
        inner_sub_right]
    rw [hpair]
    exact hA (x - y) hz

end ContinuousLinearMap

-- Proof sketch: Example 2.57 identifies the gradient of the quadratic form
-- `x ↦ ⟪x, A x⟫_ℝ` with the affine field `x ↦ (A + A.adjoint) x`, and Proposition 17.10
-- specializes on the whole space to say that a differentiable real-valued function is strictly
-- convex exactly when its derivative field is strictly monotone. For this linear field, that
-- criterion is exactly strict positivity of the quadratic form of `A + A†` on nonzero vectors.
/-- Example 17.11: for a bounded linear operator `A` on a real Hilbert space, the quadratic form
`x ↦ ⟪x, A x⟫_ℝ` is strictly convex on `H` if and only if the quadratic form of the symmetric part
`A + A†` is strictly positive on every nonzero vector. -/
theorem quadraticForm_strictConvexOn_univ_iff_symmetricPart_positive
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →L[ℝ] H) :
    StrictConvexOn ℝ Set.univ (fun x : H ↦ ⟪x, A x⟫_ℝ) ↔
      ∀ x : H, x ≠ 0 → 0 < ⟪(A + A.adjoint) x, x⟫_ℝ := sorry

-- Proof sketch: the source-facing strict quadratic-form criterion is exactly the Chapter 2 owner
-- `LinearMap.IsStrictlyMonotone` applied to the symmetric part.
/-- Canonical bridge for Example 17.11: the same strict convexity criterion can be expressed by
saying that the symmetric part `A + A†` is strictly monotone. -/
theorem quadraticForm_strictConvexOn_univ_iff_symmetricPart_isStrictlyMonotone
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A : H →L[ℝ] H) :
    StrictConvexOn ℝ Set.univ (fun x : H ↦ ⟪x, A x⟫_ℝ) ↔
      (A + A.adjoint).toLinearMap.IsStrictlyMonotone := by
  rw [show (A + A.adjoint).toLinearMap.IsStrictlyMonotone ↔
      ∀ x : H, x ≠ 0 → 0 < ⟪(A + A.adjoint) x, x⟫_ℝ from Iff.rfl]
  exact quadraticForm_strictConvexOn_univ_iff_symmetricPart_positive A
