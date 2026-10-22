/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap07.Definition_7_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Proposition_16_60

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

namespace ERealFunction

section RealLine

variable (Ω : Set ℝ) (hΩ : Ω.Nonempty)

include hΩ

-- Proof sketch: for `ξ < 0`, the support function of `Ω` is the affine map `x ↦ ξ x` maximized at
-- the lower endpoint, so the only supporting slope is the infimum endpoint of `Ω` when that
-- endpoint is real.
/-- Example 16.14 (1): if `ξ < 0`, the subdifferential of the support function of a nonempty
subset `Ω ⊆ ℝ` is the real slice of the singleton containing the infimum endpoint of `Ω`. -/
theorem subdifferential_supportFunction_eq_lowerEndpoint_of_neg
    {ξ : ℝ} (hξ : ξ < 0) :
    (∂ σ[Ω]) ξ =
      {x : ℝ | (x : EReal) = sInf (Real.toEReal '' Ω)} := sorry

-- Proof sketch: at `ξ = 0`, the support function is supported by every point of the closed convex
-- hull of `Ω`, and only those points satisfy the global affine minorization inequality defining the
-- subdifferential.
/-- Example 16.14 (2): at `0`, the subdifferential of the support function of a nonempty subset
`Ω ⊆ ℝ` is the closed convex hull of `Ω`. -/
theorem subdifferential_supportFunction_eq_closedConvexHull_at_zero
    : (∂ σ[Ω]) 0 = closedConvexHull ℝ Ω := sorry

-- Proof sketch: for `ξ > 0`, the support function of `Ω` is the affine map `x ↦ ξ x` maximized at
-- the upper endpoint, so the only supporting slope is the supremum endpoint of `Ω` when that
-- endpoint is real.
/-- Example 16.14 (3): if `ξ > 0`, the subdifferential of the support function of a nonempty
subset `Ω ⊆ ℝ` is the real slice of the singleton containing the supremum endpoint of `Ω`. -/
theorem subdifferential_supportFunction_eq_upperEndpoint_of_pos
    {ξ : ℝ} (hξ : 0 < ξ) :
    (∂ σ[Ω]) ξ =
      {x : ℝ | (x : EReal) = sSup (Real.toEReal '' Ω)} := sorry

omit hΩ

end RealLine

end ERealFunction
