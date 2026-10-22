/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_30
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_20
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: expand the Fenchel-conjugate value of
-- `x ↦ φ x + ‖x‖² / (2γ)` at `u`, complete the square in the quadratic term, and recognize the
-- remaining infimum as the `γ`-Moreau envelope of `φ` evaluated at `γ • u`.
/-- Example 13.4: for `φ : H → ]-∞,+∞]` and `γ ∈ ℝ_{++}`, the Fenchel conjugate of the
regularized function `x ↦ φ x + ‖x‖² / (2γ)` is
`u ↦ γ‖u‖² / 2 - {}^γφ(γu)`. -/
theorem conjugate_regularized_eq_scaledQuadratic_sub_moreauEnvelope
    (φ : H → Set.Ioi (⊥ : EReal)) (γ : Set.Ioi (0 : ℝ)) :
    ((φ + moreauQuadraticKernel γ).asEReal)∗ =
      fun u : H ↦ ((((γ : ℝ) / 2) * ‖u‖ ^ 2 : ℝ) : EReal) - ({}^[γ] φ) ((γ : ℝ) • u) := sorry

/-- Evaluating the Example 13.4 function identity at `u` yields the textbook pointwise formula
`(φ + ‖·‖² / (2γ))^*(u) = γ‖u‖² / 2 - {}^γφ(γu)`. -/
theorem conjugate_regularized_value_eq_scaledQuadratic_sub_moreauEnvelope
    (φ : H → Set.Ioi (⊥ : EReal)) (γ : Set.Ioi (0 : ℝ)) (u : H) :
    (((φ + moreauQuadraticKernel γ).asEReal)∗) u =
      ((((γ : ℝ) / 2) * ‖u‖ ^ 2 : ℝ) : EReal) - ({}^[γ] φ) ((γ : ℝ) • u) := by
  simpa using congrFun
    (conjugate_regularized_eq_scaledQuadratic_sub_moreauEnvelope φ γ) u

end ERealFunction
