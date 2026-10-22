/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: expand the two Fenchel conjugates. The radial parametrization `x = ρ z` with
-- `‖z‖ = 1` reduces the supremum over `H` to a supremum over `ρ ≥ 0`, the evenness of `φ` extends
-- this to all `ρ : ℝ`, and the support-function identity of the unit ball gives the factor `‖u‖`.
/-- Example 13.8: if `φ : ℝ → ]-∞,+∞]` is even, then the Fenchel conjugate of the radial function
`x ↦ φ ‖x‖` is the radial function `u ↦ φ^*(‖u‖)`. -/
theorem conjugate_comp_norm_eq_comp_norm_conjugate_of_even
    (φ : ℝ → Set.Ioi (⊥ : EReal)) (hφ_even : Function.Even φ) :
    (φ ∘ (norm : H → ℝ)).asEReal∗ = φ.asEReal∗ ∘ (norm : H → ℝ) := sorry

end ERealFunction
