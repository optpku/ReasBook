/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Definition_16_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap17.Definition_17_20

-- Declarations for this item will be appended below by the statement pipeline.

open scoped EuclideanSpace InnerProductSpace

namespace ERealFunction

noncomputable section

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-- The counterexample function `(ξ₁, ξ₂) ↦ |ξ₁| + 2 |ξ₂|`. -/
def example17_23Function (x : ℝ²) : ℝ :=
  |x 0| + 2 * |x 1|

local notation "f" => example17_23Function.toEReal

/-- The base point `(1,0)` used in the counterexample. -/
def example17_23Point : ℝ² :=
  !₂[(1 : ℝ), 0]

/-- The vector `(1, εδ)` used as a subgradient candidate in the counterexample. -/
def example17_23Subgradient (ε δ : ℝ) : ℝ² :=
  !₂[(1 : ℝ), ε * δ]

-- Proof sketch: `f` is finite everywhere, so it never takes the value
-- `-∞`, and its effective domain is all of the canonical Euclidean model of `ℝ²`, hence in
-- particular nonempty.
/-- The counterexample function, viewed through the canonical `toEReal` owner, is proper. -/
theorem example17_23Function_isProper :
    IsProper (f : ℝ² → EReal) := sorry

-- Proof sketch: the coordinate maps `x ↦ |x 0|` and `x ↦ 2 |x 1|` are convex on `ℝ²`, so their
-- sum is convex on the effective domain of `f`.
/-- The counterexample function is convex on its effective domain. -/
theorem example17_23Function_convexOn :
    ConvexOn f (effectiveDomain f) := sorry

-- Proof sketch: expand the subdifferential inequality for
-- `f(ξ₁, ξ₂) = |ξ₁| + 2 |ξ₂|` at `(1,0)`, use that the first coordinate has slope `1` there, and
-- use `|εδ| ≤ 3 / 2` to control the second coordinate term.
/-- If the second coordinate `εδ` is bounded by `3 / 2` in absolute value, then the vector
`(1, εδ)` belongs to the subdifferential of the counterexample function at `(1,0)`. In
particular, this applies to the textbook family `δ ∈ [1/2, 3/2]` with `ε = ±1`. -/
theorem example17_23Subgradient_mem_subdifferential {δ ε : ℝ}
    (hδ : |ε * δ| ≤ 3 / 2) :
    example17_23Subgradient ε δ ∈ (∂ f) example17_23Point := sorry

-- Proof sketch: write
-- `example17_23Point - α • example17_23Subgradient ε δ = (1 - α, -α ε δ)`, then compute
-- `|1 - α| + 2 |α ε δ|` and use `|ε| = 1` together with `δ ≥ 1 / 2` to show this is at least
-- `1 = example17_23Function example17_23Point` for every `α > 0`.
/-- Every positive step along the negative of the chosen subgradient keeps the counterexample
function above its value at `(1,0)` once `δ ≥ 1 / 2`. In particular, this applies to the
textbook interval `δ ∈ [1/2, 3/2]`. -/
theorem example17_23_nondecrease_along_neg_subgradient {δ ε : ℝ}
    (hδ : (1 / 2 : ℝ) ≤ δ) (hε : ε = 1 ∨ ε = -1)
    (α : ℝ) (hα : α ∈ Set.Ioi (0 : ℝ)) :
    (f (example17_23Point - α • example17_23Subgradient ε δ) : EReal) ≥
      (f example17_23Point : EReal) := sorry

-- Proof sketch: combine `example17_23Subgradient_mem_subdifferential` with the textbook upper
-- bound `δ ≤ 3 / 2`, using `|ε| = 1` for `ε = ±1`, and use the lower bound `δ ≥ 1 / 2` together
-- with `example17_23_nondecrease_along_neg_subgradient` to rule out strict decrease along
-- `-example17_23Subgradient ε δ`.
/-- Example 17.23: for `f(ξ₁, ξ₂) = |ξ₁| + 2 |ξ₂|`, `x = (1,0)`, and `u = (1, ±δ)` with
`δ ∈ [1/2, 3/2]`, the vector `u` belongs to `∂ f(x)` while `-u` is not a descent direction at
`x`. -/
theorem example17_23_subgradient_and_neg_not_descentDirection {δ ε : ℝ}
    (hδ : δ ∈ Set.Icc (1 / 2 : ℝ) (3 / 2)) (hε : ε = 1 ∨ ε = -1) :
    example17_23Subgradient ε δ ∈ (∂ f) example17_23Point ∧
      ¬ IsDescentDirectionAt f example17_23Point (-example17_23Subgradient ε δ) := sorry

end

end ERealFunction
