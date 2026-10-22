/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3

-- Declarations for this item will be appended below by the statement pipeline.

open Filter

namespace ERealFunction

/-- The real-valued function `f(ξ₁, ξ₂) = ξ₁ + ‖(ξ₁, ξ₂)‖` from Example 11.24, realized on the
Euclidean plane `ℝ²`. -/
noncomputable def example11_24Function : ℝ × ℝ → ℝ
  | (ξ₁, ξ₂) => ξ₁ + ‖(ξ₁, ξ₂)‖

local notation "f" => example11_24Function.toEReal.asEReal

/-- The sequence `xₙ = (-n, 1)` from Example 11.24. -/
def example11_24Sequence : ℕ → ℝ × ℝ
  | n => (-((n : ℝ)), 1)

-- Proof sketch: the first-coordinate projection on `ℝ × ℝ` is linear, hence convex, and the
-- Euclidean norm is convex on all of `ℝ²`; the sum of convex functions is convex.
/-- The function from Example 11.24 is convex on the Euclidean plane. -/
theorem example11_24Function_convexOn :
    _root_.ConvexOn ℝ Set.univ example11_24Function := sorry

-- Proof sketch: for `(ξ₁, ξ₂) : ℝ × ℝ`, the inequality `ξ₁ + ‖(ξ₁, ξ₂)‖ = 0` holds exactly when
-- `ξ₂ = 0` and `ξ₁ ≤ 0`; these are precisely the global minimizers because `‖(ξ₁, ξ₂)‖ ≥ -ξ₁`.
/-- The minimizers of the Example 11.24 function are exactly the nonpositive horizontal axis. -/
theorem example11_24_argmin_eq :
    Argmin f = Set.Iic (0 : ℝ) ×ˢ ({0} : Set ℝ) := sorry

-- Proof sketch: substitute `xₙ = (-n, 1)` into `ξ₁ + ‖(ξ₁, ξ₂)‖` and simplify
-- `‖(-n, 1)‖ = sqrt (n^2 + 1)`.
/-- Along the Example 11.24 sequence, the function value is `-n + √(n² + 1)`. -/
theorem example11_24Function_value_sequence (n : ℕ) :
    example11_24Function (example11_24Sequence n) =
      -((n : ℝ)) + Real.sqrt (((n : ℝ) ^ 2) + 1) := sorry

-- Proof sketch: the previous argmin description shows that the minimum value `0` is attained on
-- the nonpositive horizontal axis, so the infimum of the range is `0`.
/-- The infimum of the Example 11.24 function is `0`. -/
theorem example11_24_sInf_eq_zero :
    sInf (Set.range f) = 0 := sorry

-- Proof sketch: every term of the sequence lies in the domain automatically because the function
-- is real-valued, and the explicit value formula converges to the infimum `0`.
/-- The sequence `xₙ = (-n, 1)` is a minimizing sequence for the Example 11.24 function. -/
theorem example11_24Sequence_isMinimizing :
    IsMinimizingSequence f example11_24Sequence := sorry

-- Proof sketch: use the argmin description as the nonpositive horizontal axis; the closest
-- minimizer to `(-n, 1)` is `(-n, 0)`, so the set distance is exactly the vertical displacement
-- `1`.
/-- Every point of the Example 11.24 sequence stays at distance `1` from the minimizer set. -/
theorem example11_24Sequence_infDist_argmin (n : ℕ) :
    Metric.infDist (example11_24Sequence n) (Argmin f) = 1 := sorry

-- Proof sketch: combine `example11_24Sequence_isMinimizing` with
-- `example11_24Sequence_infDist_argmin`.
/-- Example 11.24: for `f(ξ₁, ξ₂) = ξ₁ + ‖(ξ₁, ξ₂)‖`, the sequence `xₙ = (-n, 1)` is minimizing,
while every term stays at distance `1` from `Argmin f`. -/
theorem example11_24_minimizingSequence_and_infDist_argmin :
    IsMinimizingSequence f example11_24Sequence ∧
      ∀ n : ℕ, Metric.infDist (example11_24Sequence n) (Argmin f) = 1 := sorry

end ERealFunction
