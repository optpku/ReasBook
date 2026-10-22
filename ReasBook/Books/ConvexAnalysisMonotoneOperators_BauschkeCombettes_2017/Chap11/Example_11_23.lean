/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Example_9_43
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open Set

namespace ERealFunction

local notation "q" => (fun y : ℝ × ℝ ↦ (normPowerPerspectiveAtOrigin 2 y : EReal))

/- Example 11.23: the closed quadratic perspective is exactly the specialization `p = 2` of the
canonical `Γ₀` theorem `normPowerPerspectiveAtOrigin_mem_gammaZero` from Example 9.43. -/
#check (normPowerPerspectiveAtOrigin_mem_gammaZero 2 (by norm_num) :
    normPowerPerspectiveAtOrigin 2 ∈ Γ₀(ℝ × ℝ))

-- Proof sketch: show that the global minimizers are exactly the points where the quadratic
-- perspective takes its minimal value `0`, namely the nonnegative horizontal axis.
/-- The minimizers of the quadratic perspective are exactly `ℝ₊ × {0}`. -/
theorem quadraticPerspectiveArgmin_eq :
    Argmin q =
      Set.Ici (0 : ℝ) ×ˢ ({0} : Set ℝ) := sorry

-- Proof sketch: evaluate the explicit branch formula at the origin to see that the infimum is
-- attained there and equals `0`.
/-- The infimum of the quadratic perspective is `0`. -/
theorem quadraticPerspective_sInf_eq_zero :
    sInf (Set.range q) = 0 := sorry

/-- The sequence used in Example 11.23. -/
noncomputable def example11_23Sequence (p : ℝ) : ℕ → ℝ × ℝ :=
  fun n ↦ (((n + 1 : ℝ) ^ (p + 2)), (n + 1 : ℝ))

-- Proof sketch: unfold `example11_23Sequence`, substitute the sequence coordinates into the
-- explicit formula for `normPowerPerspectiveAtOrigin` at `p = 2`, and simplify
-- `(n + 1)^2 / (n + 1)^(p + 2) = 1 / (n + 1)^p`.
/-- Along the Example 11.23 sequence, the quadratic perspective has the exact value
`1 / (n + 1)^p`. -/
theorem quadraticPerspective_value_example11_23Sequence
    (p : ℝ) (n : ℕ) :
    q (example11_23Sequence p n) =
      ((1 / ((n + 1 : ℝ) ^ p) : ℝ) : EReal) := sorry

-- Proof sketch: combine the previous value formula with `quadraticPerspective_sInf_eq_zero` and
-- the convergence of `n ↦ 1 / (n + 1)^p` to `0` for `p ≥ 1`.
/-- For every `p ≥ 1`, the textbook sequence is a minimizing sequence of the quadratic
perspective. -/
theorem example11_23Sequence_isMinimizing
    (p : ℝ) (hp : 1 ≤ p) :
    IsMinimizingSequence q (example11_23Sequence p) := sorry

-- Proof sketch: use the description `Argmin f = ℝ₊ × {0}` and observe that the
-- point `((n + 1)^(p + 2), 0)` lies in that set and realizes the distance from
-- `((n + 1)^(p + 2), n + 1)` to the horizontal axis.
/-- The distance from the Example 11.23 sequence to the minimizer set is exactly `n + 1`. -/
theorem example11_23Sequence_infDist_argmin
    (p : ℝ) (n : ℕ) :
    Metric.infDist (example11_23Sequence p n)
      (Argmin q) = n + 1 := sorry

-- Proof sketch: compare the norm distance to any minimizer with the exact set distance from the
-- previous theorem, then use that `n + 1 → +∞`.
/-- The Example 11.23 sequence diverges away from every minimizer of the quadratic perspective. -/
theorem tendsto_norm_sub_of_mem_quadraticPerspectiveArgmin
    (p : ℝ) {x : ℝ × ℝ}
    (hx : x ∈ Argmin q) :
    Tendsto (fun n ↦ ‖example11_23Sequence p n - x‖) atTop atTop := sorry

end ERealFunction
