/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_2_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {m : ℕ}

open ApproximateLagrangeMultiplierSwitchingMethod

namespace ApproximateLagrangeMultiplierSwitchingMethod

variable {problem : ProjectedMultipleConstraintFirstOrderProblem E m}

open scoped ApproximateLagrangeMultiplierSwitchingNotation

/- Theorem 3.43 lies in the chapter's approximate-Lagrange-multiplier switching-method domain.

Sampled owner-style declarations:
- `positive_inactiveConstraintCount_of_large_iteration_count`
- `maxTypeObjective` and `maxTypeObjective_le_iff`
- `constraintMaximumAt_le_sampleMaxSubgradientNorm_mul_h_of_mem_inactiveConstraintIndices`
- `delta_le_sampleMaxSubgradientNorm_mul_h_of_large_iteration_count`

Best owner abstraction:
- the owner run `ApproximateLagrangeMultiplierSwitchingMethod problem`
- the chapter finite-family maximum owner `maxTypeObjective`

Primitive data:
- the switching-method run `method`
- the time index `t`, the objective-step iterate `k ∈ A₀(t)`, and the stepsize positivity `0 < h`

Derived API:
- the source-facing residual maximum `maxTypeObjective problem.constraints (method k)`
- the componentwise owner theorem
  `constraintMaximumAt_le_sampleMaxSubgradientNorm_mul_h_of_mem_inactiveConstraintIndices`
- the gap bound `δ_t ≤ M h`

Source/core/bridge triage:
- source-facing: Theorem 3.43's positivity statement, residual-maximum bound, and gap estimate
- core/canonical: the run owner theorems in `Theorem_3_2_4` and the finite-max owner
  `maxTypeObjective`
- bridge/view: the finite-max reformulation of the componentwise residual bound

The first and third clauses are exact owner recalls. The middle clause in the source is the
finite residual maximum `max_{1 ≤ j ≤ m} f_j(x_k) ≤ M h`, and this theorem surface now lives
directly in `Theorem_3_2_4`, so this file recalls it rather than reproving a parallel copy. -/

recall positive_inactiveConstraintCount_of_large_iteration_count

omit [CompleteSpace E] in
/-- Theorem 3.43 (middle clause): on every objective-step iterate `x_k` with `k ∈ A₀(t)`, the
maximum constraint residual is bounded by `M h`, where
`M = M[method](t)`. -/
recall maxConstraintValueAt_le_sampleMaxSubgradientNorm_mul_h_of_mem_inactiveConstraintIndices

recall delta_le_sampleMaxSubgradientNorm_mul_h_of_large_iteration_count

end ApproximateLagrangeMultiplierSwitchingMethod

end
