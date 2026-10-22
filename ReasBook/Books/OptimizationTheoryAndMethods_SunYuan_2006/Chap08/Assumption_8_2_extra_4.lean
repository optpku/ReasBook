/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_2_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_2_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_2_extra_1

noncomputable section

section Chapter08Assumption82Extra4

variable {n m : ℕ} {E I : Set (Fin m)}

local notation "Point" => Fin n → ℝ

/-
Domain sampling and owner choice for this file:

* `source-facing`: `ConstrainedOptimizationProblem n m E I` together with
  `ConstrainedOptimizationProblem.linearizedFeasibleDirectionSet` from
  `Definition_8_2_2`;
* `core/canonical`: `posTangentConeAt X xStar`, recalled directly in
  `Definition_8_2_3`;
* `bridge/view`: the generic descent-direction owner `descentDirections` from
  `Definition_8_2_extra_1`, transported along the Euclidean model already used
  in `Definition_8_2_2`.

This assumption therefore keeps only the source-facing regularity predicate and
reuses the upstream owners for its constituent sets, including the Euclidean
objective bridge already owned by `Definition_8_2_2`.
-/

namespace ConstrainedOptimizationProblem

/-- Chapter08 Assumption 8.2-extra-4: the regularity assumption at `xStar` is that the
sequential feasible directions of `problem.feasibleSet` at `xStar` which are descent directions
of `problem.objective`, computed via the Euclidean model already used for gradients in
`Definition_8_2_2`, are exactly the linearized feasible directions at `xStar` with the same
descent property. -/
def regularityAssumptionAt
    (problem : ConstrainedOptimizationProblem n m E I) (xStar : Point) : Prop :=
  posTangentConeAt problem.feasibleSet xStar ∩
      ((WithLp.toLp 2) ⁻¹'
        descentDirections problem.euclideanObjective (WithLp.toLp 2 xStar)) =
    problem.linearizedFeasibleDirectionSet xStar ∩
      ((WithLp.toLp 2) ⁻¹'
        descentDirections problem.euclideanObjective (WithLp.toLp 2 xStar))

/-- Unfolding formula for `problem.regularityAssumptionAt xStar`. -/
theorem regularityAssumptionAt_iff
    (problem : ConstrainedOptimizationProblem n m E I) (xStar : Point) :
    problem.regularityAssumptionAt xStar ↔
      posTangentConeAt problem.feasibleSet xStar ∩
          ((WithLp.toLp 2) ⁻¹'
            descentDirections problem.euclideanObjective (WithLp.toLp 2 xStar)) =
        problem.linearizedFeasibleDirectionSet xStar ∩
          ((WithLp.toLp 2) ⁻¹'
            descentDirections problem.euclideanObjective (WithLp.toLp 2 xStar)) :=
  Iff.rfl

end ConstrainedOptimizationProblem

end Chapter08Assumption82Extra4
