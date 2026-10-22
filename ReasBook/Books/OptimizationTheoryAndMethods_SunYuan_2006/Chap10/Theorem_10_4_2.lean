/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Theorem_10_4_2.RunSemantics

noncomputable section

variable {n m : ℕ}

/-- Chapter10 Theorem 10.4.2: let the feasible region `X` of problem `(10.1.1)`-`(10.1.3)` be
nonempty. Then for some `ε > 0`, Algorithm 10.4.1 is either finitely terminated, or the
sequence `{x_k}` produced by Algorithm 10.4.1 satisfies `liminf_{k → ∞} f(x_k) = -∞`, encoded
here by saying that the objective values `f(x_k)` lie below every real threshold frequently
along `atTop`. In the current Chapter 10 API, a produced sequence is represented by a recorded
run `method : AugmentedLagrangianMethod n m` whose stored problem and tolerance match the source
parameters. Since the source theorem speaks about one sequence produced by Algorithm 10.4.1,
the theorem keeps the source existential choice of a positive tolerance `ε` together with a
recorded run having those source parameters, and states the source alternative for that run. -/
theorem augmentedLagrangianMethod_existsTolerance_finiteTermination_or_liminfBot
    (problem : StandardPenaltyProblem n m)
    (hFeasible : Set.Nonempty problem.feasibleSet) :
    ∃ ε : ℝ, 0 < ε ∧
      ∃ method : AugmentedLagrangianMethod n m,
        method.finiteTerminationOrObjectiveLiminfBot problem ε := sorry
