/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_50

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 3.2.8 lies in the chapter's value-oracle lower-bound domain for constrained convex
minimization on `ℓ∞`-balls.

Mandatory domain-style sampling before refinement:
- `SetConstrainedMinimizationProblem.IsInLinftyConstrainedProblemClass` in `Theorem_3_50`, the
  source-facing owner of the admissible class `Q ⊆ B∞(0, R)` with
  `f ∈ 𝓕_M^{0,0}(B∞(0, R))`;
- `DeterministicValueOracleMethod` and `DeterministicValueOracleMethod.oracleTranscript` in
  `Chap01/Theorem_1_3_9`, the chapter owner for deterministic value-oracle procedures;
- `DeterministicValueOracleMethod.SolvesLinftyConstrainedProblemClassWithin` in `Theorem_3_50`,
  the bounded-budget correctness owner for this constrained class;
- `value_oracle_query_lower_bound_of_uniform_epsilon_guarantee` in `Theorem_3_50`, the canonical
  logarithmic lower-bound theorem on that owner surface.

Best owner abstraction:
- source-facing: the textbook logarithmic lower bound for deterministic value-oracle minimization
  over `Q ⊆ B∞(0, R)` with convex `M`-Lipschitz objective;
- core/canonical: `DeterministicValueOracleMethod.SolvesLinftyConstrainedProblemClassWithin`
  together with `SetConstrainedMinimizationProblem.IsInLinftyConstrainedProblemClass`;
- bridge/view: parameter-only analytical-complexity consequences read off from the owner theorem.

Primitive data:
- a deterministic value-oracle method and its bounded-budget correctness witness on the
  constrained problem class.

Derived API:
- the logarithmic lower bound on the oracle budget.

Source/core/bridge triage:
- source-facing: Theorem 3.2.8 as the logarithmic value-oracle lower bound for the constrained
  convex class;
- core/canonical: `value_oracle_query_lower_bound_of_uniform_epsilon_guarantee`;
- bridge/view: any later parameter-only numerical reformulations.

The previous file introduced a separate parameter-only predicate saying merely that every `k < N`
satisfies the scalar hard-instance inequality. As in `Proposition_3_42`, that wrapper is downward
closed in `N`, so it is not the chapter's owner notion of oracle complexity. The canonical public
owner for this theorem already exists in `Theorem_3_50`, so this numbered item is refined to a
direct recall of that theorem rather than keeping a parallel parameter wrapper. -/

/- Theorem 3.2.8 is the chapter owner theorem
`value_oracle_query_lower_bound_of_uniform_epsilon_guarantee`. -/
recall value_oracle_query_lower_bound_of_uniform_epsilon_guarantee
