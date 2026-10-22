/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_49

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 3.2.7 lies in the chapter's analytical-complexity / separation-oracle lower-bound
domain.

Sampled owner-style declarations:
- `FeasibilityProblemWithSeparationOracle` in `Definition_3_49`, the source-facing owner of a
  feasible set together with its separation oracle;
- `SeparationOracleAlgorithm.SolvesWithin` in `Theorem_3_49`, the chapter owner for bounded-budget
  correctness of deterministic separation-oracle algorithms;
- `exists_hard_feasibility_problem_for_short_separation_oracle_algorithms` in `Theorem_3_49`, the
  canonical hard-instance theorem with exactly the source-facing oracle content needed here.

Best owner abstraction:
- source-facing: the existence of a feasibility problem with separation oracle defeating every
  deterministic algorithm below the logarithmic budget threshold;
- core/canonical:
  `exists_hard_feasibility_problem_for_short_separation_oracle_algorithms`;
- bridge/view: later analytical-complexity consequences that convert this hard-instance theorem
  into parameter-only oracle lower bounds.

Primitive data:
- the ambient dimension `n`;
- the accuracy/radius parameters `ε`, `R`;
- the oracle budget `k` below the logarithmic threshold.

Derived API:
- the hard feasibility instance `problem : FeasibilityProblemWithSeparationOracle n`;
- its nonempty interior and radius-bound properties;
- the universal failure statement for every deterministic separation-oracle algorithm at budget
  `k`.

The previous file replaced this source-facing theorem by a proof-route scalar inequality on
`ε ≤ (R / 2) * exp (-k / n)`. That estimate is only an internal bridge used in the hard-instance
construction; the canonical public owner in this chapter is already the theorem below, so this
numbered item is refined to a direct recall. -/

/- Theorem 3.2.7 is the chapter owner theorem
`exists_hard_feasibility_problem_for_short_separation_oracle_algorithms`. -/
recall exists_hard_feasibility_problem_for_short_separation_oracle_algorithms
