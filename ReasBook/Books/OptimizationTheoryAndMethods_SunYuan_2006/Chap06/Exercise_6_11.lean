/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Algorithm_6_1_12

-- Domain sampling for this refine pass:
-- * primary domain: Steihaug-CG trust-region algorithm data and its stepwise recurrence API;
-- * inspected project declarations:
--   `SteihaugCGAlgorithm`,
--   `SteihaugCGAlgorithm.step_next_eq`,
--   `SteihaugCGAlgorithm.gradient_next_eq`,
--   `SteihaugCGAlgorithm.searchDirection_next_eq`;
-- * best owner abstraction: `SteihaugCGAlgorithm`, which already owns the Step `0` data, the two
--   boundary exits, the Step `2`-`4` recurrences, and the returned step;
-- * primitive data: the algorithm fields such as `step`, `gradient`, `preconditionedGradient`,
--   `searchDirection`, `α`, `β`, `τNegCurvature`, `τBoundary`, `returnedStep`, and the control
--   predicates/branch data recorded in the structure;
-- * derived API: the companion lemmas `step_next_eq`, `gradient_next_eq`,
--   `preconditionedGradient_next_eq`, and `searchDirection_next_eq`, together with the field
--   projections recording the stopping and boundary clauses.
-- Source/core/bridge triage:
-- * source-facing: Exercise 6.11 is an expository recall of the Steihaug-CG program;
-- * core/canonical: `SteihaugCGAlgorithm`;
-- * bridge/view: the owner fields and companion lemmas that restate the pseudocode clauses in a
--   theorem-friendly form.
-- Since the chapter already owns the full Steihaug-CG program as `SteihaugCGAlgorithm`, this
-- exercise is recall-only and should not keep a parallel string-valued pseudocode wrapper.

/- Chapter06 Exercise 6.11: the Steihaug-CG program is already recorded canonically by the owner
`SteihaugCGAlgorithm`. Its source-facing pseudocode clauses are realized by the following primitive
fields and companion update lemmas:

- Step `0` input and initialization:
  `initialGradient`, `hessianApprox`, `weightMatrix`, `ε`, `Δ`, `stepZero`,
  `preconditionedGradientZero`, `searchDirectionZero`.
- Initial stopping clause:
  `initialStop`.
- Negative-curvature boundary exit:
  `activeIteration_branch`, `negativeCurvatureTauPos`, `negativeCurvatureBoundary`,
  `negativeCurvatureReturnedStep`.
- Step `2` update and trust-region boundary exit:
  `alphaUpdate`, `step_next_eq`, `boundaryTauPos`, `boundaryOnSphere`, `boundaryReturnedStep`.
- Step `3` update and residual stopping clause:
  `gradient_next_eq`, `residualStop`.
- Step `4` update and loop continuation:
  `preconditionedGradient_next_eq`, `betaUpdate`, `searchDirection_next_eq`,
  `nextIterationActive`.
-/
#check SteihaugCGAlgorithm
#check SteihaugCGAlgorithm.initialStop
#check SteihaugCGAlgorithm.negativeCurvatureReturnedStep
#check SteihaugCGAlgorithm.step_next_eq
#check SteihaugCGAlgorithm.boundaryReturnedStep
#check SteihaugCGAlgorithm.gradient_next_eq
#check SteihaugCGAlgorithm.residualStop
#check SteihaugCGAlgorithm.preconditionedGradient_next_eq
#check SteihaugCGAlgorithm.searchDirection_next_eq
