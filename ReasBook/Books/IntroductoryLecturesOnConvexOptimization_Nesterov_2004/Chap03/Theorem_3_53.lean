/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_2_10

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

/- Theorem 3.53 lies in the chapter's center-of-gravity best-value geometric-decay domain.

Mandatory domain-style sampling before refinement:
- `HasGeometricRateOfConvergence` in `Chap01/Definition_1_2_6.lean`, the scalar owner for
  geometric decay;
- `HasGeometricRateOfConvergence.of_step_bound` in `Chap01/Definition_1_2_6.lean`, the canonical
  bridge from a one-step contraction to that scalar owner;
- `bestFunctionValueUpTo` in `Definition_3_55.lean`, the chapter owner for the best sampled value
  `f_k^*`;
- `CenterOfGravityMethod.bestFunctionValueUpTo_sub_optimalValue_le_lipschitz_geometricDecay` in
  `Theorem_3_2_10.lean`, the exact chapter owner theorem with the displayed rate
  `(1 - 1 / e)^(k / dim)`.

Best owner abstraction:
- source-facing/core owner for this numbered item:
  `CenterOfGravityMethod.bestFunctionValueUpTo_sub_optimalValue_le_lipschitz_geometricDecay`;
- core/canonical scalar owner beneath it:
  `HasGeometricRateOfConvergence` on the gap sequence
  `k ↦ bestFunctionValueUpTo (fun i ↦ problem (CenterOfGravityMethod.iterate problem i)) k -
    problem xStar`;
- bridge/view:
  a bare scalar recurrence on arbitrary `values : ℕ → ℝ`, which should not be promoted to the
  public theorem surface here.

Primitive data:
- a `ConvexMinimizationWithSeparationOracle E`;
- the minimizer `xStar`, outer radius `D`, and Lipschitz constant `M`;
- the canonical iterate sequence `CenterOfGravityMethod.iterate problem`.

Derived API:
- the best-so-far owner
  `bestFunctionValueUpTo (fun i ↦ problem (CenterOfGravityMethod.iterate problem i)) k`;
- the exact geometric-decay estimate with exponent `(k : ℝ) / Module.finrank ℝ E`.

Source/core/bridge triage:
- source-facing: the center-of-gravity best-value decay theorem itself;
- core/canonical: the owner theorem in `Theorem_3_2_10`;
- bridge/view: the generic scalar contraction lemma shape that the previous version exposed.

The previous file duplicated the mathematics at the wrong layer by replacing the chapter owner
theorem with generic scalar recurrence declarations on arbitrary `values : ℕ → ℝ`. In this
development, that recurrence belongs only to the scalar owner `HasGeometricRateOfConvergence`,
while the numbered Chapter 3 item already has an exact owner theorem upstream. This file is
therefore recall-only and reuses that theorem directly instead of keeping a parallel local decay
API.
-/

/- Theorem 3.53: along the center-of-gravity iterates, the best sampled objective value satisfies
the geometric decay estimate already recorded by the chapter owner theorem in
`Theorem_3_2_10`. -/
recall CenterOfGravityMethod.bestFunctionValueUpTo_sub_optimalValue_le_lipschitz_geometricDecay

end
