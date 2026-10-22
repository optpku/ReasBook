/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Proposition_6_40

-- Declarations for this item will be appended below by the statement pipeline.

/- Text 6.4.6 lies in the second-order Hölder upper-model domain.

Primary domain:
- second-order Taylor upper models under Hölder continuity of the second derivative.

Sampled owner-style declarations:
- `HolderOnWith`, the canonical on-set owner for Hölder continuity;
- `iteratedFDerivWithin`, the canonical within-set owner for higher derivatives;
- `secondOrderTaylorModelAt` from Chapter 1, the canonical quadratic model owner;
- `holder_hessian_upper_model` in `Proposition_6_40`, the Chapter 6 theorem already expressing the
  required upper-model inequality.

Best owner abstraction:
- source-facing: the quadratic upper-model inequality under the `(6.4.5)` Hölder-Hessian
  assumption;
- core/canonical: `holder_hessian_upper_model`, built from the canonical within-set derivative
  data and `HolderOnWith H v (iteratedFDerivWithin ℝ 2 f Q) Q`;
- bridge/view: specialization to whole-space or `secondOrderTaylorModelAt` surfaces when later
  files need that presentation.

Primitive data:
- a feasible set `Q`;
- a real-valued objective `f`;
- Hölder exponent `v` and constant `H`;
- the canonical differentiability and Hölder hypotheses on the within first and second
  derivatives.

Derived API:
- the second-order upper-model inequality with remainder
  `H * ‖y - x‖^(2 + v) / ((1 + v) * (2 + v))`.

This text item does not introduce a new owner beyond the Chapter 6 theorem already formalized in
`Proposition_6_40`. The prior local minimizer-on-ball theorem was unrelated to the source
mathematics, so the correct refinement is a direct recall of the existing upper-model result
instead of another parallel wrapper. -/

/- Text 6.4.6-Second-Order Model Applicability: under the Hölder-continuous second-derivative
assumption from `(6.4.5)`, the second-order Taylor model satisfies the upper-model inequality with
remainder `H * ‖y - x‖^(2 + v) / ((1 + v) * (2 + v))`. In the chapter API, this is exactly the
canonical theorem `holder_hessian_upper_model`. -/
recall holder_hessian_upper_model
