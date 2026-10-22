/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Algorithm_2_2

-- Declarations for this item will be appended below by the statement pipeline.

/- Proposition 2.9 is a recall-only item in the Euclidean optimal-method recurrence domain.

Primary domain:
* the scalar coefficient law `L * α_k^2 = (1 - α_k) γ_k + α_k μ`

Sampled owner-style declarations:
* `OptimalMethodRecurrence` in `Algorithm_2_2`, which owns the recurrence data
  `(x_k, y_k, v_k, α_k, γ_k)`;
* `OptimalMethodRecurrence.alpha_equation` in `Algorithm_2_2`, the primitive owner field for the
  scalar law recalled here;
* `constantStepSchemeIAlpha_equation` in `Algorithm_2_3`, the same scalar law on the
  source-facing recursive Algorithm 2.3 quantities;
* `constantStepSchemeIToOptimalMethodRecurrence` in `Algorithm_2_3`, the bridge packaging those
  recursive quantities into the owner recurrence abstraction.

Best owner abstraction:
* `OptimalMethodRecurrence.alpha_equation`

Primitive data:
* the parameters `L`, `μ`, `x0`, and `gamma0`
* the recurrence sequences `x`, `y`, `v`, `alpha`, and `gamma`

Derived API:
* the textbook `ω`-notation specialization obtained by substituting `L = 1 / ω`

Source/core/bridge triage:
* source-facing: Proposition 2.9's displayed scalar identity in textbook notation
* core/canonical: `OptimalMethodRecurrence.alpha_equation`
* bridge/view: the recursive Algorithm 2.3 realization and its conversion to
  `OptimalMethodRecurrence`

This file therefore keeps the main entry as a direct recall of the owner coefficient law and
introduces no local shell theorem.
-/

recall OptimalMethodRecurrence.alpha_equation
