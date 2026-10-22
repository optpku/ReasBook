/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Proposition_6_23

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators

universe v

/- Definition 6.27 lies in Chapter 6's finite-family log-sum-exp / entropy-smoothing domain.

Primary domain:
- the textbook log-sum-exp potential `η(u)` on a finite score family.

Sampled owner-style declarations:
- `η` in `Chap06/Proposition_6_23`, the existing chapter owner for the textbook log-sum-exp
  potential;
- `eta_apply` in `Chap06/Proposition_6_23`, the upstream coordinate formula for that owner;
- `eta_eq_coordinateMaximum_add_eta_centered` in `Chap06/Proposition_6_23`, the chapter's stable
  max-shift identity for the same log-sum-exp potential;
- `smoothMaxInnerApproximation` in `Chap07/Definition_7_42`, the later affine-score smoothing
  owner built from the same log-sum-exp pattern;
- `logSumExpMaxEigenvalueSmoothing` in `Chap06/Definition_6_47`, the later Chapter 6 smoothing
  owner using the same positive-parameter surface.

Best owner abstraction:
- source-facing/core-canonical: `η`;
- bridge/view: the evaluation theorem `eta_apply`.

Primitive data:
- a finite index type `ι`;
- the positive smoothing parameter `μ : {μ : ℝ // 0 < μ}`;
- the score vector `u : EuclideanSpace ℝ ι`.

Derived API:
- the coordinate formula `eta_apply`.

Since Proposition 6.23 already owns `η` at the positive-parameter layer, this file recalls that
owner directly instead of keeping a second specialization wrapper.
-/

section

variable {ι : Type v} [Fintype ι]

/- Definition 6.27: the textbook finite-family log-sum-exp potential is the canonical Chapter 6
owner `η` for a positive smoothing parameter and a finite score family. -/
recall η

/- Evaluating the recalled owner gives the textbook positive-parameter log-sum-exp formula. -/
recall eta_apply

end
