/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Lemma_5_2_2

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 5.2.5 lies in the Chapter 5 self-concordant path-following / shifted-dual-norm
domain.

Sampled owner declarations:
* `HessianDualLocalNorm.ofDetNeZero` in `Definition_5_0_20`, the canonical Hessian-dual-local-norm
  owner used to measure shifted gradients;
* `satisfies_approximate_centering_condition` in `Lemma_5_2_2`, the chapter source-facing owner
  for the approximate centering condition;
* `satisfies_approximate_centering_condition_iff` in `Lemma_5_2_2`, the companion specification
  theorem expanding that owner back to the textbook inequality.

Best owner abstraction:
* source-facing: the approximate centering condition for the tilted objective `ψ(t; ·)`;
* core/canonical: the shifted-gradient dual-local-norm inequality built from
  `HessianDualLocalNorm.ofDetNeZero`;
* bridge/view: `satisfies_approximate_centering_condition_iff`.

Primitive data:
* the objective `f`;
* the base point `y₀`;
* the path parameter `t`;
* the evaluation point `y`;
* Hessian positivity and nondegeneracy at `y`;
* the centering parameters `M_f` and `β`.

Derived API:
* the owner predicate `satisfies_approximate_centering_condition`;
* its expansion theorem `satisfies_approximate_centering_condition_iff`.

This file is therefore a pure recall item. Keeping a second local definition here would duplicate
the Chapter 5 owner already introduced in `Lemma_5_2_2` and split downstream vocabulary for the
same source-facing notion. -/

/- Definition 5.2.5 recalls the chapter owner for the approximate centering condition. -/
recall satisfies_approximate_centering_condition

/- The textbook inequality form is the canonical companion specification theorem. -/
recall satisfies_approximate_centering_condition_iff
