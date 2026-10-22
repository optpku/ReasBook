/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 5.0.11 lies in the Hessian-induced local-norm domain.

Sampled owner declarations:
* `hessian` in `Chap01/Definition_1_4_16`, the intrinsic second-order owner;
* `secondDirectionalDerivative_eq_hessian_quadratic_form` in `Definition_5_0_10`, the bridge from
  directional differentiation to the Hessian quadratic form;
* `hessianLocalNorm` in `Definition_5_1_1`, the chapter owner for the local norm induced by the
  Hessian;
* `hessianLocalNorm_def`, the source-facing square-root expansion theorem.

Best owner abstraction:
* source-facing: the primal local norm of a direction at a point;
* core/canonical: `hessianLocalNorm f x h`;
* bridge/view: `hessianLocalNorm_def`.

Primitive data:
* a function `f`;
* a base point `x`;
* a direction `h`.

Derived API:
* the canonical local norm owner `hessianLocalNorm`;
* its source-facing notation `‖h‖[f; x]`;
* the square-root expansion theorem `hessianLocalNorm_def`.

This file therefore does not keep a parallel `primalLocalNorm` wrapper. The project already owns
the notion canonically as `hessianLocalNorm`, so Definition 5.0.11 is refined to a direct recall
of that owner and its defining expansion. -/

/- Definition 5.0.11 recalls the canonical Hessian local norm owner for the textbook primal local
norm. -/
recall hessianLocalNorm

/- The source-facing square-root formula is the owner expansion theorem. -/
recall hessianLocalNorm_def
