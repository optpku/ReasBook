/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_3_6

-- Declarations for this item will be appended below by the statement pipeline.

/-
This item lies in the chapter's scalar parametric max-objective / value-function domain.

Primary domain:
- feasible-set infima of the two-term max objective `x ↦ max (f x - t) (fBar x)`.

Relevant owner declarations sampled before refining:
- `setConstrainedParametricObjective` in `Chap03/Lemma_3_3_6`, the chapter owner of the
  parametric function `x ↦ max (f x - t) (fBar x)`;
- `setConstrainedParametricObjective_apply` in `Chap03/Lemma_3_3_6`, the pointwise expansion of
  that owner;
- `parametricValueFunction` in `Chap03/Lemma_3_3_6`, the chapter owner of the feasible-set value
  function `t ↦ inf_{x ∈ Q} max (f x - t) (fBar x)`;
- `parametricValueFunction_eq_sInf_image` and `parametricValueFunction_def` in
  `Chap03/Lemma_3_3_6`, the canonical source-facing expansions of the same value function.

Best owner abstraction:
- the pair consisting of `setConstrainedParametricObjective f fBar` and
  `parametricValueFunction Q f fBar`.

Primitive data:
- feasible set `Q`;
- objective `f`;
- auxiliary function `fBar`.

Derived API:
- the pointwise evaluation formula for `setConstrainedParametricObjective`;
- the image and subtype/range infimum formulas for `parametricValueFunction`.

Source/core/bridge triage:
- source-facing: the textbook parametric function and its value function;
- core/canonical: the same chapter owners
  `setConstrainedParametricObjective f fBar` and `parametricValueFunction Q f fBar`;
- bridge/view: the source-facing infimum expansions already provided by
  `parametricValueFunction_eq_sInf_image` and `parametricValueFunction_def`.

This file is therefore recall-only and introduces no parallel wrapper API.
-/

/- Definition 3.74: the textbook parametric function
`f(t; x) = max {f(x) - t, \bar f(x)}` is the chapter owner
`setConstrainedParametricObjective f fBar`, and its value function
`f^*(t) = \min_{x ∈ Q} f(t; x)` is the owner `parametricValueFunction Q f fBar`. -/
recall setConstrainedParametricObjective

/- The associated value function is reused directly from the chapter owner. -/
recall parametricValueFunction

/- Evaluating the parametric function at `(t, x)` gives the displayed maximum formula. -/
recall setConstrainedParametricObjective_apply

/- Unfolding the value function gives the feasible-set image infimum of the parametric function.
-/
recall parametricValueFunction_eq_sInf_image

/- Rewriting over the feasible subtype recovers the displayed formula `min_{x ∈ Q} f(t; x)`. -/
recall parametricValueFunction_def
