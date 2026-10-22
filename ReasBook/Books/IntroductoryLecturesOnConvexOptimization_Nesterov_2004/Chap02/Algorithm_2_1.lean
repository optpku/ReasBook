/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Algorithm_1_6_1

-- Declarations for this item will be appended below by the statement pipeline.

/- Algorithm 2.1 is a recall-only item in the domain of recursive first-order optimization
trajectories.

Sampled owner-style declarations:
- `gradientMethod`
- `gradientMethod_zero`
- `gradientMethod_succ`
- `gradientMethod_const_eq_iterate`

Source/core/bridge triage:
- source-facing/core: the recursive trajectory owner `gradientMethod stepSize f x0`
- bridge/view: the constant-step iterate description `gradientMethod_const_eq_iterate`

Primitive data:
- the step-size schedule `stepSize`
- the objective `f`
- the initial point `x0`

Derived API:
- the base-point identity `gradientMethod_zero`
- the one-step recursion `gradientMethod_succ`
- the constant-step iterate bridge `gradientMethod_const_eq_iterate`

Chapter 2 therefore reuses the Chapter 1 owner directly and keeps only canonical recalls of that
API, rather than repeating its full binder telescope or introducing a Euclidean-model wrapper. -/
recall gradientMethod

recall gradientMethod_zero

recall gradientMethod_succ

recall gradientMethod_const_eq_iterate
