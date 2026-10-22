/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

variable {Problem : Type u} {Query : Type v} {Answer : Type w}

/- Definition 1.2.8 is a recall item in the Chapter 1 black-box optimization-oracle domain.
The canonical owner is the curried class-oracle type `Problem → Query → Answer`; fixed-problem
evaluations `oracle problem : Query → Answer` and locality predicates such as
`OptimizationOracle.IsLocal` are derived views built on top of this owner. -/

/- Definition 1.2.8: an optimization oracle for problem instances in `Problem` and query points in
`Query` is just a curried answer rule `Problem → Query → Answer`. -/
#check (Problem → Query → Answer)
