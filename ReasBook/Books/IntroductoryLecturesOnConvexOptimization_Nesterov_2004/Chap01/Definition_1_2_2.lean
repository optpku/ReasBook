/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {Query : Type u} {Answer : Type v}

/- Definition 1.2.2 is a source-facing recall item in the Chapter 1 black-box optimization
domain.

Layer targeted by this refinement:
* source-facing recall of the core/canonical owner object already used elsewhere in the chapter

Primary domain:
* black-box optimization oracles as answer maps on a query space

Relevant owner-style declarations sampled before refining:
* `GeneralIterativeScheme.oracle` in `Algorithm_1_2_10.lean`, which stores a single-problem
  oracle directly as `Query → Answer`;
* `OptimizationOracle.IsLocal` in `Definition_1_2_13.lean`, which treats class-level oracles as
  the curried answer rule `Problem → Query → Answer`;
* the direct zero-, first-, and second-order answer maps in `Definition_1_2_9.lean`, which use
  the same owner shape without introducing separate wrapper objects.

Owner abstraction:
* the function type `Query → Answer`

Primitive data:
* the query type `Query`
* the answer type `Answer`

Derived API:
* the class-of-problems generalization `Problem → Query → Answer` from Definition 1.2.8
* locality properties such as `OptimizationOracle.IsLocal` from Definition 1.2.13
* transcript-based algorithms that consume the oracle by evaluation

This recall file intentionally introduces no separate public wrapper such as `ProblemOracle`.
Downstream chapter files should use the function type `Query → Answer` directly. -/

#check (Query → Answer)
