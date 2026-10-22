/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/-
Definition 1.2.1 is a source-facing recall item in the Chapter 1 black-box optimization domain.

Sampled owner-style declarations:
- `Type u`, the core/canonical owner of the problem/query carrier itself
- `BlackBoxOptimizationProblemClass.model` in `Definition_1_2_4.lean`, which stores the model `Σ`
  directly as `Type u`
- `OptimizationOracle.IsLocal` in `Definition_1_2_13.lean`, whose problem parameter is again just a
  carrier type
- `GeneralIterativeScheme` in `Algorithm_1_2_10.lean`, which likewise uses the query space itself
  as a bare type parameter

Source/core/bridge triage:
- source-facing: the textbook model `Σ` of optimization problems
- core/canonical: the carrier type `Type u`
- bridge/view: downstream owner declarations such as oracle and stopping-rule maps built from this
  carrier

Owner abstraction:
- the visible problem or query space itself, namely a type `σ : Type u`

Primitive data:
- the carrier type `σ`

Derived API:
- oracle answer maps `σ → Answer` from Definition 1.2.2
- stopping predicates on an informational state from Definition 1.2.3
- transcript-based iterative schemes built from those owner objects in later files

There is no separate public wrapper such as `ProblemModel` or `ProblemState`. Later chapter files
use the carrier type directly, so the canonical main entry here is the type expression itself.
-/

/- Definition 1.2.1: for a problem `P`, its model `Σ` is the part of `P` known to a numerical
method; in this source-facing black-box optimization layer, that model is represented directly by
its carrier type. -/
#check (Type u)
