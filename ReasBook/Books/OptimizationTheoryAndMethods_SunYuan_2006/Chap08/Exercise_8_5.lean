/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_3_2

/- Domain sampling:
* primary domain: Chapter 8 null-constraint directions for constrained optimization
* inspected project owners:
  `ConstrainedOptimizationProblem.IsKKTPoint` from `Theorem_8_2_7`
  `ConstrainedOptimizationProblem.sequentialNullConstraintDirections` and
  `ConstrainedOptimizationProblem.positiveActiveIneqIndexSet` from `Definition_8_3_1`
  `ConstrainedOptimizationProblem.linearizedNullConstraintDirections` and
  `ConstrainedOptimizationProblem.sequentialNullDirections_subset_linearizedNullDirections`
  from `Definition_8_3_2`
* owner abstraction chosen here: the existing Chapter 8 null-direction owner chain on
  `ConstrainedOptimizationProblem`
* primitive data live upstream in the constrained-problem/KKT/active-set owners
* derived API reused here: the canonical theorem sending `S(xStar, lamStar)` into
  `G(xStar, lamStar)` under the chapter's constraint-gradient hypothesis
* source/core/bridge triage:
  - source-facing exercise content: formula `(8.3.18)`
  - core/canonical owner: the Chapter 8 theorem
    `ConstrainedOptimizationProblem.sequentialNullDirections_subset_linearizedNullDirections`
  - bridge/view choice here: none; this exercise is already a recall-layer item
-/

/- Chapter08 Exercise 8.5: formula `(8.3.18)` is already the canonical Chapter 8 theorem
`ConstrainedOptimizationProblem.sequentialNullDirections_subset_linearizedNullDirections`
from `Definition_8_3_2`. This is the source-faithful statement because the upstream owner keeps
the needed constraint-gradient hypothesis explicit instead of relying on totalized `gradient`
outside its differentiability domain. -/
#check ConstrainedOptimizationProblem.sequentialNullDirections_subset_linearizedNullDirections
