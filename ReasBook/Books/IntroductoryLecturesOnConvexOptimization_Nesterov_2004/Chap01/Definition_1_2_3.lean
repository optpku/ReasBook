/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {State : Type u}

/- Definition 1.2.3 is a source-facing recall in the black-box stopping-criterion domain.

Layer targeted by this refinement:
* source-facing recall of the core/canonical owner expression already used elsewhere in Chapter 1

Primary domain:
* stopping predicates on the informational state of a black-box method

Relevant owner-style declarations sampled before refining:
* `Set` in mathlib, the owner type of accepted-state predicates;
* `Set.mem_setOf` in mathlib, the canonical bridge between the set and predicate views;
* `GeneralIterativeScheme.shouldStop` in `Algorithm_1_2_10.lean`, which stores the stopping rule
  directly as `Set (Set (Query × Answer))`;
* `GeneralIterativeScheme.HaltsAt` in `Algorithm_1_2_10.lean`, which derives halting from
  membership in that accepted-state set.

Source/core/bridge triage:
* source-facing: the `ε`-stopping rule itself;
* core/canonical: the accepted-state set `Set State`;
* bridge/view: `Set.mem_setOf`, which converts between set-builder and predicate syntax.

Owner abstraction:
* the accepted-state predicate/set `Set State`

Primitive data:
* the informational-state type `State`
* the accepted-state set itself

Derived API:
* set-builder membership via `Set.mem_setOf`
* downstream consumers such as `GeneralIterativeScheme.shouldStop`
* halting predicates such as `GeneralIterativeScheme.HaltsAt`

This recall file intentionally introduces no separate public wrapper such as `StoppingCriterion`.
The positivity witness `0 < ε` belongs to the ambient method/problem data that owns the stopping
rule, not to the stopping rule itself. -/

#check (Set State)

recall Set.mem_setOf
    {x : State} {p : State → Prop} :
    x ∈ {y | p y} ↔ p x
