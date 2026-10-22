/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_5_6

-- Declarations for this item will be appended below by the statement pipeline.

/- Corollary 3.1.6 is a recall-only item in the chapter's convex-analysis/subdifferential domain.

Sampled owner-style declarations:
- `subdifferential`
- `mem_subdifferential_iff`
- `subgradient_nonneg_on_sublevelSet_of_mem_subdifferential`
- `subgradient_inner_sub_nonneg_of_isMinOn`

Best owner abstraction:
- the canonical subdifferential owner API together with the owner theorem
  `subgradient_nonneg_on_sublevelSet_of_mem_subdifferential`

Primitive data:
- a set `Q`, a function `f`, points `x0`, `xStar`, `g`
- the membership hypothesis `x0 ∈ Q`
- the minimizer hypothesis `IsMinOn f Q xStar`
- the subdifferential-membership hypothesis `g ∈ subdifferential f x0`

Derived API:
- the pairing inequality `0 ≤ inner ℝ g (x0 - xStar)`

Source/core/bridge triage:
- source-facing: the corollary that every subgradient at a feasible point has nonnegative pairing
  with the displacement to a minimizer
- core/canonical: the subdifferential owner API and the owner theorem
  `subgradient_nonneg_on_sublevelSet_of_mem_subdifferential`
- bridge/view: the existing chapter theorem `subgradient_inner_sub_nonneg_of_isMinOn`, which
  already has the exact corollary interface

This item therefore keeps only the direct recall of that source-facing bridge theorem instead of
introducing a second local wrapper around the owner abstraction. -/

recall subgradient_inner_sub_nonneg_of_isMinOn
