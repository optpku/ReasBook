/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_14

-- Declarations for this item will be appended below by the statement pipeline.

/-
Primary domain: constrained minimization for strongly convex functions on finite-dimensional real
normed spaces.

Sampled owner-style declarations:
* project `StrongConvexOnWith` in `Definition_2_14`
* project `StrongConvexOnWith.exists_pos_strongConvexOn` in `Definition_2_14`
* project `StrongConvexOnWith.existsUnique_isMinOn_of_isClosed` in `Definition_2_14`
* project `StrongConvexOn.existsUnique_isMinOn_of_isClosed` in `Theorem_3_45`

Best owner abstraction:
* source-facing/core: `StrongConvexOnWith p μ Q f`

Primitive data:
* the normed seminorm `p`
* the feasible set `Q`
* the objective `f`
* the owner predicate `StrongConvexOnWith p μ Q f`

Derived API:
* `StrongConvexOnWith.exists_pos_strongConvexOn`, the bridge to Euclidean `StrongConvexOn`
* `StrongConvexOnWith.existsUnique_isMinOn_of_isClosed`, the owner unique-minimizer theorem
* `StrongConvexOn.existsUnique_isMinOn_of_isClosed`, the lower-level Euclidean theorem used by the
  bridge

Source/core/bridge triage:
* source-facing: the unique constrained minimizer conclusion for the textbook arbitrary-norm
  hypothesis
* core/canonical: `StrongConvexOnWith.existsUnique_isMinOn_of_isClosed`
* bridge/view: the internal passage through `StrongConvexOnWith.exists_pos_strongConvexOn`

This numbered theorem is direct owner API for `StrongConvexOnWith`, so the declaration now lives
with the rest of that owner in `Definition_2_14`. This file is recall-only and keeps no parallel
theorem shell.
-/

/- Theorem 2.32 is the direct owner recall of the closed-set unique-minimizer theorem for
`StrongConvexOnWith`. -/
recall StrongConvexOnWith.existsUnique_isMinOn_of_isClosed
