/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_8_19

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 5.4.8.8 lies in the Chapter 5 finite exponential-sum convexity domain.

Sampled owner declarations:
* `sumOfExponentials` from `Definition_5_4_8_19`, the source-facing owner for the exponential sum
  `y ↦ ∑ⱼ αⱼ exp ⟪aⱼ, y⟫`;
* `sumOfExponentials_apply`, the defining evaluation bridge for that owner;
* `sumOfExponentials_convex`, the upstream chapter owner theorem proving whole-space convexity
  under the mathematically weaker nonnegativity hypothesis on the coefficients.

Best owner abstraction:
* source-facing: the textbook positive-coefficient convexity statement for `sumOfExponentials`;
* core/canonical: `sumOfExponentials_convex`;
* bridge/view: specializing the owner theorem from nonnegative coefficients to strictly positive
  coefficients.

Primitive data:
* the coefficient family `α₁, …, αᵣ`;
* the vectors `a₁, …, aᵣ`.

Derived API:
* the whole-space convexity conclusion for `sumOfExponentials`.

Source/core/bridge triage:
* source-facing: the positive-coefficient textbook theorem;
* core/canonical: `sumOfExponentials_convex`;
* bridge/view: the implication `0 < αⱼ → 0 ≤ αⱼ`.

This numbered item adds no new mathematical owner beyond the canonical theorem already proved in
`Definition_5_4_8_19`. Since the project already exposes the stronger reusable owner statement
with nonnegative coefficients, this file keeps only the direct recall surface; the textbook
strict-positivity specialization should be obtained from `sumOfExponentials_convex` at the call
site when needed.
-/

recall sumOfExponentials_convex
