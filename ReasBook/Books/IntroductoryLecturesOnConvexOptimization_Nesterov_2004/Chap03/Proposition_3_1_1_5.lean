/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Proposition 3.1.1.5 lies in the chapter's closed-convex `WithTop`-valued convex-analysis
domain.

Primary domain:
- closed convexity of seminorm functions on finite-dimensional real normed spaces, with the
  textbook `ℝⁿ` case as a specialization.

Sampled owner-style declarations:
- `ClosedConvexOn` and `ClosedConvexFunction` in `Definition_3_1_1_5`, the chapter owners for
  closed convex extended-real-valued functions;
- `Seminorm.closedConvexFunction` in `Proposition_3_6`, the existing chapter theorem giving the
  canonical owner statement for `x ↦ p x`;
- mathlib `Seminorm.convexOn`, the canonical convexity owner behind the theorem;
- mathlib `ConvexOn.continuousOn`, the canonical continuity bridge on the open owner domain
  `Set.univ`.

Best owner abstraction:
- `ClosedConvexFunction (fun x : E ↦ (p x : WithTop ℝ))`.

Primitive data:
- a seminorm `p : Seminorm ℝ E`.

Derived API:
- the owner theorem `Seminorm.closedConvexFunction`;
- the `ClosedConvexOn Set.univ` specialization obtained from the owner abbreviation because norm
  functions are finite everywhere.

Source/core/bridge triage:
- source-facing: the proposition that a norm function is closed and convex on all of `ℝⁿ`;
- core/canonical: `ClosedConvexFunction` / `ClosedConvexOn`;
- bridge/view: the identification of the norm function's effective domain with `Set.univ`.

This file is therefore recall-only. `Proposition_3_6` already introduced the correct owner-level
theorem in the minimal chapter closure, so keeping another named theorem here would only duplicate
that API under a second shell. -/

recall Seminorm.closedConvexFunction
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (p : Seminorm ℝ E) :
    ClosedConvexFunction (fun x : E ↦ (p x : WithTop ℝ))
