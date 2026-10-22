/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_5

-- Declarations for this item will be appended below by the statement pipeline.

section

universe u

variable {X : Type u} [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X]

/- Theorem 3.6 is recall-only in the chapter's closed-convex `WithTop ℝ`-valued function API.

Primary domain:
- closure properties of closed convex extended-real-valued functions on feasible sets, specialized
  in the source to the textbook `ℝⁿ` model and refined here to the owner ambient real module.

Sampled owner-style declarations in this domain:
- `ClosedConvexOn` from `Definition_3_1_1_5`, the chapter owner for closed convexity on a feasible
  set;
- `ClosedConvexOn.nonneg_smul` from `Theorem_3_1_5`, the owner nonnegative-scalar closure rule;
- `ClosedConvexOn.add_inter` from `Theorem_3_1_5`, the owner sum closure rule on intersected
  feasible sets;
- `ClosedConvexOn.max_inter` from `Theorem_3_1_5`, the owner pointwise-maximum closure rule on
  intersected feasible sets.

Best owner abstraction:
- `ClosedConvexOn`.

Primitive data:
- the owner witnesses `hf`, `hf₁`, `hf₂`;
- the scalar `β` together with the nonnegativity hypothesis `0 ≤ β`.

Derived API:
- `ClosedConvexOn.nonneg_smul`;
- `ClosedConvexOn.add_inter`;
- `ClosedConvexOn.max_inter`.

Source/core/bridge triage:
- source-facing: the three closure properties recorded under Theorem 3.6;
- core/canonical: the owner namespace `ClosedConvexOn`;
- bridge/view: this Euclidean specialization file, which should recall the owner theorems directly
  rather than keep a second public vocabulary `closedConvexOn_smul_nonneg`, `closedConvexOn_add`,
  and `closedConvexOn_max`.

The earlier file `Theorem_3_1_5` already owns these exact closure operations with the correct
chapter-level names and general ambient assumptions. This file therefore reuses those owner entries
directly instead of exporting parallel theorem shells in the `ℝⁿ` presentation.
-/

recall ClosedConvexOn.nonneg_smul

recall ClosedConvexOn.add_inter

recall ClosedConvexOn.max_inter

end
