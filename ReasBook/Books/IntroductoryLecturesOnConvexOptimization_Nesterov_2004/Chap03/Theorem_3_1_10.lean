/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_2_6

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 3.1.10 lies in the chapter's two-function minimax-linearization domain.

Sampled owner-style declarations:
- `constrainedSublevelSet`
- `ClosedConvexOn`
- `IsMinimaxLinearizationParameter`
- `exists_minimax_parameter_of_bounded_constrainedSublevelSets`

Best owner abstraction:
- source-facing:
  Theorem 3.1.10 as the Euclidean textbook presentation of the bounded-sublevel-set minimax
  statement
- core/canonical:
  `exists_minimax_parameter_of_bounded_constrainedSublevelSets`
- bridge/view:
  this file only, which recalls the earlier owner theorem instead of exporting a second local
  theorem or a non-exported `example`

Primitive data:
- a feasible set `Q : Set E`
- two real-valued objectives `f₁`, `f₂ : E → ℝ`
- closed convexity of their `WithTop` lifts on `Q`
- boundedness of the constrained sublevel sets of the pointwise maximum
  `x ↦ max (f₁ x) (f₂ x)` on `Q`

Derived API:
- the minimizing parameter `lam : unitInterval`
- the owner predicate
  `IsMinimaxLinearizationParameter (fun x : Q ↦ f₁ x) (fun x : Q ↦ f₂ x) lam`

Source/core/bridge triage:
- source-facing: the textbook Euclidean presentation of the two-function minimax statement
- core/canonical: `exists_minimax_parameter_of_bounded_constrainedSublevelSets`
- bridge/view: this numbered file, which reuses the earlier owner theorem directly

The earlier file already owns the exact mathematical content with the chapter's canonical
`constrainedSublevelSet` API. This file therefore recalls that theorem directly rather than
maintaining a parallel local wrapper or a non-exported restatement.
-/

/- Theorem 3.1.10: if `f₁` and `f₂` are real-valued functions whose canonical `WithTop` lifts are
closed and convex on a feasible set `Q`, and every constrained sublevel set of the pointwise
maximum `x ↦ max (f₁ x) (f₂ x)` on `Q` is bounded, then there exists a parameter
`λ* ∈ [0, 1]` for which the constrained minimum value of `x ↦ max (f₁ x) (f₂ x)` on `Q` equals
that of the convex combination `x ↦ λ* f₁ x + (1 - λ*) f₂ x`; Lean records this conclusion by the
owner predicate `IsMinimaxLinearizationParameter` on the subtype `Q`. -/
recall exists_minimax_parameter_of_bounded_constrainedSublevelSets
