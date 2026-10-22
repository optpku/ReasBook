/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_2_6

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 3.11 lies in the chapter's two-function closed-convex minimax domain.

Sampled owner-style declarations in this domain:
- `ClosedConvexOn` from `Definition_3_1_1_5`, the chapter owner for closed convexity on a feasible
  set
- `constrainedSublevelSet` from `Definition_3_3`, the owner constrained sublevel-set construction
- `IsMinimaxLinearizationParameter` from `Definition_3_1_2_3`, the source-facing owner predicate
  for two-function minimax linearization
- `exists_minimax_parameter_of_bounded_constrainedSublevelSets` from `Theorem_3_1_2_6`, the
  earlier chapter owner theorem with the exact canonical conclusion

Best owner abstraction:
- source-facing: the existence of a minimax linearization parameter for the maximum of two closed
  convex functions
- core/canonical: `exists_minimax_parameter_of_bounded_constrainedSublevelSets`
- bridge/view: this file only, which recalls the earlier owner theorem as the numbered textbook
  item without exporting a second theorem name

Primitive data:
- the feasible set `Q`
- two real-valued objectives `f₁`, `f₂ : E → ℝ`
- closed convexity of the canonical `WithTop` lifts of `f₁` and `f₂` on `Q`
- boundedness of the constrained sublevel sets of the pointwise maximum
  `x ↦ max (f₁ x) (f₂ x)` on `Q`

Derived API:
- a weight `lam : unitInterval`
- the owner conclusion
  `IsMinimaxLinearizationParameter (fun x : Q ↦ f₁ x) (fun x : Q ↦ f₂ x) lam`

Source/core/bridge triage:
- source-facing: Theorem 3.11 as the chapter's two-function minimax statement for the maximum of
  two closed convex functions
- core/canonical: `IsMinimaxLinearizationParameter` and
  `exists_minimax_parameter_of_bounded_constrainedSublevelSets`
- bridge/view: the `WithTop` lift in the hypotheses, used only to express the chapter's
  closed-convex owner assumptions

The previous version replaced the minimax-parameter conclusion by the weaker existence of an
attained weighted objective, and it added redundant hypotheses `Q.Nonempty` and `IsClosed Q`
instead of reusing the chapter owner theorem. This refinement removes that parallel wrapper and
keeps Theorem 3.11 as a direct recall of the canonical minimax-parameter owner. -/

/- Theorem 3.11: if `f₁` and `f₂` are real-valued functions whose canonical `WithTop` lifts are
closed and convex on a feasible set `Q`, and every constrained sublevel set of the pointwise
maximum `x ↦ max (f₁ x) (f₂ x)` on `Q` is bounded, then there exists a parameter `λ* ∈ [0, 1]`
for which the constrained minimum value of `x ↦ max (f₁ x) (f₂ x)` on `Q` equals that of the
convex combination `x ↦ λ* f₁ x + (1 - λ*) f₂ x`; Lean records this conclusion by the owner
predicate `IsMinimaxLinearizationParameter` on the subtype `Q`. -/
recall exists_minimax_parameter_of_bounded_constrainedSublevelSets
