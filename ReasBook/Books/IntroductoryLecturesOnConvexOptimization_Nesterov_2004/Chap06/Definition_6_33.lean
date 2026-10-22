/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Theorem_6_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Definition 6.33 lies in the chapter's excessive-gap certificate domain.

Sampled owner-style declarations:
- `satisfiesExcessiveGapCondition` in `Chap06/Definition_6_34`, the chapter's canonical owner for
  the excessive-gap inequality `f_{μ₂}(\bar x) ≤ φ_{μ₁}(\bar u)`;
- `satisfiesExcessiveGapCondition_iff` in `Chap06/Definition_6_34`, the ambient-point expansion of
  the same owner;
- `raw_duality_gap_le_excessive_gap_budget` in `Chap06/Lemma_6_2_1`, which already consumes this
  condition through the chapter owner.

Best owner abstraction:
- source-facing: the excessive-gap condition on a feasible pair;
- core/canonical: `satisfiesExcessiveGapCondition`;
- bridge/view: the ambient-point expansion theorem in `Definition_6_34`.

This numbered definition is recall-only in the current project: the exact source-facing notion is
already exposed canonically in `Definition_6_34`, so this file should not introduce a duplicate
predicate or alias.
-/

section

variable {X : Type u} {U : Type v}
variable (Q₁ : Set X) (Q₂ : Set U)
variable (fμ₂ : X → ℝ) (φμ₁ : U → ℝ)
variable (xBar : Q₁) (uBar : Q₂)

/- Definition 6.33 [Chapter6_1.json:71]: a feasible pair `(xBar, uBar) ∈ Q₁ × Q₂` satisfies the
excessive gap condition exactly when the smoothed primal value `f_{μ₂}(xBar)` is bounded above by
the smoothed dual value `φ_{μ₁}(uBar)`, namely the chapter owner
`satisfiesExcessiveGapCondition`. -/
recall satisfiesExcessiveGapCondition

end
