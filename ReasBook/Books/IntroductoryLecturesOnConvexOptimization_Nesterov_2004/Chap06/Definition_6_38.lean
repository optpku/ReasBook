/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_39

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Definition 6.38 [Chapter6_1.json:87] lies in Chapter 6's excessive-gap certificate domain.

Sampled owner-style declarations:
- `satisfiesExcessiveGapConditionWithMu1Zero` in `Chap06/Definition_6_39`, the chapter owner for
  the `mu1 = 0` excessive-gap inequality `f_{mu2}(xBar) <= phi(uBar)`;
- `satisfiesExcessiveGapConditionWithMu1Zero_iff` in `Chap06/Definition_6_39`, the ambient-point
  expansion of the same owner.

Best owner abstraction:
- source-facing: the `mu1 = 0` excessive-gap condition on a feasible pair `(xBar, uBar)`;
- core/canonical: `satisfiesExcessiveGapConditionWithMu1Zero`;
- bridge/view: the ambient-point expansion theorem
  `satisfiesExcessiveGapConditionWithMu1Zero_iff`.

This item is recall-only in the current project: the exact source-facing notion is already exposed
canonically in `Definition_6_39`, so this file should not introduce a duplicate predicate or alias.
-/

section

variable {X : Type u} {U : Type v}
variable (Q₁ : Set X) (Q₂ : Set U)
variable (fμ₂ : Q₁ → ℝ) (φ : Q₂ → ℝ)
variable (xBar : Q₁) (uBar : Q₂)

/- Definition 6.38 [Chapter6_1.json:87]: a feasible pair `(xBar, uBar) in Q1 x Q2` satisfies the
excessive gap condition with `mu1 = 0` exactly when `f_{mu2}(xBar) <= phi(uBar)`, namely the
chapter owner `satisfiesExcessiveGapConditionWithMu1Zero`. -/
recall satisfiesExcessiveGapConditionWithMu1Zero

recall satisfiesExcessiveGapConditionWithMu1Zero_iff

end
