/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_31

/- Definition 6.32 [Chapter6_1.json:70] lies in the chapter's prox-function / prox-center domain.

Sampled owner declarations:
- `NesterovIsProxFunction` in `Chap06/Definition_6_31`, the chapter's canonical owner for continuity and
  unit strong convexity with respect to a chosen norm;
- `NesterovIsProxCenter` in `Chap06/Definition_6_31`, the chapter's canonical owner for a feasible
  minimizer normalized by the condition `d₁ x₀ = 0`;
- mathlib `ContinuousOn`, `IsMinOn`, and the project owner `StrongConvexOnWith`, which are the
  core ingredients packaged by those two chapter declarations.

Source/core/bridge triage:
- source-facing: the prox-function condition on `Q₁` and the normalized prox-center condition at
  `x₀`;
- core/canonical: `NesterovIsProxFunction p Q₁ d₁` and `NesterovIsProxCenter Q₁ d₁ x₀`;
- bridge/view: the field projections `continuousOn`, `strongConvexOnWith`, `mem`, `isMinOn`, and
  `value_eq_zero`.

This numbered definition only recalls notions already introduced canonically in the chapter. The
file therefore keeps a direct recall surface rather than introducing duplicate aliases or wrapper
predicates.
-/

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (p : Seminorm ℝ E) [Seminorm.IsNorm p]
variable (Q₁ : Set E) (d₁ : E → ℝ) (x₀ : E)

/- Definition 6.32 [Chapter6_1.json:70]: a prox-function on `Q₁` with respect to the norm `p`
is the chapter's canonical owner `NesterovIsProxFunction p Q₁ d₁`; a prox-center is the canonical
normalized minimizer owner `NesterovIsProxCenter Q₁ d₁ x₀`. -/
recall NesterovIsProxFunction
recall NesterovIsProxFunction.continuousOn
recall NesterovIsProxFunction.strongConvexOnWith
recall NesterovIsProxCenter
recall NesterovIsProxCenter.mem
recall NesterovIsProxCenter.isMinOn
recall NesterovIsProxCenter.value_eq_zero

set_option linter.hashCommand false in
#check NesterovIsProxFunction p Q₁ d₁

set_option linter.hashCommand false in
#check NesterovIsProxCenter Q₁ d₁ x₀

end
