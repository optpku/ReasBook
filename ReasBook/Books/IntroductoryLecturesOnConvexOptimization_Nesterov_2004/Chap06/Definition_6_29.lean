/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_31

/- Definition 6.29 lies in the chapter's prox-function / prox-center domain.

Sampled owner-style declarations:
- `NesterovIsProxFunction` in `Definition_6_31`, the chapter's canonical owner for the
  prox-function hypothesis on `d`;
- `NesterovIsProxCenter` in `Definition_6_31`, the chapter's canonical owner for the
  normalized prox-center condition;
- project `StrongConvexOnWith`, the chapter owner reused by `NesterovIsProxFunction`;
- mathlib `IsMinOn`, the ambient minimizer owner reused by `NesterovIsProxCenter`.

Best owner abstraction:
- source-facing: the prox-function condition on `Q` and the normalized
  prox-center condition at `x₀`;
- core/canonical: `NesterovIsProxFunction Q d` and `NesterovIsProxCenter Q d x₀`;
- bridge/view: this numbered item is a recall-only surface for those canonical
  owners rather than a second pair of duplicate local definitions.

Primitive data:
- the norm-like seminorm `p`, the feasible set `Q`, the prox-function
  candidate `d`, and the candidate center `x₀`.

Derived API:
- `NesterovIsProxFunction.continuousOn` and `NesterovIsProxFunction.strongConvexOnWith`;
- `NesterovIsProxCenter.mem`, `NesterovIsProxCenter.isMinOn`, and
  `NesterovIsProxCenter.value_eq_zero`.

The previous version duplicated the prox owners with the separate public names
`is_prox_function_on` and `is_prox_center_on`. Those notions already have a
canonical chapter owner in `Definition_6_31`, so this file now keeps only the
direct recall surface.
-/

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (p : Seminorm ℝ E) [Seminorm.IsNorm p]

variable (Q : Set E) (d : E → ℝ) (x₀ : E)

/- Definition 6.29 uses the chapter's canonical prox-function owner and the
canonical normalized prox-center owner. -/
recall NesterovIsProxFunction
recall NesterovIsProxFunction.continuousOn
recall NesterovIsProxFunction.strongConvexOnWith
recall NesterovIsProxCenter
recall NesterovIsProxCenter.mem
recall NesterovIsProxCenter.isMinOn
recall NesterovIsProxCenter.value_eq_zero

set_option linter.hashCommand false in
#check NesterovIsProxFunction p Q d

set_option linter.hashCommand false in
#check NesterovIsProxCenter Q d x₀

end
