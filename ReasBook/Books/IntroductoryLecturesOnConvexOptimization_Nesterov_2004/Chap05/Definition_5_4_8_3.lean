/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_8_1

-- Declarations for this item will be appended below by the statement pipeline.

namespace SeparableOptimizationProblem

universe u

variable {E : Type u} [AddCommGroup E] [Module ℝ E] {m : ℕ}

/- Definition 5.4.8.3 lies in the separable optimization / standard-form epigraph domain.

Sampled owner-style declarations:
- `SeparableOptimizationProblem` from `Definition_5_4_8_1`, the source-facing owner of the block
  data `mᵢ`, affine functionals `ℓᵢⱼ`, and scalar functions `fᵢⱼ`;
- `StandardFormDecisionVariable` from `Theorem_5_4_8_1`, the chapter's owner for the standard-form
  variables `(x, τ, t)`;
- `StandardFormDecisionVariable.epigraphSlack`, the canonical projection exposing the slack family
  `τ : Fin (m + 1) → ℝ`;
- `StandardFormDecisionVariable.termSlack`, the canonical projection exposing the block family
  `t_{i,j}`.

Best owner abstraction:
- source-facing: the textbook slack coordinates `τ` and `t_{i,j}` of a standard-form decision
  variable;
- core/canonical: `StandardFormDecisionVariable problem`;
- bridge/view: the projections `epigraphSlack` and `termSlack`.

Primitive data:
- the original point `x`;
- the slack family `τ`;
- the block family `t`.

Derived API:
- `decision.epigraphSlack : Fin (m + 1) → ℝ`;
- `decision.termSlack i : Fin (problem.blockSize i) → ℝ`.

Source/core/bridge triage:
- source-facing: the slack-coordinate surface `(τ, t)` appearing in the standard-form variables;
- core/canonical: `StandardFormDecisionVariable problem`;
- bridge/view: its coordinate projections.

This numbered item therefore does not keep a second owner for `(τ, t)`: the slack variables are
recalled through the canonical owner `StandardFormDecisionVariable problem`, and only their
coordinate projections are exposed on the public surface. The `τ` surface is still read through
the weaker finite-family type `Fin (m + 1) → ℝ` rather than the over-concrete model
`EuclideanSpace ℝ (Fin (m + 1))`. -/

/- Definition 5.4.8.3 recalls the canonical owner whose projections supply the slack variables. -/
recall StandardFormDecisionVariable

/- Definition 5.4.8.3 uses the canonical slack-coordinate projections. -/
recall StandardFormDecisionVariable.epigraphSlack
recall StandardFormDecisionVariable.termSlack

end SeparableOptimizationProblem
