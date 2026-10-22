/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_22

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 3.1.22 lies in the chapter's parametric minimax / convex-analysis domain.

Sampled owner-style declarations:
- the slice-infimum value function `u ↦ sInf ((fun x ↦ Ψ x u) '' P)`
- `ClosedConvexOn.max_inter`
- `exists_minimax_parameter_of_bounded_constrainedSublevelSets`
- `exists_isMinOn_parametricMaximumObjective_eq_valueFunction_of_valueFunction_maximizer`

Best owner abstraction:
- source-facing: the attained minimum of the two-slice maximum together with its value-function
  identification at a maximizing parameter;
- core/canonical: the Chapter 3 owner theorem
  `exists_isMinOn_parametricMaximumObjective_eq_valueFunction_of_valueFunction_maximizer`;
- bridge/view: the internal `WithTop` lift used only in the theorem's slice-geometry hypotheses.

Primitive data:
- the feasible set `P`
- the parameter set `S`
- the real-valued kernel `Ψ`
- nonemptiness of `P`, which lets the dual closed-concavity owner recover `Convex ℝ S`
- closed-convexity and bounded constrained sublevel sets of the primal slices
- closed-concavity of the dual slices, encoded canonically by closed convexity of `u ↦ -Ψ(x, u)`
- the canonical maximizing-parameter datum
  `uStar ∈ S ∧ IsMaxOn (fun u ↦ sInf ((fun x ↦ Ψ x u) '' P)) S uStar`

Derived API:
- the attained minimizer of `x ↦ max (Ψ x u) (Ψ x uStar)`
- the equality of that minimum value with `sInf ((fun x ↦ Ψ x uStar) '' P)`

Source/core/bridge triage:
- source-facing: the textbook minimum-attainment statement for the maximum of two parameter
  slices of a convex-concave kernel;
- core/canonical: the earlier Chapter 3 theorem above;
- bridge/view: the internal `WithTop` lift used by the closed-convex owner API.

The previous file introduced a second public theorem stated through the later wrapper
`maximinLowerValue`, weakened the conclusion to a bare `sInf` equality, and kept redundant convexity
data in the local API. This refinement removes that duplicate wrapper layer and makes the numbered
item a direct recall of the canonical owner theorem from `Lemma_3_22`.
-/

recall exists_isMinOn_parametricMaximumObjective_eq_valueFunction_of_valueFunction_maximizer
