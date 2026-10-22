/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_27

noncomputable section

open scoped BigOperators

/- Algorithm 6.2 lies in the finite log-sum-exp stabilization domain.

Sampled owner-style declarations:
- `coordinateMaximum` in `Proposition_6_23`, the chapter owner for the maximal coordinate;
- `centeredByCoordinateMaximum` in `Proposition_6_23`, the canonical centered vector obtained by
  subtracting that maximal coordinate;
- `η` in `Definition_6_27`, the established chapter recall surface for the log-sum-exp potential;
- `eta_eq_coordinateMaximum_add_eta_centered` in `Proposition_6_23`, the chapter's stable
  log-sum-exp shift identity.

Best owner abstraction:
- source-facing: the stable max-shift decomposition of the log-sum-exp potential on `ℝ^m`;
- core/canonical: `coordinateMaximum`, `centeredByCoordinateMaximum`, `η`, and
  `eta_eq_coordinateMaximum_add_eta_centered`;
- bridge/view: the evaluation theorem `eta_apply`; no extra bridge is needed here.

Primitive data:
- the dimension `m : ℕ` together with `[NeZero m]`;
- the positive smoothing parameter `μ : {μ : ℝ // 0 < μ}`;
- the score vector `u : EuclideanSpace ℝ (Fin m)`.

Derived API:
- the centered vector `centeredByCoordinateMaximum u`;
- the stable decomposition
  `η μ u = coordinateMaximum u + η μ (centeredByCoordinateMaximum u)`.

Source/core/bridge triage:
- source-facing: Algorithm 6.2's stable shift identity;
- core/canonical: the owner declarations in `Proposition_6_23`, with `η` recalled again in
  `Definition_6_27`;
- bridge/view: no parallel restatement is kept beyond that existing chapter recall surface.

Earlier drafts kept a parallel public surface for the same stable-shift construction in the older
text file. This refinement removes that duplicate wheel and keeps Algorithm 6.2 as a recall-only
item that reuses the chapter owner directly. -/

section

variable {m : ℕ} [NeZero m]

/- Algorithm 6.2: given a positive smoothing parameter `μ` and a score vector `u ∈ ℝ^m`, let
`\bar u = coordinateMaximum u` and let `centeredByCoordinateMaximum u` be the vector obtained by
subtracting `\bar u` from every coordinate of `u`. Then the log-sum-exp potential is recovered by
the numerically stable shift formula
`η μ u = \bar u + η μ (centeredByCoordinateMaximum u)`. -/
recall eta_eq_coordinateMaximum_add_eta_centered

end
