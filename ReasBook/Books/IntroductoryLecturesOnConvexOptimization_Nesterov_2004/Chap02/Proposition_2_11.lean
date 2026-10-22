/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Algorithm_2_4

-- Declarations for this item will be appended below by the statement pipeline.

/- Proposition 2.11 is recall-only.

Primary domain:
- type-II accelerated Euclidean momentum recurrences.

Sampled owner-style declarations:
- `OptimalMethodRecurrence.y_eq` in `Algorithm_2_2`, the heavier interpolation formula from
  which the type-II momentum update is derived;
- `OptimalMethodRecurrence.gamma_succ_eq_L_mul_sq` in `Algorithm_2_2`, the heavier curvature
  identity used in the same elimination;
- `constantStepSchemeIIAlpha_succ_equation` in `Algorithm_2_4`, the source-facing scalar
  recurrence for Algorithm 2.4;
- `constantStepSchemeIIY_succ` in `Algorithm_2_4`, the source-facing momentum update
  `y_{k+1} = x_{k+1} + β_k (x_{k+1} - x_k)`.

Best owner abstraction:
- the recursive source-facing trajectory `constantStepSchemeII` for Proposition 2.11 itself;
- `OptimalMethodRecurrence` only as upstream bridge/provenance for the eliminated auxiliary
  parameters.

Primitive data:
- the recursive trajectory `constantStepSchemeII` together with
  `constantStepSchemeIIAlpha_succ_equation` and `constantStepSchemeIIY_succ`.

Derived API:
- the textbook coefficient `β_k`;
- the derivation from the heavier optimal-method owner via `y_eq` and
  `gamma_succ_eq_L_mul_sq`.

Source/core/bridge triage:
- source-facing: Proposition 2.11's displayed type-II scalar and momentum formulas;
- core/canonical: `ConstantStepSchemeIIMomentumRecurrence`;
- bridge/view: `constantStepSchemeIIToMomentumRecurrence`, together with elimination of the
  heavier optimal-method fields `v`, `γ` via `y_eq` and `gamma_succ_eq_L_mul_sq`.

This file therefore recalls the source-facing Algorithm 2.4 theorems directly. The generic
momentum owner remains background provenance available through
`constantStepSchemeIIToMomentumRecurrence`, but the main labeled entry stays on the textbook
recursive trajectory. This file intentionally adds no local
`estimatingSequenceMomentumCoefficient` wrapper and no parallel proposition-specific momentum
theorem. -/

recall constantStepSchemeIIAlpha_succ_equation
recall constantStepSchemeIIY_succ
