/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Remark_6_1_1

-- Declarations for this item will be appended below by the statement pipeline.

/- Proposition 6.9 lies in the Euclidean prox-function / radius-bound domain.

Sampled owner-style declarations:
- `quadraticDistanceTo` in `Remark_6_1_1`, the chapter owner of the Euclidean prox term
  `d(x) = (1 / 2) ‖x - x₀‖²`;
- `two_mul_quadraticDistanceTo` in `Remark_6_1_1`, the canonical bridge from the prox term back
  to the squared distance;
- `euclidean_prox_radius_bound` in `Remark_6_1_1`, the earlier chapter theorem with the exact
  source-facing radius estimate used here.

Best owner abstraction:
- source-facing: the Euclidean prox radius estimate from the squared-distance hypothesis;
- core/canonical: `euclidean_prox_radius_bound`;
- bridge/view: `two_mul_quadraticDistanceTo`.

Primitive data:
- the Euclidean prox center `x₀` and comparison point `xStar`;
- the iterate family `v : ℕ → E`;
- the source squared-distance hypothesis
  `‖v k - xStar‖ ^ (2 : ℕ) ≤ 2 * quadraticDistanceTo x₀ xStar`.

Derived API:
- the Euclidean prox owner `quadraticDistanceTo`;
- the expansion lemma `two_mul_quadraticDistanceTo`;
- the radius conclusion `‖v k - xStar‖ ≤ ‖x₀ - xStar‖`.

Source/core/bridge triage:
- source-facing: Proposition 6.9's Euclidean prox radius estimate;
- core/canonical: `euclidean_prox_radius_bound`;
- bridge/view: the helper conversion `two_mul_quadraticDistanceTo`.

The previous file duplicated the earlier chapter owner declaration, helper lemma, and theorem
verbatim. Proposition 6.9 adds no new mathematics beyond that earlier canonical theorem, so this
file is a pure recall item. -/

/- Proposition 6.9 is the earlier Euclidean prox radius theorem
`euclidean_prox_radius_bound`. -/
recall euclidean_prox_radius_bound
