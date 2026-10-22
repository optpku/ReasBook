/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_6
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_7

open scoped BigOperators
open scoped EuclideanSpaceLp

/- Definition 3.1.1.7 lies in the finite-dimensional `ℓ_p`-geometry domain.

Sampled owner-style declarations:
- `Seminorm.closedBall`
- `Seminorm.mem_closedBall`
- `EuclideanSpace.lpSeminorm`
- `EuclideanSpace.lpNorm_eq_sum`

Best owner abstraction:
- `(EuclideanSpace.lpSeminorm n p).closedBall x₀ r`

Primitive data:
- the ambient dimension `n : ℕ`
- the exponent `p : EuclideanSpace.LpExponent`
- the center `x₀ : EuclideanSpace ℝ (Fin n)`
- the radius `r : ℝ`

Derived API:
- the coordinate membership criterion below, obtained from the canonical owner membership lemma
  `Seminorm.mem_closedBall` and the coordinate formula `EuclideanSpace.lpNorm_eq_sum`

Source/core/bridge triage:
- source-facing: the coordinate description of the textbook `ℓ_p` closed ball
- core/canonical: `(EuclideanSpace.lpSeminorm n p).closedBall x₀ r`
- bridge/view: `mem_lp_closedBall_coord_iff`

The previous file duplicated `Seminorm.mem_closedBall` under the local name
`mem_lp_closedBall_iff`. Since the owner declaration is already recalled in
`Definition_3_1_1_6`, this file keeps only the genuine coordinate bridge. -/

/-- Definition 3.1.1.7: membership in the textbook `ℓ_p` closed ball centered at `x₀` and of
radius `r` is equivalent to the usual coordinate `ℓ_p` inequality. -/
theorem mem_lp_closedBall_coord_iff (n : ℕ) (p : EuclideanSpace.LpExponent)
    (x₀ x : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    x ∈ (EuclideanSpace.lpSeminorm n p).closedBall x₀ r ↔
      (∑ i, |(x - x₀) i| ^ p.toReal) ^ (1 / p.toReal : ℝ) ≤ r := by
  rw [(EuclideanSpace.lpSeminorm n p).mem_closedBall, EuclideanSpace.lpNorm_eq_sum (x - x₀) p]
