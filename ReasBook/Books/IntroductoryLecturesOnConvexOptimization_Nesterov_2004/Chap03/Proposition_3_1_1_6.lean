/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_7

-- Declarations for this item will be appended below by the statement pipeline.

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "e[" i "]" => EuclideanSpace.single i (1 : ℝ)

/- Proposition 3.1.1.6 lies in the chapter's finite-dimensional `ℓ₁`-geometry / convex-hull
domain.

Layer targeted by this refinement:
- source-facing proposition stated at the canonical `ℓ₁`-closed-ball owner layer

Sampled owner-style declarations:
- `EuclideanSpace.l1Seminorm`
- `Seminorm.closedBall`
- `l1_ball_eq_convexHull_signed_standard_basis_prop`

Best owner abstraction:
- `(EuclideanSpace.l1Seminorm n).closedBall x₀ r`

Primitive data:
- the ambient dimension `n : ℕ`
- the center `x₀ : E`
- the radius `r : ℝ`

Derived API:
- the convex-hull description of that closed ball by the signed standard-basis vertices, already
  established in `Proposition_3_7`

Dimension side condition:
- `0 < n`, excluding the degenerate `n = 0` case where the signed-vertex set is empty while the
  closed ball is nonempty for `r ≥ 0`

Source/core/bridge triage:
- source-facing: the `ℓ₁` closed ball / signed-vertex convex-hull equality
- core/canonical: `Seminorm.closedBall` for `EuclideanSpace.l1Seminorm n`
- bridge/view: this recall-only file

`Proposition_3_7` now already states the proposition on the canonical closed-ball owner surface.
Keeping a second theorem here with the same interface would only duplicate that owner-level API
under a different name, so this file is recall-only.
-/

recall l1_ball_eq_convexHull_signed_standard_basis_prop
    (hn : 0 < n) (x₀ : E) (r : ℝ) (hr : 0 ≤ r) :
    (EuclideanSpace.l1Seminorm n).closedBall x₀ r =
      convexHull ℝ
        (Set.range (fun i : Fin n ↦ x₀ + r • e[i]) ∪
          Set.range (fun i : Fin n ↦ x₀ - r • e[i]))
