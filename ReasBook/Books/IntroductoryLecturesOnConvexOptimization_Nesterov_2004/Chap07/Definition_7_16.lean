/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Proposition_7_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix

variable {m n : ℕ}

local notation "Eₘ" => EuclideanSpace ℝ (Fin m)

/- Definition 7.16 lies in the chapter's homogeneous linear-programming / dual-value domain.

Sampled owner-style declarations:
- mathlib `Matrix.fromCols`, the canonical matrix augmentation used in the source rank hypotheses
- Chapter 7 `homogeneousLinearProgrammingFeasibleSet` in `Proposition_7_3`
- Chapter 7 `mem_homogeneousLinearProgrammingFeasibleSet_iff` in `Proposition_7_3`
- Chapter 7 `homogeneousLinearProgrammingOptimalValue` and
  `homogeneousLinearProgrammingOptimalValue_eq_sSup` in `Proposition_7_3`

Best owner abstraction:
- source-facing: Definition 7.16's homogeneous linear-programming value `f*` for a pair
  `(hatA, c)` satisfying the source's standing rank assumptions
- core/canonical: the existing Chapter 7 owner `homogeneousLinearProgrammingOptimalValue hatA c`
- bridge/view: the coordinatewise feasible-set expansion below

Primitive data:
- `hatA : Matrix (Fin m) (Fin (n - 1)) ℝ`
- `c : Eₘ`

Derived API:
- `homogeneousLinearProgrammingFeasibleSet hatA`
- `homogeneousLinearProgrammingOptimalValue hatA c`

Source/core/bridge triage:
- source-facing: the textbook dual homogeneous linear-programming value `f*`
- core/canonical: the Chapter 7 feasible-set and optimal-value owners attached to `(hatA, c)`
- bridge/view: the coordinatewise membership reformulation below

The source also records rank assumptions on `hatA` and on the augmented matrix `(hatA, c)`, but
those assumptions do not enter the definitional bodies of the feasible set or optimal value. This
file therefore stays recall-first on the existing pair-based Chapter 7 owners and keeps the rank
conditions as surrounding mathematical context rather than packaging them into a new public owner.
-/

section

variable (hatA : Matrix (Fin m) (Fin (n - 1)) ℝ) (c : Eₘ)

/- Definition 7.16: the homogeneous linear-programming feasible set and optimal value are the
existing Chapter 7 owners attached to `(hatA, c)`. -/
recall homogeneousLinearProgrammingFeasibleSet
recall homogeneousLinearProgrammingOptimalValue
recall homogeneousLinearProgrammingOptimalValue_eq_sSup

end

/-- Membership in `homogeneousLinearProgrammingFeasibleSet hatA` means satisfying the linear
constraint `\hat Aᵀ u = 0` together with the coordinatewise bounds `|u⁽ⁱ⁾| ≤ 1`. -/
theorem mem_homogeneousLinearProgrammingFeasibleSet_iff_coordinatewise
    (hatA : Matrix (Fin m) (Fin (n - 1)) ℝ) (u : Eₘ) :
    u ∈ homogeneousLinearProgrammingFeasibleSet hatA ↔
      hatA.transpose.mulVec u = 0 ∧ ∀ i, |u i| ≤ 1 := by
  rw [mem_homogeneousLinearProgrammingFeasibleSet_iff, mem_coordinatewiseUnitBox_iff]

end
