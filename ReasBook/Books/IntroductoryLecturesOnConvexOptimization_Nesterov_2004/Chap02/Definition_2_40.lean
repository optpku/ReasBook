/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_39

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/- Definition 2.40 is a recall-only item in the finite max-type quadratic-regularization domain on
a real Hilbert space.

Sampled owner-style declarations:
* `maxTypeAffineApproximation` in `Definition_2_39`, the owner affine max-type model at `xBar`;
* `maxTypeAffineApproximation_apply`, the pointwise bridge for that affine model;
* `quadraticallyRegularizedObjective` in `Definition_1_4_17.lean`, the owner quadratic
  regularization of an objective;
* `quadraticallyRegularizedObjective_apply`, the pointwise bridge for the regularized objective.

Best owner abstraction:
* source-facing/core:
  `quadraticallyRegularizedObjective (maxTypeAffineApproximation fi xBar) γ xBar`;
* bridge/view: the pointwise expansion obtained by composing the two owner `..._apply` lemmas.

Primitive data:
* a nonempty finite component family `fi : ι → E → ℝ`;
* a base point `xBar : E`;
* a regularization parameter `γ : ℝ`.

Derived API:
* the affine max-type model `maxTypeAffineApproximation fi xBar`;
* the expanded value formula for the regularized max-type model.

Source/core/bridge triage:
* source-facing/core:
  `quadraticallyRegularizedObjective (maxTypeAffineApproximation fi xBar) γ xBar`;
* bridge/view: its pointwise expansion.

This file therefore recalls the composed owner expression directly and introduces no parallel local
alias such as `regularizedMaxTypeModel` or `proximalMaxLinearization`. -/

recall maxTypeAffineApproximation
recall maxTypeAffineApproximation_apply
recall quadraticallyRegularizedObjective
recall quadraticallyRegularizedObjective_apply

section

variable (fi : ι → E → ℝ) (γ : ℝ) (xBar : E)

set_option linter.hashCommand false in
#check quadraticallyRegularizedObjective (maxTypeAffineApproximation fi xBar) γ xBar

example (x : E) :
    quadraticallyRegularizedObjective (maxTypeAffineApproximation fi xBar) γ xBar x =
      Finset.univ.sup' Finset.univ_nonempty
          (fun i : ι ↦ fi i xBar + inner ℝ (∇ (fi i) xBar) (x - xBar)) +
        (γ / 2) * ‖x - xBar‖ ^ (2 : ℕ) := by
  rw [quadraticallyRegularizedObjective_apply, maxTypeAffineApproximation_apply]

end
