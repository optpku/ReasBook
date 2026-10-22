/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_39
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_21

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {m : ℕ}

/- Definition 2.46 lies in the constrained max-type affine-linearization domain on a real Hilbert
space.

Sampled owner-style declarations:
* `LagrangianProblem.constrainedAuxiliaryComponents` in `Lemma_2_21`, the canonical finite
  component family encoding the shifted objective and the constraint functions;
* `LagrangianProblem.constrainedAuxiliaryComponents_zero` and
  `LagrangianProblem.constrainedAuxiliaryComponents_succ` in `Lemma_2_21`, the source-facing
  split of index `0` versus the successor constraint indices;
* `maxTypeAffineApproximation` in `Definition_2_39`, the owner affine linearization of a finite
  max-type family at a base point;
* `maxTypeAffineApproximation_apply` in `Definition_2_39`, the pointwise bridge for that owner
  affine model;
* `firstOrderTaylorModelAt` in `Chap01/Definition_1_4_17`, the canonical affine owner of each
  single component.

Best owner abstraction:
* `maxTypeAffineApproximation (problem.constrainedAuxiliaryComponents t) xBar`.

Primitive data:
* the owner constrained problem `problem : LagrangianProblem E m`;
* the parameter `t` and base point `xBar`.

Derived API:
* the pointwise evaluation formula from `maxTypeAffineApproximation_apply`;
* the source-facing `0`/`i.succ` split of
  `problem.constrainedAuxiliaryComponents t` from
  `constrainedAuxiliaryComponents_zero` and `constrainedAuxiliaryComponents_succ`.

Source/core/bridge triage:
* source-facing: the affine model whose component `0` is the shifted objective affine term and
  whose successor components are the constraint affine terms;
* core/canonical: `maxTypeAffineApproximation (problem.constrainedAuxiliaryComponents t) xBar`;
* bridge/view: `maxTypeAffineApproximation_apply` together with the zero/successor component
  simplification lemmas from `Lemma_2_21`.

Definition 2.46 therefore uses the chapter owner expression directly. This file is recall-only:
it introduces no parallel public `functionalConstraintAffineApproximation` wrapper, and it does
not add a second theorem surface whose statement only repackages the owner through implementation
bookkeeping. -/

recall LagrangianProblem.constrainedAuxiliaryComponents
recall LagrangianProblem.constrainedAuxiliaryComponents_zero
recall LagrangianProblem.constrainedAuxiliaryComponents_succ
recall maxTypeAffineApproximation
recall maxTypeAffineApproximation_apply

section

variable (problem : LagrangianProblem E m) (t : ℝ) (xBar : E)

#check (maxTypeAffineApproximation (problem.constrainedAuxiliaryComponents t) xBar : E → ℝ)

#check
  (show problem.constrainedAuxiliaryComponents t 0 = fun y ↦ problem y - t from
    problem.constrainedAuxiliaryComponents_zero t)

#check
  (show
      ∀ i : Fin m,
        problem.constrainedAuxiliaryComponents t i.succ = problem.constraints i from
    problem.constrainedAuxiliaryComponents_succ t)

end
