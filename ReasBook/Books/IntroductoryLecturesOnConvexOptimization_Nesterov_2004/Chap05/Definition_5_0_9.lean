/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Gradient
open scoped HessianLocalNorm

/- Definition 5.0.9 lies in the local Hessian norm domain.

Source/core/bridge triage:
* source-facing: the local norm induced by the Hessian quadratic form at a point
* core/canonical: `hessianLocalNorm`
* bridge/view: the owner-level source-facing notation `‖u‖[f; x]`

Sampled owner declarations:
* `hessian` in `Chap01/Definition_1_4_16`, the intrinsic Hessian operator owner
* `hessianLocalNorm` in `Chap05/Definition_5_1_1`, the chapter owner for the Hessian-induced
  local norm
* `hessianLocalNorm_def` in `Chap05/Definition_5_1_1`, the canonical expansion of that owner
* `LinearMap.BilinForm.primalSeminorm` together with the source-facing norm notation
  `‖x‖[B]` from `Chap04/Definition_4_2_6`, the chapter owner pattern for induced quadratic norms

Best owner abstraction:
* `hessianLocalNorm`

Primitive data:
* a function `f`
* a base point `x`
* a direction `u`

Derived API:
* the owner-level source-facing notation `‖u‖[f; x]`
* the Hessian quadratic form `inner ℝ u (hessian f x u)`
* the owner expansion theorem `hessianLocalNorm_def`

This item is therefore refined to direct reuse of the chapter owner `hessianLocalNorm` together
with its owner-level source-facing notation, rather than a second local norm owner, a local
notation copy, or a separate squared-norm wrapper theorem. -/

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 5.0.9 recalls the canonical Hessian local norm owner. -/
recall hessianLocalNorm
