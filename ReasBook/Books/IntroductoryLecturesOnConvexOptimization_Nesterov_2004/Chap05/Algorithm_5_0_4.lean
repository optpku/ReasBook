/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Algorithm_1_7_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

/- Algorithm 5.0.4 lies in the finite-dimensional full-Newton domain for unconstrained
minimization.

Sampled owner-style declarations:
* `NewtonSystem.AdmissiblePoint`, the canonical Hessian-nondegeneracy owner for `∇ f`;
* `NewtonSystem.step`, the full Newton update owner for the stationarity equation `∇ f = 0`;
* `NewtonSystem.step_def`, the intrinsic inverse-Hessian correction formula;
* `NewtonSystem.Method`, the recursive full-Newton orbit owner.

Best owner abstraction:
* source-facing: the optimization specialization `NewtonSystem.Method (∇ f) x0`;
* core/canonical: `NewtonSystem.AdmissiblePoint (∇ f)` and `NewtonSystem.step (∇ f)`;
* bridge/view: `NewtonSystem.step_def`, `NewtonSystem.Method.zero_eq`,
  `NewtonSystem.Method.succ_eq`, and
  `NewtonSystem.Method.jacobian_nondegenerate`.

Primitive data:
* an objective `f : E → ℝ`;
* an initial point `x0 : E`.

Derived API:
* the admissible Newton domain `NewtonSystem.AdmissiblePoint (∇ f)`;
* the inverse-Hessian Newton update `NewtonSystem.step (∇ f)`;
* the recursive method owner `NewtonSystem.Method (∇ f) x0`;
* its initial-value, recursion, and Hessian-nondegeneracy projections.

This file is a recall layer: it reuses the Chapter 1 owner declarations directly on the
optimization surface and keeps no parallel local aliases for the full-step specialization. -/

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable (f : E → ℝ) (x0 : E)

/- Algorithm 5.0.4 recalls the canonical Newton method for unconstrained minimization as Newton's
method for the stationarity equation `∇ f = 0`. -/
#check (NewtonSystem.Method (∇ f) x0)

/- The underlying admissible domain consists of points where the Hessian of `f` is
nonsingular. -/
#check (NewtonSystem.AdmissiblePoint (∇ f))

/- The Newton update is the full inverse-Hessian correction for the stationarity equation
`∇ f = 0`. -/
recall NewtonSystem.step

/- Expanding the recalled owner gives the intrinsic inverse-Hessian formula for one Newton
step. -/
recall NewtonSystem.step_def

/- Every Newton method for `∇ f = 0` starts from its prescribed initial point. -/
recall NewtonSystem.Method.zero_eq

/- Each iterate of the method is the Newton update of the previous one. -/
recall NewtonSystem.Method.succ_eq

/- The Hessian remains nondegenerate along the Newton trajectory. -/
recall NewtonSystem.Method.jacobian_nondegenerate

end

end
