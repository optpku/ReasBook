/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Algorithm_1_7_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_16

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient
open NewtonSystem (AdmissiblePoint)

noncomputable section

universe u

/- Algorithm 4.1.2 lies in the finite-dimensional damped-Newton domain for unconstrained
minimization.

Sampled owner-style declarations in this domain:
* `NewtonSystem.AdmissiblePoint`, the canonical Hessian-nondegeneracy owner for `∇ f`;
* `DampedNewton.step`, the chapter-1 owner of the one-step damped Newton update;
* `DampedNewton.Method`, the source-facing recursive damped Newton algorithm owner;
* `hessianMatrix` and `hessianMatrix_toEuclideanLin`, the Euclidean matrix bridge for the
  intrinsic Hessian operator.

Best owner abstraction:
* source-facing: `DampedNewton.step` and `DampedNewton.Method`;
* core/canonical: the same owner layer on `AdmissiblePoint (∇ f)`;
* bridge/view: the Euclidean inverse-Hessian matrix formula recovered from
  `hessianMatrix_toEuclideanLin`.

Primitive data:
* an objective `f : E → ℝ`;
* an admissible point `x : AdmissiblePoint (∇ f)`;
* a scalar damping parameter `h : ℝ`.

Derived API:
* the intrinsic one-step formula `DampedNewton.step_def`;
* the Euclidean matrix formula in `step_eq_hessianMatrixFormula`;
* the recursive method owner `DampedNewton.Method`;
* its basic iterate API `DampedNewton.Method.zero_eq`, `DampedNewton.Method.succ_eq`, and
  `DampedNewton.Method.hessian_nondegenerate`.

The previous file duplicated the owner one-step map by introducing a new `dampedNewtonStep`
definition on the totalized matrix inverse and an unused positivity subtype for `h`. This
refinement reuses the chapter-1 owner directly and keeps only the Euclidean matrix formula as a
bridge theorem. -/

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Algorithm 4.1.2 recalls the canonical damped Newton update from Chapter 1. -/
recall DampedNewton.step
    (f : E → ℝ) (x : AdmissiblePoint (∇ f)) (h : ℝ) : E

/- Expanding the recalled owner gives the intrinsic inverse-Hessian correction formula. -/
recall DampedNewton.step_def

/- Algorithm 4.1.2 is the recursive damped Newton method owner from Chapter 1. -/
recall DampedNewton.Method

/- Every damped Newton method starts from its prescribed initial point. -/
recall DampedNewton.Method.zero_eq

/- Each iterate is the damped Newton update of the previous one. -/
recall DampedNewton.Method.succ_eq

/- The Hessian remains nondegenerate along a damped Newton trajectory. -/
recall DampedNewton.Method.hessian_nondegenerate

end

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- In Euclidean coordinates, the owner damped Newton update is the textbook line-search
formula `x - h [∇² f(x)]⁻¹ ∇ f(x)`. -/
recall DampedNewton.step_eq_hessianMatrixFormula

end
