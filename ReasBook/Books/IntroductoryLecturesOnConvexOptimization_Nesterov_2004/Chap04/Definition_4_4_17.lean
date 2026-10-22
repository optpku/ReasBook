/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_16

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {φ : E → ℝ} {x : E}

/- Definition 4.4.17 lies in the unconstrained smooth minimization / stationarity-reformulation
domain on real Hilbert spaces.

Sampled owner-style declarations:
* `gradient`, recalled in `Chap01/Definition_1_4_7`, the canonical stationarity map `x ↦ ∇ φ x`;
* `fderiv`, recalled in `Chap04/Definition_4_4_7`, the canonical Jacobian owner for a map;
* `hessian` from `Chap01/Definition_1_4_16`, the Jacobian of the gradient map;
* `HasGradientAt.fderiv_apply`, the scalar derivative/gradient bridge used elsewhere in the
  chapter.

Best owner abstraction:
* core/canonical: the gradient map `∇ φ`, with Jacobian `hessian φ x`.

Primitive data:
* a smooth objective `φ`.

Derived API:
* the stationarity equation `∇ φ x = 0`;
* the Jacobian/Hessian operator `hessian φ x = fderiv ℝ (∇ φ) x`.

Source/core/bridge triage:
* source-facing: rewriting unconstrained minimization as the nonlinear equation `∇ φ x = 0`;
* core/canonical: `gradient` and `hessian`;
* bridge/view: the Jacobian description `fderiv ℝ (∇ φ) x`.

This item therefore introduces no parallel Chapter 4 definition of the stationarity map: the
textbook `F` is exactly the existing gradient owner, and its derivative is exactly the existing
Hessian owner. -/

/- Definition 4.4.17: the stationarity map for unconstrained minimization is the canonical
gradient map. -/
#check (∇ φ)

/- Its Jacobian at `x` is the canonical Hessian operator, equivalently `fderiv ℝ (∇ φ) x`. -/
#check (hessian φ x)
#check (fderiv ℝ (∇ φ) x)

end
