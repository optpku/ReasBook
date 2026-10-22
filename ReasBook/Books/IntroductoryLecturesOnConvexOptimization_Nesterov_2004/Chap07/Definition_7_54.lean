/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_20
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 7.54 lies in the Chapter 5 Hessian local-norm domain.

Source/core/bridge triage:
* source-facing: the local norm and dual local norm attached to the barrier Hessian at a point
* core/canonical: `hessianLocalNorm` and `dualLocalNorm`
* bridge/view: `hessianLocalNorm_def`, `dualLocalNorm_def`, and `inverseHessianOperator`

Mandatory domain-style sampling before refinement:
* `hessianLocalNorm` in `Chap05/Definition_5_1_1`, the chapter owner for the primal local norm
* `hessianLocalNorm_def` in `Chap05/Definition_5_1_1`, the canonical square-root expansion of that
  owner
* `dualLocalNorm` in `Chap05/Definition_5_0_20`, the chapter owner for the dual local norm
* `dualLocalNorm_def` in `Chap05/Definition_5_0_20`, the canonical inverse-Hessian pairing formula

Best owner abstraction:
* the Chapter 5 owners `hessianLocalNorm` and `dualLocalNorm`

Primitive data:
* a function `F`
* a base point `x`
* a primal direction `h` or dual vector `g`
* for the dual norm, the Hessian positivity and nondegeneracy witnesses

Derived API:
* the source-facing local-norm notation `‖h‖[F; x]`
* the source-facing dual local-norm notation `‖g‖*[F; x | hPos; hInv]`
* the determinant bridge `HessianDualLocalNorm.ofDetNeZero F x hPos hH g`
* the square-root Hessian expansion theorem
* the inverse-Hessian pairing expansion theorem

The previous file duplicated the Chapter 5 bridge API under the new theorem names
`local_norm_eq_sqrt_hessian_quadratic_form` and
`dual_local_norm_eq_sqrt_inverse_hessian_pairing`. Those wrappers added no mathematical content,
had no downstream uses, and kept a parallel local vocabulary around existing owners. This
refinement deletes the duplicate wheel statements and recalls the canonical declarations directly.
-/

/- Definition 7.54 recalls the canonical Hessian local norm owner. -/
recall hessianLocalNorm

/- Its source-facing square-root expansion is the Chapter 5 bridge theorem. -/
recall hessianLocalNorm_def

/- Definition 7.54 also recalls the canonical Hessian dual local norm owner. -/
recall dualLocalNorm

/- Its source-facing inverse-Hessian pairing formula is the Chapter 5 bridge theorem. -/
recall dualLocalNorm_def
