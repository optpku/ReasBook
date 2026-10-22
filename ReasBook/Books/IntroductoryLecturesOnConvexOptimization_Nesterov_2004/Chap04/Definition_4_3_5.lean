/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open LinearMap (BilinForm)
open LinearMap.BilinForm
open scoped BInducedNorm

/- Definition 4.3.5 lies in the bilinear-form / induced-seminorm / Hessian-Lipschitz domain.

Sampled owner-style declarations:
* `LinearMap.BilinForm.PrimalSpace` in `Chap04/Definition_4_2_9`
* `HasLipschitzContinuousHessian` in `Chap04/Definition_4_2_7`
* `HasLipschitzContinuousHessian.sndFDeriv_norm_sub_le` in `Chap04/Definition_4_2_7`
* the norm notation `‖x‖[B]` on `PrimalSpace B` in `Chap04/Definition_4_2_9`

Best owner abstraction:
* source-facing: Definition 4.3.5's Hessian-Lipschitz condition in the `B`-induced geometry
* core/canonical: `HasLipschitzContinuousHessian Mf f` on `LinearMap.BilinForm.PrimalSpace B`
* bridge/view: the `B`-norm notation on `PrimalSpace B`, where the ambient norm is already
  `‖·‖[B]`

Primitive data:
* `B : BilinForm ℝ E`
* the positive-definite quadratic data of `B`
* `Mf : NNReal`
* `f : PrimalSpace B → ℝ`

Derived API:
* the canonical owner `HasLipschitzContinuousHessian Mf f`
* the textbook notation `f ∈ C22[Mf]`
* the inherited `C²` regularity projection

Once Chapter 4 has introduced the intrinsic carrier `PrimalSpace B`, Definition 4.3.5 is no
longer a place to keep a second public owner. The source condition is exactly the existing owner
`HasLipschitzContinuousHessian` on that carrier. -/

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

section

variable {B : BilinForm ℝ E} [Fact B.toQuadraticMap.PosDef]
variable {Mf : NNReal} {f : PrimalSpace B → ℝ}

/- Definition 4.3.5: on the intrinsic carrier `PrimalSpace B`, the textbook condition that the
Hessian of `f` is globally `M_f`-Lipschitz in the `B`-induced norm is exactly the chapter owner
`HasLipschitzContinuousHessian Mf f`, written on theorem surfaces as `f ∈ C22[Mf]`. -/
recall HasLipschitzContinuousHessian

set_option linter.hashCommand false in
#check (f ∈ C22[Mf])

recall HasLipschitzContinuousHessian.contDiff

end
