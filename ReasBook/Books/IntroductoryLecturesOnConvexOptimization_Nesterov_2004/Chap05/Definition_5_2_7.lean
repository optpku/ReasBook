/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_3_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open Module LinearMap
open scoped LinearMap.BilinForm.BInducedNorm

/- Definition 5.2.7 lies in the dual-valued-operator / bilinear-form / induced-seminorm domain.

Sampled owner-style declarations:
- `LinearMap.BilinForm.primalSeminorm` in `Chap04/Definition_4_3_4`, the chapter owner for the
  seminorm induced by positive-definite quadratic data;
- `LinearMap.BilinForm.primalSeminorm_apply` in `Chap04/Definition_4_3_4`, the canonical
  pointwise expansion of that owner;
- `LinearMap.BilinForm.IsSymm` in `Chap04/Definition_4_2_5`, the chapter owner for the symmetry
  predicate on the same dual-valued operator data;
- mathlib `Module.Dual`, the canonical codomain `E⋆ = Dual ℝ E`.

Best owner abstraction:
- source-facing: the metric attached to a dual-valued operator `B : E →ₗ[ℝ] Dual ℝ E`,
  written on the owner surface as `B : LinearMap.BilinForm ℝ E`;
- core/canonical: the Chapter 4 bilinear-form owner `LinearMap.BilinForm.primalSeminorm`;
- bridge/view: the pointwise formula `‖x‖[B | hPos] = Real.sqrt (B x x)`.

Primitive data:
- `B : LinearMap.BilinForm ℝ E` (equivalently `B : E →ₗ[ℝ] Dual ℝ E`);
- `hPos : B.toQuadraticMap.PosDef`.

Derived API:
- the recalled seminorm owner `B.primalSeminorm hPos`;
- the source-facing norm notation `‖x‖[B | hPos]`;
- the evaluation theorem `primalSeminorm_apply B hPos`.

Source/core/bridge triage:
- source-facing: Definition 5.2.7's metric attached to `B : E → E⋆`;
- core/canonical: `LinearMap.BilinForm.primalSeminorm`;
- bridge/view: `LinearMap.BilinForm.primalSeminorm_apply`.

Because `E →ₗ[ℝ] Dual ℝ E` is already the canonical bilinear-form owner layer, this item stays on
that primitive algebraic dual surface. The continuous-dual specialization belongs only to later
analytic bridge lemmas, not to the main public declaration here. -/

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-
Definition 5.2.7: the metric attached to a dual-valued operator `B : E → E⋆`, written on the
owner surface as a bilinear form `B : LinearMap.BilinForm ℝ E`, is recalled through the Chapter 4
owner `LinearMap.BilinForm.primalSeminorm`.
-/
recall LinearMap.BilinForm.primalSeminorm
    (B : LinearMap.BilinForm ℝ E) (hPos : B.toQuadraticMap.PosDef) :
    Seminorm ℝ E

/-
Evaluating the recalled metric gives the textbook formula `√(B x x)`.
-/
recall LinearMap.BilinForm.primalSeminorm_apply
    (B : LinearMap.BilinForm ℝ E) (hPos : B.toQuadraticMap.PosDef) :
    ∀ x : E, ‖x‖[B | hPos] = Real.sqrt (B x x)

end
