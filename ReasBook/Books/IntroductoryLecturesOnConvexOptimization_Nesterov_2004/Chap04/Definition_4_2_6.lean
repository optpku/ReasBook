/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_3_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

open Module LinearMap

/- Definition 4.2.6 is a source-facing recall item in the induced-norm geometry of
positive-definite self-adjoint bilinear forms on real vector spaces.

Layer targeted by this refinement:
- source-facing recall of the Chapter 4 norm owners already defined on bilinear forms

Sampled owner-style declarations:
- `LinearMap.BilinForm.primalSeminorm` in `Definition_4_3_4`
- `LinearMap.BilinForm.dualNorm` in `Definition_4_3_4`
- `LinearMap.BilinForm.dualNorm_apply` in `Definition_4_3_4`
- `Seminorm.dualNorm` in `Definition_2_5`
- mathlib `StrongDual`

Best owner abstraction:
- the canonical bilinear-form owner `B : BilinForm ℝ E`, with derived norm API
  `LinearMap.BilinForm.primalSeminorm` and, in finite dimension,
  `LinearMap.BilinForm.dualNorm`

Primitive data:
- `B : BilinForm ℝ E`

Derived API:
- the primal seminorm owner `primalSeminorm B`
- in finite dimension, the dual norm `dualNorm B`
- the canonical inverse-pairing bridge `dualPreimage hPos`
- the support-function expansion `dualNorm_eq_sSup_primalUnitBall`
- under symmetry and positive-definiteness, the `B.toDual` inverse-pairing formula
  `dualNorm_apply`
- the continuous-dual bridge used by the nearby analytic statements

Source/core/bridge triage:
- source-facing: Definition 4.2.6's primal and dual norms attached to `B`
- core/canonical: the bilinear-form owner declarations in `Definition_4_3_4`
- bridge/view: the finite-dimensional `toDual` formula and its continuous-dual specialization
-/

/- The Chapter 4 primal seminorm owner is the canonical bilinear-form declaration from
`Definition_4_3_4`. -/
#check LinearMap.BilinForm.primalSeminorm

/- The bilinear-form dual norm owner is the corresponding support-function declaration from
`Definition_4_3_4`; as for the Chapter 2 owner `Seminorm.dualNorm`, the source-facing dual
surface is used in finite-dimensional settings where this support value is real-valued. -/

/- The pointwise primal seminorm expansion is recalled directly from the owner file. -/
#check LinearMap.BilinForm.primalSeminorm_apply

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

/- The finite-dimensional bilinear-form dual norm owner is recalled directly from the owner file. -/
#check LinearMap.BilinForm.dualNorm

/- The finite-dimensional dual-norm support formula and its `B.toDual` bridge are recalled
directly from the owner file. -/
#check LinearMap.BilinForm.dualNorm_eq_sSup_primalUnitBall
#check LinearMap.BilinForm.dualNorm_apply

end

namespace LinearMap.BilinForm

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-
Definition 4.2.6: for a positive-definite self-adjoint operator, the primal norm on `E` is
recalled through the canonical bilinear-form owner `LinearMap.BilinForm.primalSeminorm`, whose
value at `h` is `⟪Bh, h⟫^(1/2)` and whose owner surface depends only on `B.toQuadraticMap`.
-/
recall LinearMap.BilinForm.primalSeminorm (B : LinearMap.BilinForm ℝ E)
    (hPos : B.toQuadraticMap.PosDef) :
    Seminorm ℝ E

end

end LinearMap.BilinForm

namespace BInducedNorm

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

end

end BInducedNorm

open scoped BInducedNorm

namespace LinearMap.BilinForm

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- In finite dimension, the `B`-dual norm on the continuous dual is computed by the same
`B.toDual` inverse-pairing formula after coercing a continuous functional to its underlying linear
map. -/
theorem dualNorm_apply_strongDual
    [FiniteDimensional ℝ E]
    (B : LinearMap.BilinForm ℝ E) (hSymm : B.IsSymm) (hPos : B.toQuadraticMap.PosDef)
    (s : StrongDual ℝ E) :
    B.dualNorm hPos s.toLinearMap = Real.sqrt (s (B.dualPreimage hPos s.toLinearMap)) := by
  simpa using B.dualNorm_apply hSymm hPos s.toLinearMap

/-- In finite dimension, the `B`-dual norm on the continuous dual is still the support function of
the primal `B`-unit ball after passing to the underlying linear functional. -/
theorem dualNorm_eq_sSup_primalUnitBall_strongDual
    [FiniteDimensional ℝ E]
    (B : LinearMap.BilinForm ℝ E) (hPos : B.toQuadraticMap.PosDef)
    (s : StrongDual ℝ E) :
    B.dualNorm hPos s.toLinearMap =
      sSup ((fun x : E ↦ s x) '' {x | B.primalSeminorm hPos x ≤ 1}) := by
  simpa using B.dualNorm_eq_sSup_primalUnitBall hPos s.toLinearMap

end

end LinearMap.BilinForm
