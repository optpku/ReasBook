/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Module LinearMap

universe u

/- Text 4.2.4 lies in the finite-dimensional bilinear-form duality domain for symmetric
positive-definite bilinear forms.

Sampled owner-style declarations:
- `LinearMap.BilinForm.dualNorm` in `Definition_4_3_4`
- `LinearMap.BilinForm.dualNorm_eq_sSup_primalUnitBall` in `Definition_4_3_4`
- `LinearMap.BilinForm.dualNorm_apply` in `Definition_4_3_4`
- `LinearMap.BilinForm.dualNorm_apply_strongDual` in `Definition_4_2_6`

Best owner abstraction:
- core/canonical: the bilinear-form dual norm owner `LinearMap.BilinForm.dualNorm`
- bridge/view: its support-function and `B.toDual` inverse-pairing expansions

Primitive data:
- `B : BilinForm ℝ E`

Derived API:
- the support-function formula on the primal `B`-unit ball
- the coordinate-free `B.toDual` inverse-pairing formula
- the source-facing equality below, obtained by composing those two owner theorems

Source/core/bridge triage:
- source-facing: the textbook equality between the support-function and inverse-pairing formulas
- core/canonical: `LinearMap.BilinForm.dualNorm`
- bridge/view: the two owner expansions recalled from `Definition_4_3_4`
-/

namespace LinearMap.BilinForm

open scoped BInducedNorm

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]

/-- Text 4.2.4: the support-function formula for the `B`-dual norm agrees with the coordinate-free
expression `⟨s, B⁻¹ s⟩^(1/2)`, where `B⁻¹ s` is the preimage of `s` under the finite-dimensional
equivalence `B.toDual` induced by the symmetric positive-definite bilinear form `B`. -/
theorem dualNorm_eq_sqrt_dualPairing_preimage
    (B : LinearMap.BilinForm ℝ E) (hSymm : B.IsSymm) (hPos : B.toQuadraticMap.PosDef)
    (s : Dual ℝ E) :
    sSup ((fun x : E ↦ s x) '' {x | B.primalSeminorm hPos x ≤ 1}) =
      Real.sqrt (s (B.dualPreimage hPos s)) := by
  simpa using
    (B.dualNorm_eq_sSup_primalUnitBall
        hPos
        s).symm.trans
      (B.dualNorm_apply
        hSymm
        hPos
        s)

end LinearMap.BilinForm
