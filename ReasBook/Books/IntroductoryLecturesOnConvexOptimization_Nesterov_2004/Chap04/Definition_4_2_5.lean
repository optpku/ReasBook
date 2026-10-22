/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {R : Type u} {M : Type v} [CommSemiring R] [AddCommMonoid M] [Module R M]

open LinearMap (BilinForm)

/- Definition 4.2.5 lies in the bilinear-form/symmetric-operator domain.

Sampled owner-style declarations:
- `LinearMap.BilinForm.IsSymm`
- `LinearMap.BilinForm.isSymm_def`
- `LinearMap.IsSymmetric`
- `ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric`

Best owner abstraction:
- source-facing: symmetry of the bilinear pairing associated with an operator `E → E⋆`
- core/canonical: `LinearMap.BilinForm.IsSymm`
- bridge/view: `LinearMap.IsSymmetric` and `IsSelfAdjoint` after choosing an inner product

Primitive data:
- a bilinear form `B : BilinForm R M`

Derived API:
- the pointwise symmetry characterization `B x y = B y x`

This item is therefore a direct recall of the canonical bilinear-form owner, not a new local
`selfAdjoint` wrapper. -/
/-
Definition 4.2.5: for a linear operator `B : E → E⋆` on a real vector space, the textbook
self-adjointness condition is the canonical symmetry predicate on the associated bilinear form,
equivalently `(B x) y = (B y) x` for all `x` and `y`.
-/
recall LinearMap.BilinForm.IsSymm (B : BilinForm R M) : Prop

/-
The canonical symmetry predicate on a bilinear form is exactly the pointwise equality
`B x y = B y x`.
-/
recall LinearMap.BilinForm.isSymm_def {B : BilinForm R M} :
    B.IsSymm ↔ ∀ x y : M, B x y = B y x
