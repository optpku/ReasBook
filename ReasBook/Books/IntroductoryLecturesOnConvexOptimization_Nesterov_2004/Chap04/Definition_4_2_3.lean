/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

open Module

universe u v w

/- Definition 4.2.3 lies in the algebraic-duality / bilinear-transpose domain.

Sampled owner-style declarations:
- mathlib `LinearMap.flip`
- mathlib `LinearMap.flip_apply`
- mathlib `Module.Dual`
- mathlib `Dual.eval`

Best owner abstraction:
- core/canonical: `LinearMap.flip` for bilinear maps

Primitive data:
- a commutative semiring `R`
- `R`-modules `E₁` and `E₂`
- a dual-valued linear map `A : E₁ →ₗ[R] Dual R E₂`

Derived API:
- the pointwise transpose identity `A.flip y x = A x y`

Source/core/bridge triage:
- source-facing: the transpose `A* : E₂ → E₁*` of `A : E₁ → E₂*`
- core/canonical: `LinearMap.flip`
- bridge/view: the specialization from bilinear maps to dual-valued operators

The previous local owner `adjointOperator` was definitionally equal to `LinearMap.flip`, so this
file now recalls the canonical owner directly and keeps only the specialized pointwise companion
theorem used in the chapter.
-/

variable {R : Type u} {E₁ : Type v} {E₂ : Type w}
variable [CommSemiring R]
variable [AddCommMonoid E₁] [Module R E₁]
variable [AddCommMonoid E₂] [Module R E₂]

/- Definition 4.2.3: for a linear operator `A : E₁ → E₂*`, the adjoint operator is exactly the
canonical transpose `A.flip : E₂ → E₁*`. -/
#check (LinearMap.flip : (E₁ →ₗ[R] Dual R E₂) → E₂ →ₗ[R] Dual R E₁)

/- Evaluating the canonical transpose at `y` and then at `x` recovers the defining pairing
identity `(A x) y`. -/
#check
  (LinearMap.flip_apply :
    ∀ (A : E₁ →ₗ[R] Dual R E₂) (x : E₁) (y : E₂), A.flip y x = A x y)
