/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import Mathlib.LinearAlgebra.Dual.Defs

-- Declarations for this item will be appended below by the statement pipeline.

open Module

universe u v w

/- Definition 4.4.3 lies in the algebraic-duality domain for linear maps and their dual
transposes.

Sampled owner-style declarations:
- mathlib `Module.Dual`
- mathlib `Module.Dual.transpose`
- mathlib `LinearMap.dualMap`
- mathlib `LinearMap.dualMap_apply`

Best owner abstraction:
- core/canonical: `LinearMap.dualMap`

Primitive data:
- a commutative semiring `R`
- `R`-modules `E₁` and `E₂`
- a linear map `A : E₁ →ₗ[R] E₂`

Derived API:
- the induced dual map `A.dualMap : Dual R E₂ →ₗ[R] Dual R E₁`
- its pointwise evaluation formula `LinearMap.dualMap_apply`

Source/core/bridge triage:
- source-facing: the textbook adjoint-on-dual-spaces construction `A* : E₂* → E₁*`
- core/canonical: `LinearMap.dualMap`
- bridge/view: the textbook reading of `A.dualMap` as the adjoint on dual spaces

The previous local alias `adjointOnDualSpaces` and its companion theorem were exact-interface
duplicates of mathlib owners. This file therefore recalls the canonical declarations directly
instead of keeping a parallel chapter-local wrapper. -/

variable {R : Type u} {E₁ : Type v} {E₂ : Type w}
variable [CommSemiring R] [AddCommMonoid E₁] [Module R E₁]
variable [AddCommMonoid E₂] [Module R E₂]

/- Definition 4.4.3: for a linear operator `A : E₁ → E₂`, the adjoint operator on dual spaces is
exactly the canonical dual map `A.dualMap : E₂⋆ → E₁⋆`. -/
recall LinearMap.dualMap
    (A : E₁ →ₗ[R] E₂) :
    Dual R E₂ →ₗ[R] Dual R E₁

/- Evaluating the canonical dual map gives the defining pairing identity. -/
recall LinearMap.dualMap_apply
    (A : E₁ →ₗ[R] E₂) (φ : Dual R E₂) (x : E₁) :
    A.dualMap φ x = φ (A x)
