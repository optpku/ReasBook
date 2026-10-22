/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

open Module

universe u v

variable {E : Type u} {H : Type v}
variable [AddCommMonoid E] [Module ℝ E]
variable [AddCommMonoid H] [Module ℝ H]

/- This item is a recall-only real specialization in the chapter's algebraic-duality /
bilinear-transpose domain.

Sampled owner-style declarations:
- mathlib `LinearMap.flip`
- mathlib `LinearMap.flip_apply`
- Chapter 4 `Definition_4_2_3`, which already refines the same transpose operator over a general
  commutative semiring

Best owner abstraction:
- core/canonical: `LinearMap.flip`

Primitive data:
- real vector spaces `E` and `H`
- a dual-valued linear map `A : E →ₗ[ℝ] Dual ℝ H`

Derived API:
- the transposed operator `A.flip : H →ₗ[ℝ] Dual ℝ E`
- the pairing identity `A.flip y x = A x y`

Source/core/bridge triage:
- source-facing: the adjoint/transposed operator `A* : H → E*`
- core/canonical: `LinearMap.flip`
- bridge/view: the real-vector-space specialization used in Chapter 7

This item adds no new owner beyond the scalar-generic transpose API, so the redundant local wrapper
theorem is deleted in favor of direct recall of the canonical owner API. -/

/- Definition 7.49: for a linear operator `A : E → H*`, the adjoint operator is exactly the
canonical transpose `A.flip : H → E*`. -/
#check (show (E →ₗ[ℝ] Dual ℝ H) → H →ₗ[ℝ] Dual ℝ E from LinearMap.flip)

/- Evaluating the canonical transpose recovers the defining dual pairing identity. -/
#check (show ∀ (A : E →ₗ[ℝ] Dual ℝ H) (x : E) (y : H), A.flip y x = A x y from
  LinearMap.flip_apply)
