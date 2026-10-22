/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix

/-
Proposition 1.4.5 lies in the finite-dimensional inner-product linear algebra domain.

Relevant owner declarations sampled before refining:
* `LinearMap.adjoint`, the owner adjoint construction for linear maps on Euclidean spaces
* `LinearMap.adjoint_inner_right`, the canonical adjointness identity
* `Matrix.toEuclideanLin`, the owner matrix action on Euclidean space
* `Matrix.toEuclideanLin_conjTranspose_eq_adjoint`, the canonical matrix-to-adjoint bridge

Best owner abstraction:
* `LinearMap.adjoint`

Primitive data:
* a real matrix `A`
* vectors `x` and `y`
* the induced linear map `A.toEuclideanLin`

Derived API:
* the adjointness identity from `A.toEuclideanLin.adjoint_inner_right`
* the matrix bridge `A.toEuclideanLin.adjoint = Aᵀ.toEuclideanLin`

Source/core/bridge triage:
* source-facing: the textbook transpose identity `⟨Ax, y⟩ = ⟨x, Aᵀ y⟩`
* core/canonical: `LinearMap.adjoint`
* bridge/view: `Matrix.toEuclideanLin_conjTranspose_eq_adjoint`

This file therefore keeps only the source-facing theorem and reuses the owner adjoint API
directly, rather than rebuilding a parallel matrix-specific adjoint interface.
-/

variable {m n : ℕ}

-- Proof sketch: rewrite `⟪A x, y⟫` using the owner adjointness identity for `A.toEuclideanLin`,
-- then identify the adjoint with `(Aᵀ).toEuclideanLin`.
/-- Proposition 1.4.5: for a real `m × n` matrix, the standard Euclidean inner products on
`ℝ^n` and `ℝ^m` satisfy the adjointness identity `⟨Ax, y⟩ = ⟨x, Aᵀ y⟩`. -/
theorem matrix_transpose_adjointness
    (A : Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin m)) :
    inner ℝ (A.toEuclideanLin x) y =
      inner ℝ x (Aᵀ.toEuclideanLin y) := by
  rw [← A.toEuclideanLin.adjoint_inner_right]
  exact congrArg
    (fun z : EuclideanSpace ℝ (Fin n) ↦ inner ℝ x z)
    (congrArg
      (fun T : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) ↦ T y)
      (Matrix.toEuclideanLin_conjTranspose_eq_adjoint A).symm)
