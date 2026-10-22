/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-
Definition 1.4.4 lies in the finite-dimensional Euclidean inner-product-space domain.

Relevant owner-style declarations sampled before refining:
* `inner ℝ`, the canonical inner product on `E`
* `(fun x : E ↦ ‖x‖)`, the inherited norm on `E`
* mathlib `EuclideanSpace.inner_eq_star_dotProduct`, the canonical coordinate bridge for the
  Euclidean inner product
* mathlib `EuclideanSpace.norm_eq`, the canonical sum-of-squares norm formula

Best owner abstraction:
* the canonical `InnerProductSpace` and `Norm` structure on `EuclideanSpace ℝ (Fin n)`

Primitive data:
* vectors `x y : E`

Derived API:
* `EuclideanSpace.inner_eq_star_dotProduct`, the coordinate formula for the Euclidean inner product
* `EuclideanSpace.norm_eq`, the coordinate formula for the Euclidean norm
* the real-specialized textbook rewrites below, where absolute values disappear and the dot
  product may be read in the usual order

Source/core/bridge triage:
* source-facing: the Euclidean inner product and norm on `ℝⁿ`
* core/canonical: `inner ℝ` and `‖·‖` on `EuclideanSpace ℝ (Fin n)`
* bridge/view: `EuclideanSpace.inner_eq_star_dotProduct` and `EuclideanSpace.norm_eq`

The canonical owner operations come from the `InnerProductSpace` and `Norm` structures on `E`,
and the coordinate bridges are the upstream mathlib `EuclideanSpace` theorems. This file
therefore reuses those owners directly instead of keeping parallel local copies.
-/

#check (inner ℝ : E → E → ℝ)
#check (‖·‖ : E → ℝ)

#check
  (EuclideanSpace.inner_eq_star_dotProduct :
    ∀ x y : E, inner ℝ x y = y ⬝ᵥ x)

#check
  (show ∀ x y : E, inner ℝ x y = x ⬝ᵥ y from
    fun x y ↦ by
      simpa [dotProduct_comm] using (EuclideanSpace.inner_eq_star_dotProduct x y))

#check
  (EuclideanSpace.norm_eq :
    ∀ x : E, ‖x‖ = Real.sqrt (∑ i, ‖x i‖ ^ 2))

#check
  (show ∀ x : E, ‖x‖ = Real.sqrt (∑ i, (x i) ^ 2) from
    fun x ↦ by
      simpa using (EuclideanSpace.norm_eq x))
