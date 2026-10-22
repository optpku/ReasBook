/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped RealInnerProductSpace

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Definition 1.14 is recall-only: mathlib's public `EuclideanSpace ℝ ι` is the concrete
coordinate model used later for `ℝ^n`, not the owner abstraction for an abstract Euclidean space.
For an abstract Euclidean space, the primitive owner abstractions are the real inner product
structure and the finite-dimensionality predicate below. -/

/- Definition 1.14 (1): a Euclidean space carries the canonical real inner product structure
`InnerProductSpace ℝ E`. -/
#check InnerProductSpace ℝ E

/- Definition 1.14 (2): a Euclidean space is finite-dimensional, encoded by the canonical
typeclass `FiniteDimensional ℝ E`. -/
#check FiniteDimensional ℝ E

/- Definition 1.14 (3): the Euclidean norm is derived from the ambient real inner product space,
canonically identified with `√⟪x, x⟫_ℝ` by `norm_eq_sqrt_real_inner`. -/
#check norm_eq_sqrt_real_inner

end
