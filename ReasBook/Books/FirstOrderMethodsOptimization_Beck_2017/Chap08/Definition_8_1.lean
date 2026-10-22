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

/- Definition 8.1: in this chapter, an abstract Euclidean space is modeled by the canonical real
inner-product-space owner `InnerProductSpace ℝ E`; the finite-dimensionality hypothesis and the
derived Euclidean norm formula are recalled below as companion views. -/
#check InnerProductSpace ℝ E

/- Finite-dimensionality is the remaining Euclidean-space hypothesis, encoded by the canonical
typeclass `FiniteDimensional ℝ E`. -/
#check FiniteDimensional ℝ E

/- The Euclidean norm is canonically derived from the ambient real inner product, identified with
`√⟪x, x⟫_ℝ` by `norm_eq_sqrt_real_inner`. -/
#check norm_eq_sqrt_real_inner

end
