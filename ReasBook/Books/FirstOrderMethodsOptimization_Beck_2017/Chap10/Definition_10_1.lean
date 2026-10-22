/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_14

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Definition 10.1 is recall-only. The ambient Euclidean-space owner was already fixed in
Definition 1.14, so the Chapter 10 entry should reuse that same canonical surface rather than
repeat a parallel local wrapper.

Domain sampling in the ambient geometry API gives:
- `source-facing`: the Chapter 10 Euclidean-space recall;
- `core/canonical`: `InnerProductSpace ℝ E`, `FiniteDimensional ℝ E`, and
  `norm_eq_sqrt_real_inner`;
- `bridge/view`: none.

Primitive data are only the real inner-product structure and finite-dimensionality; the norm is
derived API from that owner. -/

/- Definition 10.1: a Euclidean space carries the canonical real inner product structure
`InnerProductSpace ℝ E`. -/
#check InnerProductSpace ℝ E

/- Definition 10.1: finite-dimensionality is the standard predicate `FiniteDimensional ℝ E`. -/
#check FiniteDimensional ℝ E

/- Definition 10.1: the Euclidean norm is the norm induced by the ambient inner product, with
canonical evaluation rule `norm_eq_sqrt_real_inner`. -/
recall norm_eq_sqrt_real_inner

end
