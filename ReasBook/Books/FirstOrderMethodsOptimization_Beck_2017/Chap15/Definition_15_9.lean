/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_16

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 15.9 is a `bridge/view`: the textbook objective
`x ↦ ∑ i, g_i (A_i x)` is exactly the Chapter 8 finite-sum owner specialized to the family
`fun i x ↦ g_i (A_i x)`.

Domain sampling against the surrounding project identifies the canonical owners already present:
- `finite_sum_objective` for the aggregate objective;
- `finite_sum_objective_apply` for its pointwise evaluation formula; and
- `isMinOn_finite_sum_objective_iff` for the minimization reformulation.

Primitive data are only the family `g` and the linear maps `A i`. The aggregate objective and its
basic minimization API are already owned upstream, so this file should recall those declarations
directly rather than introducing local wrappers or a separate regularity package. -/

/- Definition 15.9: the finite-sum linear-composite objective `x ↦ ∑ i, g_i (A_i x)` is the
Chapter 8 finite-sum owner specialized to the family `fun i x ↦ g_i (A_i x)`. -/
recall finite_sum_objective
recall finite_sum_objective_apply
recall isMinOn_finite_sum_objective_iff
