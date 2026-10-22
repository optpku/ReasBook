/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_4

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 8.19 is `source-facing`: it reintroduces the Lagrangian dual objective
`q(λ) = min_{x ∈ X} L(x; λ)` for the inequality-constrained primal problem from this chapter. The
`core/canonical` owners for this data are already Chapter 3's declarations `lagrangian` and
`lagrangian_dual_objective`, so this item should reuse that existing owner directly rather than
manufacturing a second dual-objective wrapper for the same mathematics. -/

/- Definition 8.19: the Lagrangian dual objective function `q(λ)` of
`min f(x)` subject to `g(x) ≤ 0` and `x ∈ X` is the existing owner
`lagrangian_dual_objective`, which formalizes the textbook formula by sending `λ` to the infimum
over `X` of the Lagrangian `L(x; λ) = f(x) + λᵀ g(x)`. -/
recall lagrangian_dual_objective

/- The displayed formula `q(λ) = min_{x ∈ X} L(x; λ)` is formalized by the canonical infimum
statement `lagrangian_dual_objective_eq_sInf`. -/
recall lagrangian_dual_objective_eq_sInf
