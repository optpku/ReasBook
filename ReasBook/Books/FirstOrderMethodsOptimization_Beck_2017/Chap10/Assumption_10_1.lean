/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_3

-- Declarations for this item will be appended below by the statement pipeline.

/- Assumption 10.1 is recall-only in Chapter 10. Its `source-facing` content is the standing
assumption package for the composite model `min_x {f(x) + g(x)}`, and the exact `core/canonical`
owner already exists as `IsCompositeSmoothMinimizationProblem`; there is no new mathematics here
that would justify a second wrapper, alias, or unpacking theorem. -/

/- Assumption 10.1: the standing hypotheses (A)-(C) for the composite model
`min_x {F(x) = f(x) + g(x)}` are the existing owner class
`IsCompositeSmoothMinimizationProblem`, which packages that `g : E → (-∞, ∞]` is proper, closed,
and convex; that `f : E → (-∞, ∞]` never takes the value `-∞`, is closed, has convex effective
domain, satisfies `effective_domain g ⊆ interior (effective_domain f)`, and has
`(fun x ↦ (f x).toReal)` `L_f`-smooth on `interior (effective_domain f)`; consequently `f` is
proper; and that the optimal set `X^*` is nonempty with optimal value `F_opt`. -/
recall IsCompositeSmoothMinimizationProblem
