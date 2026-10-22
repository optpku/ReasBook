/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap08.Assumption_8_7

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 9.1 is recall-only in Chapter 9. Its `source-facing` content is the standing
assumption package for the constrained convex problem `(P)`, and the exact `core/canonical` owner
already exists as `IsConstrainedConvexProblem`; there is no new mathematics here that would
justify a second wrapper or alias. -/

/- Definition 9.1: the standing assumptions (A)-(D) for
`(P) := min {f(x) : x ∈ C}` are the existing owner class `IsConstrainedConvexProblem`, which
packages that `f : E → (-∞, ∞]` is proper, closed, and convex, that `C` is nonempty, closed,
convex, and contained in `interior (dom(f))`, and that the optimal set `X^*` is nonempty with
optimal value `f_opt`. -/
recall IsConstrainedConvexProblem
