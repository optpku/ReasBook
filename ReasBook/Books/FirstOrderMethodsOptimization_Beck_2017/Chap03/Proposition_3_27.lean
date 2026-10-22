/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_23

-- Declarations for this item will be appended below by the statement pipeline.

/- Proposition 3.27 is recall-only in the Chapter 3 subdifferential-calculus API. The primary
mathematical domain is the weak max rule for subdifferentials of pointwise suprema. In this
domain, the owner abstraction is the Chapter 3 owner set `subdifferential`; the active-index family
`{i : ι // f i x = ⨆ j, f j x}` is derived data, and the convex-hull inclusion is the canonical
source-facing statement. Sampling the nearby owner declarations:

* `directional_derivative_iSup_eq_iSup_active_indices` in `Theorem_3_9` identifies the active
  indices for pointwise suprema.
* `subdifferential_pointwise_max_eq_convexHull_iUnion_active_subdifferential` in
  `Theorem_3_22` is the stronger equality under finite-family convexity/interior hypotheses.
* `convexHull_iUnion_active_subdifferential_subset_subdifferential_iSup` in `Theorem_3_23` is the
  weak inclusion with the exact source-facing semantics of Proposition 3.27.

This file therefore reuses the owner theorem from `Theorem_3_23` directly and introduces no
parallel local wrapper. -/
recall convexHull_iUnion_active_subdifferential_subset_subdifferential_iSup
