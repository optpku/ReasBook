/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_9

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 3.11 is recall-only in the chapter convex-analysis API. Its source-facing mathematical
content is already owned by
`directional_derivative_isGreatest_subgradient_pairings_at_interior_point` in
`Definition_3_9`, stated at the chapter owner abstraction `subdifferential`; this file therefore
reuses that exact theorem instead of keeping a second `StrongDual`-flavored wrapper API. -/
recall directional_derivative_isGreatest_subgradient_pairings_at_interior_point
