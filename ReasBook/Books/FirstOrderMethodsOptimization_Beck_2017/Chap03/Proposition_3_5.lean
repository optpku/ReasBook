/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_1

-- Declarations for this item will be appended below by the statement pipeline.

/- Proposition 3.5 is recall-only in the chapter subdifferential API. The primitive owner data is
`subdifferential : Set (Module.Dual ℝ E)`. Convexity belongs to that owner abstraction itself,
while closedness is a topological bridge statement on `strongDualSubdifferential`; this file
therefore reuses those upstream declarations directly and introduces no parallel local wrapper. -/
recall isClosed_subdifferential
recall convex_subdifferential
