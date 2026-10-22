/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_9

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 3.7 is recall-only as a `bridge/view` item in the chapter convex-subdifferential API:
the exact owner theorem is already
`subdifferential_unbounded_of_affineSpan_effective_domain_direction_finrank_lt`, stated on the
continuous-dual owner bridge `strongDualSubdifferential` rather than an expanded set-builder
presentation. The necessary domain hypothesis is part of that proposition statement; the textbook
omission is explained in the source file comments rather than encoded in the public name. -/
recall
  subdifferential_unbounded_of_affineSpan_effective_domain_direction_finrank_lt
