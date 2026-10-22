/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 1.7 (1) (core/canonical): the textbook open ball `B(c, r)` is the owner declaration
`Metric.ball c r`. Mathlib defines it in any pseudometric space for all real radii, while the
textbook uses the normed additive commutative group special case and states the definition for
`r > 0`. -/
recall Metric.ball

/- Definition 1.7 (2) (core/canonical): the textbook closed ball `B[c, r]` is the owner
declaration `Metric.closedBall c r`. Mathlib again works in any pseudometric space for all real
radii, while the textbook uses the normed additive commutative group special case and assumes
`r > 0`. -/
recall Metric.closedBall

/- The source-facing set-builder description of the open ball is the canonical derived theorem
`mem_ball_iff_norm`. -/
recall mem_ball_iff_norm

/- The source-facing set-builder description of the closed ball is the canonical derived theorem
`mem_closedBall_iff_norm`. -/
recall mem_closedBall_iff_norm
