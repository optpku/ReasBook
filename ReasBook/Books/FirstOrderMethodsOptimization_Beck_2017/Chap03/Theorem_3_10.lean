/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_9

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 3.10 is recall-only in the chapter directional-derivative API. Its mathematical content
is the `bridge/view` finite-index specialization of the owner theorem
`directional_derivative_iSup_eq_iSup_active_indices` from `Theorem_3_9`; the choice of `Fin m`
adds no new primitive data beyond the existing `[Finite ι] [Nonempty ι]` owner hypotheses. This
file therefore reuses that exact theorem instead of keeping a duplicate local `Fin m` wrapper. -/
recall directional_derivative_iSup_eq_iSup_active_indices
