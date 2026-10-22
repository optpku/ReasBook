/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Definition 1.6 (source-facing): a real normed vector space on `E` is formalized by the owner
pair `[NormedAddCommGroup E] [NormedSpace ℝ E]`. The first class carries the additive, metric,
and norm structure, while the second is the canonical scalar-compatibility typeclass. -/
#check NormedAddCommGroup E
#check NormedSpace ℝ E

/- The underlying real vector-space structure is then derived canonically from `NormedSpace ℝ E`,
so it does not need to be introduced as separate primitive data in this item. -/
#check Module ℝ E

end
