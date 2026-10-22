/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_6
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_2

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 14.5 is a `bridge/view` recall: the Chapter 14 block composite objective
`x ↦ f x + ∑ i, g_i (x_i)` is already owned by the Chapter 10 composite objective applied to the
Chapter 6 block-separable sum.

Domain sampling identifies the relevant owner declarations:
- `composite_model_objective`;
- `composite_model_objective_apply`;
- `separableSum`;
- `separableSum_apply`.

Primitive data are only the smooth term `f` and the block penalties `g_i`. Since the source
introduces no additional owner beyond this specialization, the file should reuse those canonical
declarations directly instead of keeping a parallel Chapter 14 specialization theorem. -/

/- Definition 14.5: the Chapter 14 composite model is the canonical objective
`composite_model_objective f (separableSum g)`. -/
recall composite_model_objective
recall composite_model_objective_apply
recall separableSum
recall separableSum_apply
