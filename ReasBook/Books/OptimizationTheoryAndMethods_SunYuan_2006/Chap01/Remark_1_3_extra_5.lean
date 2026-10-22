/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.MeanInequalities

-- Semantic recall hits verified for this item: `NNReal.Lp_add_le`,
-- `Real.Lp_add_le`, and `Real.Lp_add_le_of_nonneg`.

/-
Chapter01 Remark 1.3-extra-5

Canonical recall: the textbook Minkowski inequality on `ℝ^n` is exactly the
finite-set specialization of `Real.Lp_add_le`, with the coordinate index set
taken to be `Fin n`.
-/
#check Real.Lp_add_le
