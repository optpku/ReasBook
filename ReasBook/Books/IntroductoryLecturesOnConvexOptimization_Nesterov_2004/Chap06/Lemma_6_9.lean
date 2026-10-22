/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Lemma_6_2_4

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 6.9 is the same switching-parameter recurrence statement already canonicalized in
`Lemma_6_2_4`. The owner theorem there now works directly with the pair-valued
`switching_parameters` sequence, so this file keeps only the direct recall surface. -/
recall alpha_succ_eq_one_sub_tau_mul_pred_of_alternating_scalar_updates
