/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Definition 5.2 is a `bridge/view` item in the chapter smoothness API: the owner predicate
`is_l_smooth_on` is already defined in Definition 5.1, and this file only records the textbook
`C^{1,1}` notation by specializing that owner predicate to the whole space. -/

/-- The notation `C^{1,1}` is represented by the existence of some global smoothness parameter
`L ≥ 0`. -/
def is_c11 (f : E → ℝ) : Prop :=
  ∃ L : NNReal, is_l_smooth_on f Set.univ L

end
