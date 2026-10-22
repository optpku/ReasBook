/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap05.Theorem_5_8
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

/- Chapter 10 uses `PosReal` stepsizes, while Theorem 5.8 records cocoercivity with an `NNReal`
smoothness constant. This file is a `bridge/view` owner for that canonical conversion. -/

/-- In a proper real inner-product space, convex global `L`-smoothness with `L : PosReal`
specializes Theorem 5.8's gradient cocoercivity clause without introducing a local wrapper. -/
theorem gradient_cocoercive_of_convex_l_smooth_posReal
    (L : PosReal) {f : E → ℝ} (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_smooth : is_l_smooth_on f Set.univ (PosReal.toNNReal L)) :
    gradient_cocoercive f (PosReal.toNNReal L) := by
  letI : FiniteDimensional ℝ E := FiniteDimensional.of_locallyCompactSpace ℝ
  exact
    gradient_cocoercive_of_convex_l_smooth
      hf_convex hf_smooth (by exact_mod_cast L.2)

end
