/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_85

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {Q : Type u}

-- Proof sketch: evaluate at an arbitrary `x : Q`; from `hf x` we get `0 < f₁ x`, and since
-- `f₁ x ≤ max (f₁ x) (f₂ x)`, transitivity gives positivity of the function-space maximum.
/-- Lemma 7.19: if `f₁` is strictly positive on `Q`, then the pointwise maximum of `f₁` and `f₂`
is strictly positive on `Q`. In particular, this applies when both functions are strictly
positive. -/
theorem StrictlyPositive.max {f₁ : Q → ℝ}
    (hf : StrictlyPositive f₁) (f₂ : Q → ℝ) :
    StrictlyPositive (max f₁ f₂) := by
  intro x
  exact (hf x).trans_le (le_max_left (f₁ x) (f₂ x))
