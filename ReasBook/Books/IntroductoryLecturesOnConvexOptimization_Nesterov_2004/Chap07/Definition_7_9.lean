/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

/-- Definition 7.9: the a priori radius estimate attached to a function `f`, a base point `x0`,
and a scalar `γ₀` is the quantity `γ₀⁻¹ f(x₀)`. -/
def aPrioriRadiusEstimate {X : Type u} (f : X → ℝ) (γ₀ : ℝ) (x0 : X) : ℝ :=
  f x0 / γ₀

/-- The a priori radius estimate can equivalently be written as the quotient `f x0 / γ₀`. -/
@[simp]
theorem aPrioriRadiusEstimate_eq_div {X : Type u} (f : X → ℝ) (γ₀ : ℝ) (x0 : X) :
    aPrioriRadiusEstimate f γ₀ x0 = f x0 / γ₀ := rfl

end
