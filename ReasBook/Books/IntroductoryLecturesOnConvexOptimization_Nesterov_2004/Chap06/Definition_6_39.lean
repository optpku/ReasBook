/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {X : Type u} {U : Type v}
variable {Q₁ : Set X} {Q₂ : Set U}

/-- Definition 6.39 [Chapter6_1.json:91]: a feasible pair `(xBar, uBar)` satisfies the excessive
gap condition with `μ₁ = 0` when the smoothed primal value `f_{μ₂}(xBar)` is bounded above by the
dual value `φ(uBar)`. -/
abbrev satisfiesExcessiveGapConditionWithMu1Zero
    (fμ₂ : Q₁ → ℝ) (φ : Q₂ → ℝ) (xBar : Q₁) (uBar : Q₂) : Prop :=
  fμ₂ xBar ≤ φ uBar

-- Proof sketch: unfold `satisfiesExcessiveGapConditionWithMu1Zero`.
/-- A feasible pair satisfies the `μ₁ = 0` excessive-gap condition exactly when
`f_{μ₂}(xBar) ≤ φ(uBar)`. -/
theorem satisfiesExcessiveGapConditionWithMu1Zero_iff
    (fμ₂ : Q₁ → ℝ) (φ : Q₂ → ℝ) (xBar : Q₁) (uBar : Q₂) :
    satisfiesExcessiveGapConditionWithMu1Zero fμ₂ φ xBar uBar ↔
      fμ₂ xBar ≤ φ uBar := by
  -- Unfolding the abbreviation turns the statement into a reflexive equivalence.
  rfl

end
