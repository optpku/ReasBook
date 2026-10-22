/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_6_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_7_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped PowerCone

/- Theorem 5.4.6.3 is a bridge/view statement in the chapter's power-cone domain.

Sampled declarations:
* `ConvexCone.positive` and `ConvexCone.mem_positive` for the scalar cone `ℝ₊`;
* `coneCompositionFeasibleSet` and `mem_coneCompositionFeasibleSet_iff` as the generic cone-
  composition owner;
* `powerConeGeometricMean`, `powerConeQ1`, `powerConeQ2`, and `powerCone` as the chapter's
  existing source-facing `K_α` owner data.

Owner choice:
* source-facing: `powerCone α`;
* core/canonical: `coneCompositionFeasibleSet`;
* bridge/view: the equality below.

This file therefore reuses the chapter owner `powerCone α` directly and does not introduce a
parallel local power-cone definition. After `Definition_5_4_7_1` is expressed through the owner
`coneCompositionFeasibleSet`, the bridge below is definitional rather than a second proof-level
reconstruction. -/

/-- Theorem 5.4.6.3: specializing `coneCompositionFeasibleSet` to the power-cone data
`Q₁ = powerConeQ1`, `K = ℝ₊`, `ξ = powerConeGeometricMean α`, and `Q₂ = powerConeQ2` recovers
the chapter's source-facing power cone `K_α = powerCone α`. The textbook assumptions
`0 < α < 1` are redundant for this set identity. -/
theorem coneCompositionFeasibleSet_eq_powerCone (α : ℝ) :
    coneCompositionFeasibleSet
      powerConeQ1
      (ConvexCone.positive ℝ ℝ)
      (powerConeGeometricMean α)
      powerConeQ2 =
    K_[α] := by
  simp [powerCone]
