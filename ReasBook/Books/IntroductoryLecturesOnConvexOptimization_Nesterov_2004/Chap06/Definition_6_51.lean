/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.FenchelPrimalExtension

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

local instance {p : Prop} : Decidable p := Classical.propDecidable p

/- This item belongs to the chapter's `WithTop ℝ`-valued convex-analysis layer.

The source-facing object is the indicator function of a set `Q`, taking the value `0` on `Q` and
`+∞` outside `Q`. In the existing chapter API this is exactly the zero-function specialization of
`fenchelPrimalExtension`. The textbook assumes `Q` is closed and convex, but the defining formula
itself depends only on `Q`, so the public statement stays at that weaker canonical level.
-/

section

variable {E : Type u} (Q : Set E)

/- For a closed convex set `Q ⊆ E`, the indicator function of `Q` is the `WithTop ℝ`-valued
function that equals `0` on `Q` and `+∞` outside `Q`. In the chapter API this is the
specialization `fenchelPrimalExtension Q (fun _ ↦ 0)`. -/
set_option linter.hashCommand false in
#check (fenchelPrimalExtension Q (fun _ : E ↦ (0 : ℝ)) : E → WithTop ℝ)

end

section

variable {E : Type u}

-- Proof sketch: unfold `fenchelPrimalExtension`; membership in `Q` is exactly the branch
-- condition, so the zero-function specialization yields the displayed `0`/`+∞` case split.
/-- Definition 6.51: the zero-function specialization of `fenchelPrimalExtension` is the textbook
indicator function formula. -/
theorem fenchelPrimalExtension_zero_apply (Q : Set E) (x : E) :
    fenchelPrimalExtension Q (fun _ : E ↦ (0 : ℝ)) x =
      if x ∈ Q then (0 : WithTop ℝ) else ⊤ := by
  classical
  -- The defining branch condition for the indicator function is exactly membership in `Q`.
  by_cases hx : x ∈ Q
  · -- On `Q`, the primal extension agrees with the underlying zero function.
    simp [hx]
  · -- Outside `Q`, the primal extension takes the value `⊤`.
    simp [hx]

end
