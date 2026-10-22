/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

section

open Set

/-
Theorem 3.20 lives at the one-variable calculus owner layer. Its main statement is already the
canonical mathlib chain rule `HasDerivAt.comp_hasDerivWithinAt`; the textbook right-endpoint
formula for `derivWithin` is only a thin `bridge/view` consequence of that owner theorem together
with `HasDerivWithinAt.derivWithin` and `uniqueDiffWithinAt_Ici`.
-/
recall HasDerivAt.comp_hasDerivWithinAt
recall HasDerivWithinAt.derivWithin
recall uniqueDiffWithinAt_Ici

/-- Right-derivative formula companion to the canonical chain rule at a left endpoint. -/
theorem derivWithin_comp_right_endpoint {f g : ℝ → ℝ} {a f' g' : ℝ}
    (hf : HasDerivWithinAt f f' (Ici a) a) (hg : HasDerivAt g g' (f a)) :
    derivWithin (g ∘ f) (Ici a) a = g' * f' :=
  (hg.comp_hasDerivWithinAt a hf).derivWithin (uniqueDiffWithinAt_Ici a)

end
