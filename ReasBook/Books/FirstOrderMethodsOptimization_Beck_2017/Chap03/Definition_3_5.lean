/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E] {f : E → EReal} {x : E}

/- Definition 3.5 is a `bridge/view` item in the chapter convex-analysis API: the owner object is
`subdifferential f x`, and the textbook phrase "f is subdifferentiable at x" is exactly the
nonemptiness proposition on that owner set. The downstream owner set `subdifferential_domain`
introduced in Definition 3.6 is derived from this same proposition, so this file only recalls it. -/
#check (subdifferential f x).Nonempty

end
