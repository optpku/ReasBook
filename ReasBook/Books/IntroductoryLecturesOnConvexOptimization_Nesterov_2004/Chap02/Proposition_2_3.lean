/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Analysis.Convex.Strong

-- Declarations for this item will be appended below by the statement pipeline.

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace StrongConvexOn

/- Proposition 2.3 is a bridge/view theorem in the strong-convexity owner API.

Sampled owner-style declarations:
* mathlib `UniformConvexOn`
* mathlib `UniformConvexOn.add`
* mathlib `ConvexOn.uniformConvexOn_zero`
* mathlib `StrongConvexOn`

Best owner abstraction:
* `StrongConvexOn Q μ g`

Primitive data:
* a convex perturbation `ConvexOn ℝ Q f`
* a strongly convex owner hypothesis `StrongConvexOn Q μ g`

Derived API:
* the strong convexity of `f + g`, obtained by viewing `hf` as zero-modulus uniform convexity and
  then applying the canonical modulus-addition theorem

Source/core/bridge triage:
* bridge/view: this proposition derives a new `StrongConvexOn` statement from the owner theorem
  `UniformConvexOn.add`; it does not define a new strong-convexity notion
-/

variable {Q : Set E} {f g : E → ℝ} {μ : ℝ}

/-- Proposition 2.3: on a convex subset `Q` of a real normed space, adding a convex function to a
`μ`-strongly convex function yields another `μ`-strongly convex function with respect to the
ambient norm. -/
theorem add_convexOn
    (hg : StrongConvexOn Q μ g) (hf : ConvexOn ℝ Q f) :
    StrongConvexOn Q μ (f + g) := by
  -- View the convex summand as zero-modulus uniform convexity, then add moduli.
  simpa [StrongConvexOn] using hf.uniformConvexOn_zero.add hg

end StrongConvexOn
