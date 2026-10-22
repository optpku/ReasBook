/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Analysis.Calculus.ContDiff.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff

section

variable (f : ℝ → ℝ) (I : Set ℝ)

/- Definition 12.0.6 is a `core/canonical` recall in one-variable smooth calculus. Domain sampling
in mathlib's same-domain owner API gives:
- `ContDiffWithinAt ℝ ∞ f I x` for smoothness at a point within a set;
- `ContDiffOn ℝ ∞ f I` for smoothness on a set;
- `ContDiff ℝ ∞ f` for global smoothness.

The source-facing textbook specialization adds no owner beyond `ContDiffOn`. The primitive data are
only the function `f` and interval `I`; openness of `I` remains ambient source setup rather than
primitive data of a second public wrapper. -/

/- Definition 12.0.6: the textbook notion of a smooth real-valued function on an open interval `I`
is the canonical mathlib predicate `ContDiffOn ℝ ∞ f I`. -/
#check ContDiffOn ℝ ∞ f I

end
