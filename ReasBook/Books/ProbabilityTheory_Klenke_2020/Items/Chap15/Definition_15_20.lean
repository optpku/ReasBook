/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 15.20: For a family `F : ι → E → ℝ` of real-valued functions on a metric space `E`,
the textbook notion of being uniformly equicontinuous is the canonical mathlib predicate
`UniformEquicontinuous F`. In the metric-space case, this means that for every `ε > 0` there
exists `δ > 0` such that `|F i t - F i s| < ε` for all indices `i` and all `s, t : E` with
`dist s t < δ`. -/
recall UniformEquicontinuous
