/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 6.1: If `f, g : Ω → E` are measurable maps into a metric space equipped with its Borel
`σ`-algebra, then the nonnegative distance map `ω ↦ nndist (f ω) (g ω)` is measurable. This is
the canonical mathlib statement `Measurable.nndist`. -/
recall Measurable.nndist
