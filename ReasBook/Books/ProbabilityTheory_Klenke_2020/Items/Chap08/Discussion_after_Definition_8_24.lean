/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Discussion after Definition 8.24: The pointwise quantities `x ↦ P[A | X = x]` are in general
defined only up to `X`-dependent null sets that may vary with the event `A`, so they do not
automatically assemble into a probability measure in the parameter `x`. The canonical owner
abstraction that resolves this issue under the standard-Borel hypotheses is the regular
conditional distribution `ProbabilityTheory.condDistrib`. -/
recall ProbabilityTheory.condDistrib
