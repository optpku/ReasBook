/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Remark 24.11: the Poisson point process definition and its existence construction still make
sense for a sigma-finite intensity measure on a measurable space. In the locally compact Polish
setting used in this chapter, this broader sigma-finite framework is already available through the
canonical fact that every locally finite measure on a second-countable space is sigma-finite; the
advantage of the locally compact Polish hypotheses is that the Laplace-transform characterization
is cleaner there. -/
recall MeasureTheory.sigmaFinite_of_locallyFinite
