/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 7.43: Every signed measure `φ` admits a Hahn decomposition: there is a measurable set
`Ω⁺` such that `0 ≤[Ω⁺] φ` and `φ ≤[Ω⁺ᶜ] 0`, equivalently every measurable subset of `Ω⁺` has
nonnegative `φ`-mass and every measurable subset of `Ω⁺ᶜ` has nonpositive `φ`-mass. -/
recall MeasureTheory.SignedMeasure.exists_compl_positive_negative
