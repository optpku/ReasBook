/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/- Remark 4.5: For a nonnegative simple function `f`, the lower Lebesgue integral of the
underlying `ℝ≥0∞`-valued function agrees with its simple-function integral `I(f) = f.lintegral μ`.
Hence `MeasureTheory.lintegral` extends the map `I` from `E⁺` to nonnegative measurable
functions. -/
recall MeasureTheory.SimpleFunc.lintegral_eq_lintegral
