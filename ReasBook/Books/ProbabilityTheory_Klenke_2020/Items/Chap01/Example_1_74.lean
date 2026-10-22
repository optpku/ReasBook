/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped unitInterval

/-- Example 1.74: The restriction of Lebesgue measure on `ℝ` to `[0,1]`, represented by the
canonical volume measure on the unit interval subtype `I`, is a probability measure on the trace
Borel `σ`-algebra of `[0,1]`. -/
theorem unitInterval_volume_isProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure I) := inferInstance
